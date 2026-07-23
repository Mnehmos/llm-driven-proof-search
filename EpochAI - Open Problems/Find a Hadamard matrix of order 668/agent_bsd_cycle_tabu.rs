//! Randomized alternating-cycle tabu search for BS(84,83).
//!
//! Positions are edges between one of 16 fixed-margin cells and one of the 84
//! autocorrelation-syndrome classes.  A legal sign swap is an edge between two
//! syndrome classes inside a margin cell.  Hence every cycle of such swaps
//! preserves row sums, alternating sums, z=i components, and all residual
//! parities.  This searches cycles of five through twelve swaps, beyond the
//! exhaustively checked 1--4-swap basin.

use std::{collections::{HashMap,HashSet,VecDeque},env,fs,thread};
use std::sync::Arc;
use std::time::{Duration,Instant,SystemTime,UNIX_EPOCH};
const L:[usize;4]=[84,84,83,83];const H:usize=83;const V:usize=84;

#[derive(Clone)]struct State{a:[Vec<i8>;4],r:[i32;H],e:i64}
#[derive(Clone,Copy)]struct Mv{k:usize,p:usize,q:usize,u:usize,v:usize,dr:[i8;H]}
#[derive(Clone)]struct Choice{edges:Vec<u16>,e:i64,h:u64}
#[derive(Clone,Copy)]struct Rng(u64);impl Rng{fn next(&mut self)->u64{let mut x=self.0;x^=x<<13;x^=x>>7;x^=x<<17;self.0=x;x}fn usize(&mut self,n:usize)->usize{self.next()as usize%n}}

impl State{
 fn new(a:[Vec<i8>;4])->Self{let mut s=Self{a,r:[0;H],e:0};s.recompute();s}
 fn recompute(&mut self){self.r=[0;H];for k in 0..4{for d in 1..L[k]{for i in 0..L[k]-d{self.r[d-1]+=self.a[k][i]as i32*self.a[k][i+d]as i32}}}self.e=self.r.iter().map(|&x|(x as i64)*(x as i64)).sum()}
 fn flip(&mut self,k:usize,p:usize){let old=self.a[k][p]as i32;for d in 1..L[k]{let mut z=0;if p+d<L[k]{z+=self.a[k][p+d]as i32}if p>=d{z+=self.a[k][p-d]as i32}let dr=-2*old*z;let b=self.r[d-1]as i64;let c=b+dr as i64;self.e+=c*c-b*b;self.r[d-1]+=dr}self.a[k][p]=-self.a[k][p]}
 fn swap(&mut self,m:Mv){debug_assert_ne!(self.a[m.k][m.p],self.a[m.k][m.q]);self.flip(m.k,m.p);self.flip(m.k,m.q)}
 fn parity0(&self)->bool{self.r.iter().all(|x|x.rem_euclid(4)==0)}
 fn rows(&self)->[i32;4]{std::array::from_fn(|k|self.a[k].iter().map(|&x|x as i32).sum())}
 fn alts(&self)->[i32;4]{std::array::from_fn(|k|self.a[k].iter().enumerate().map(|(i,&x)|if i&1==0{x as i32}else{-(x as i32)}).sum())}
 fn z4(&self)->[i32;8]{let mut z=[0;8];for k in 0..4{for(i,&x)in self.a[k].iter().enumerate(){match i&3{0=>z[2*k]+=x as i32,1=>z[2*k+1]+=x as i32,2=>z[2*k]-=x as i32,_=>z[2*k+1]-=x as i32}}}z}
}

fn parse(path:&str)->Option<State>{let text=fs::read_to_string(path).ok()?;let st=text.find("\"sequences\"")?;let b=text[st..].as_bytes();let need:usize=L.iter().sum();let mut v=vec![];let mut i=0;while i<b.len()&&v.len()<need{if b[i]==b'-'&&i+1<b.len()&&b[i+1]==b'1'{v.push(-1);i+=2}else if b[i]==b'1'{v.push(1);i+=1}else{i+=1}}if v.len()!=need{return None}let mut o=0;let a=std::array::from_fn(|k|{let x=v[o..o+L[k]].to_vec();o+=L[k];x});Some(State::new(a))}
fn sig(n:usize,p:usize)->u128{let mut s=0;for d in 1..84{if(p<d)^(p>=n-d){s|=1u128<<(d-1)}}s}
fn gp(k:usize,p:usize)->usize{[0,84,168,251][k]+p}
fn token(k:usize,p:usize)->u64{let mut x=((gp(k,p)+1)as u64).wrapping_mul(0x9e3779b97f4a7c15);x=(x^(x>>30)).wrapping_mul(0xbf58476d1ce4e5b9);x=(x^(x>>27)).wrapping_mul(0x94d049bb133111eb);x^(x>>31)}
fn state_hash(s:&State)->u64{let mut h=0;for k in 0..4{for p in 0..L[k]{if s.a[k][p]<0{h^=token(k,p)}}}h}

fn graph(s:&State)->(Vec<Mv>,[Vec<u16>;V]){
 let mut ids=HashMap::new();let mut cls:[Vec<usize>;4]=std::array::from_fn(|k|vec![0;L[k]]);for k in 0..4{for p in 0..L[k]{let q=sig(L[k],p);cls[k][p]=if q==0{83}else{let n=ids.len();*ids.entry(q).or_insert(n)}}}assert_eq!(ids.len(),83);
 let mut m=vec![];for k in 0..4{for c in 0..4{let mut p=c;while p<L[k]{let mut q=p+4;while q<L[k]{if s.a[k][p]!=s.a[k][q]{let mut dr=[0i16;H];for &x in &[p,q]{let old=s.a[k][x]as i16;for d in 1..L[k]{let mut z=0;if x+d<L[k]{z+=s.a[k][x+d]as i16}if x>=d{z+=s.a[k][x-d]as i16}dr[d-1]+=-2*old*z}}dr[q-p-1]+=4*(s.a[k][p]as i16)*(s.a[k][q]as i16);m.push(Mv{k,p,q,u:cls[k][p],v:cls[k][q],dr:std::array::from_fn(|d|dr[d]as i8)})}q+=4}p+=4}}}
 let mut adj:[Vec<u16>;V]=std::array::from_fn(|_|vec![]);for(i,e)in m.iter().enumerate(){adj[e.u].push(i as u16);if e.v!=e.u{adj[e.v].push(i as u16)}}(m,adj)
}
fn other(e:Mv,x:usize)->usize{if e.u==x{e.v}else{debug_assert_eq!(e.v,x);e.u}}
fn free(e:Mv,used:&[bool;334])->bool{!used[gp(e.k,e.p)]&&!used[gp(e.k,e.q)]}
fn mark(e:Mv,used:&mut[bool;334]){used[gp(e.k,e.p)]=true;used[gp(e.k,e.q)]=true}

fn cycle(rng:&mut Rng,m:&[Mv],adj:&[Vec<u16>;V])->Option<Vec<u16>>{
 let len=5+rng.usize(8);for _ in 0..10{let e0i=rng.usize(m.len());let e0=m[e0i];if e0.u==e0.v{continue}let(start,mut cur)=if rng.usize(2)==0{(e0.u,e0.v)}else{(e0.v,e0.u)};let mut usedp=[false;334];let mut usedv=[false;V];usedv[start]=true;usedv[cur]=true;mark(e0,&mut usedp);let mut out=vec![e0i as u16];let mut ok=true;
  for _ in 1..len-1{let mut pick=None;for _ in 0..48{let ix=adj[cur][rng.usize(adj[cur].len())];let e=m[ix as usize];let w=other(e,cur);if w!=start&&!usedv[w]&&free(e,&usedp){pick=Some((ix,w));break}}if let Some((ix,w))=pick{mark(m[ix as usize],&mut usedp);usedv[w]=true;out.push(ix);cur=w}else{ok=false;break}}
  if !ok{continue}let mut close=None;let mut seen=0;for &ix in &adj[cur]{let e=m[ix as usize];if other(e,cur)==start&&free(e,&usedp){seen+=1;if rng.usize(seen)==0{close=Some(ix)}}}if let Some(ix)=close{out.push(ix);return Some(out)}
 }None
}

fn evaluate(s:&State,m:&[Mv],ed:&[u16])->i64{let mut dr=[0i32;H];for &ix in ed{let e=m[ix as usize];for d in 0..H{dr[d]+=e.dr[d]as i32}}for x in 0..ed.len(){let a=m[ed[x]as usize];for y in x+1..ed.len(){let b=m[ed[y]as usize];if a.k==b.k{for p in [a.p,a.q]{for q in [b.p,b.q]{dr[p.abs_diff(q)-1]+=4*(s.a[a.k][p]as i32)*(s.a[b.k][q]as i32)}}}}}s.r.iter().zip(dr).map(|(&x,d)|{let q=(x+d)as i64;q*q}).sum()}
fn candidate_hash(base:u64,m:&[Mv],ed:&[u16])->u64{let mut h=base;for &ix in ed{let e=m[ix as usize];h^=token(e.k,e.p)^token(e.k,e.q)}h}
struct Part{best:Option<Choice>,valid:u64}
fn sample(s:Arc<State>,m:Arc<Vec<Mv>>,adj:Arc<[Vec<u16>;V]>,tabu:Arc<HashSet<u64>>,base:u64,global:i64,n:u64,seed:u64)->Part{let mut rng=Rng(seed|1);let mut best=None;let mut valid=0;for _ in 0..n{if let Some(ed)=cycle(&mut rng,&m,&adj){valid+=1;let e=evaluate(&s,&m,&ed);let h=candidate_hash(base,&m,&ed);if(e<global||!tabu.contains(&h))&&best.as_ref().map_or(true,|q:&Choice|e<q.e){best=Some(Choice{edges:ed,e,h})}}}Part{best,valid}}

fn verify(s:&State,rows:[i32;4],alts:[i32;4],z4:[i32;8])->State{let t=State::new(s.a.clone());assert_eq!(t.e,s.e);assert_eq!(t.r,s.r);assert!(t.parity0());assert_eq!(t.rows(),rows);assert_eq!(t.alts(),alts);assert_eq!(t.z4(),z4);t}
fn json(s:&State,elapsed:f64,rounds:u64,valid:u64)->String{let seq=s.a.iter().map(|x|format!("[{}]",x.iter().map(|v|v.to_string()).collect::<Vec<_>>().join(","))).collect::<Vec<_>>().join(",");let r=s.r.iter().map(|x|x.to_string()).collect::<Vec<_>>().join(",");format!("{{\"construction\":\"base sequences BS(84,83)\",\"search\":\"agent exact parity alternating-cycle tabu\",\"solved\":{},\"independently_recomputed\":true,\"energy\":{},\"l1\":{},\"parity_bad\":0,\"elapsed_s\":{},\"rounds\":{},\"valid_cycles_tested\":{},\"row_sums\":{:?},\"alternating_sums\":{:?},\"z4_components\":{:?},\"residual\":[{}],\"sequences\":[{}]}}\n",s.e==0,s.e,s.r.iter().map(|x|x.abs()).sum::<i32>(),elapsed,rounds,valid,s.rows(),s.alts(),s.z4(),r,seq)}

fn main(){let a:Vec<String>=env::args().collect();let secs=a.get(1).and_then(|x|x.parse().ok()).unwrap_or(300);let threads=a.get(2).and_then(|x|x.parse().ok()).unwrap_or(4);let samples=a.get(3).and_then(|x|x.parse().ok()).unwrap_or(400000u64);let path=a.get(4).map(String::as_str).expect("checkpoint");let stem=a.get(5).map(String::as_str).unwrap_or("agent_bsd_e896_cycle");let mut s=parse(path).unwrap();assert!(s.parity0());let(rows,alts,z4)=(s.rows(),s.alts(),s.z4());let mut global=s.clone();let start=Instant::now();let end=start+Duration::from_secs(secs);let mut trail=VecDeque::from([state_hash(&s)]);let mut rounds=0;let mut valid=0;let mut stale=0;eprintln!("agent_bsd_cycle seed={} energy={} l1={} samples_per_round={} rows={:?} alts={:?} z4={:?}",path,s.e,s.r.iter().map(|x|x.abs()).sum::<i32>(),samples,rows,alts,z4);
 while Instant::now()<end&&global.e!=0{let(m0,a0)=graph(&s);let m=Arc::new(m0);let adj=Arc::new(a0);let base=state_hash(&s);let tabu=Arc::new(trail.iter().copied().collect::<HashSet<_>>());let state=Arc::new(s.clone());let epoch=SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos()as u64;let mut hs=vec![];for id in 0..threads{let(q,w,x,t)=(state.clone(),m.clone(),adj.clone(),tabu.clone());let ge=global.e;let n=(samples+id as u64)/threads as u64;hs.push(thread::spawn(move||sample(q,w,x,t,base,ge,n,epoch^(id as u64+1).wrapping_mul(0x9e3779b97f4a7c15))))}let mut pick=None;for h in hs{let q=h.join().unwrap();valid+=q.valid;if let Some(x)=q.best{if pick.as_ref().map_or(true,|y:&Choice|x.e<y.e){pick=Some(x)}}}rounds+=1;let q=match pick{Some(x)=>x,None=>{trail.clear();trail.push_back(base);continue}};for &ix in &q.edges{s.swap(m[ix as usize])}s=verify(&s,rows,alts,z4);assert_eq!(s.e,q.e);assert_eq!(state_hash(&s),q.h);trail.push_back(q.h);while trail.len()>512{trail.pop_front();}eprintln!("agent_bsd_cycle step energy={} l1={} len={} valid={} round={} elapsed_s={:.3}",s.e,s.r.iter().map(|x|x.abs()).sum::<i32>(),q.edges.len(),valid,rounds,start.elapsed().as_secs_f64());if s.e<global.e{global=s.clone();fs::write(format!("{}_live.json",stem),json(&global,start.elapsed().as_secs_f64(),rounds,valid)).unwrap();eprintln!("agent_bsd_cycle best energy={}",global.e);stale=0}else{stale+=1}if stale>96{s=global.clone();trail.push_back(state_hash(&s));stale=0}}
 let ans=verify(&global,rows,alts,z4);let out=format!("{}_{}.json",stem,if ans.e==0{"candidate"}else{"summary"});fs::write(&out,json(&ans,start.elapsed().as_secs_f64(),rounds,valid)).unwrap();println!("agent_bsd_cycle result solved={} energy={} l1={} rounds={} valid_cycles={} output={}",ans.e==0,ans.e,ans.r.iter().map(|x|x.abs()).sum::<i32>(),rounds,valid,out)}
