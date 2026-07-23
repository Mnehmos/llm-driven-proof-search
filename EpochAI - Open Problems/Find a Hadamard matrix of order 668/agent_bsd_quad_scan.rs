//! Exact four-swap syndrome meet-in-the-middle scan in a fixed BS(84,83)
//! row/alternating/quartic fibre.  Every accepted macro preserves all 83
//! autocorrelation parities.  Pair deltas are cached as compact i8 vectors so
//! the complete four-swap shell can be evaluated without mutating the state.

use std::{collections::{HashMap,HashSet,VecDeque},env,fs,thread};
use std::sync::Arc;
use std::time::{Duration,Instant};

const L:[usize;4]=[84,84,83,83];
const H:usize=83;

#[derive(Clone)] struct State{a:[Vec<i8>;4],r:[i32;H],e:i64}
#[derive(Clone,Copy)] struct Mv{k:usize,p:usize,q:usize,sig:u128,dr:[i8;H]}
#[derive(Clone)] struct Pair{i:u16,j:u16,dr:[i8;H]}
#[derive(Clone,Copy)] struct Quad{i:u16,j:u16,u:u16,v:u16,e:i64,h:u64}

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
fn position_sig(n:usize,p:usize)->u128{let mut s=0;for d in 1..84{if(p<d)^(p>=n-d){s|=1u128<<(d-1)}}s}
fn disjoint(a:Mv,b:Mv)->bool{a.k!=b.k||(a.p!=b.p&&a.p!=b.q&&a.q!=b.p&&a.q!=b.q)}

fn moves(s:&State)->Vec<Mv>{
 let ps:[Vec<u128>;4]=std::array::from_fn(|k|(0..L[k]).map(|p|position_sig(L[k],p)).collect());let mut out=vec![];
 for k in 0..4{for c in 0..4{let mut p=c;while p<L[k]{let mut q=p+4;while q<L[k]{if s.a[k][p]!=s.a[k][q]{
  let mut dr=[0i16;H];for &x in &[p,q]{let old=s.a[k][x]as i16;for d in 1..L[k]{let mut z=0i16;if x+d<L[k]{z+=s.a[k][x+d]as i16}if x>=d{z+=s.a[k][x-d]as i16}dr[d-1]+=-2*old*z}}
  dr[q-p-1]+=4*(s.a[k][p]as i16)*(s.a[k][q]as i16);
  let compact=std::array::from_fn(|d|{assert!((-32..=32).contains(&dr[d]));dr[d]as i8});out.push(Mv{k,p,q,sig:ps[k][p]^ps[k][q],dr:compact});
 }q+=4}p+=4}}}out
}

fn build_pairs(s:&State,m:&[Mv])->HashMap<u128,Vec<Pair>>{
 let mut map:HashMap<u128,Vec<Pair>>=HashMap::with_capacity(190000);
 for i in 0..m.len(){for j in i+1..m.len(){if !disjoint(m[i],m[j]){continue}let mut dr:[i16;H]=std::array::from_fn(|d|m[i].dr[d]as i16+m[j].dr[d]as i16);
  if m[i].k==m[j].k{for &p in &[m[i].p,m[i].q]{for &q in &[m[j].p,m[j].q]{dr[p.abs_diff(q)-1]+=4*(s.a[m[i].k][p]as i16)*(s.a[m[j].k][q]as i16)}}}
  let compact=std::array::from_fn(|d|{assert!((-64..=64).contains(&dr[d]));dr[d]as i8});map.entry(m[i].sig^m[j].sig).or_default().push(Pair{i:i as u16,j:j as u16,dr:compact});
 }}map
}

fn pairs_disjoint(a:&Pair,b:&Pair,m:&[Mv])->bool{let x=[m[a.i as usize],m[a.j as usize]];let y=[m[b.i as usize],m[b.j as usize]];x.iter().all(|&u|y.iter().all(|&v|disjoint(u,v)))}

fn token(k:usize,p:usize)->u64{let mut x=((k*84+p+1)as u64).wrapping_mul(0x9e3779b97f4a7c15);x=(x^(x>>30)).wrapping_mul(0xbf58476d1ce4e5b9);x=(x^(x>>27)).wrapping_mul(0x94d049bb133111eb);x^(x>>31)}
fn state_hash(s:&State)->u64{let mut h=0;for k in 0..4{for p in 0..L[k]{if s.a[k][p]<0{h^=token(k,p)}}}h}
fn candidate_hash(base:u64,a:&Pair,b:&Pair,m:&[Mv])->u64{let mut h=base;for ix in [a.i,a.j,b.i,b.j]{let q=m[ix as usize];h^=token(q.k,q.p)^token(q.k,q.q)}h}

fn cross_corrections(a:&Pair,b:&Pair,m:&[Mv],s:&State,ds:&mut[usize;16],cs:&mut[i32;16])->usize{
 let aa=[m[a.i as usize],m[a.j as usize]];let bb=[m[b.i as usize],m[b.j as usize]];let mut n=0;
 for x in aa{for y in bb{if x.k!=y.k{continue}for p in [x.p,x.q]{for q in [y.p,y.q]{let d=p.abs_diff(q)-1;let c=4*(s.a[x.k][p]as i32)*(s.a[y.k][q]as i32);let mut at=None;for z in 0..n{if ds[z]==d{at=Some(z);break}}if let Some(z)=at{cs[z]+=c}else{ds[n]=d;cs[n]=c;n+=1}}}}}n
}

struct Part{best:Option<Quad>,tested:u64}
fn scan(s:Arc<State>,m:Arc<Vec<Mv>>,map:Arc<HashMap<u128,Vec<Pair>>>,keys:Arc<Vec<u128>>,tabu:Arc<HashSet<u64>>,base_hash:u64,global:i64,part:usize,parts:usize)->Part{
 let mut best=None;let mut tested=0;for z in(part..keys.len()).step_by(parts){let g=&map[&keys[z]];for i in 0..g.len(){for j in i+1..g.len(){let(a,b)=(&g[i],&g[j]);if !pairs_disjoint(a,b,&m){continue}tested+=1;
  let mut e=0i64;for d in 0..H{let x=s.r[d]+a.dr[d]as i32+b.dr[d]as i32;e+=(x as i64)*(x as i64)}
  let mut ds=[0usize;16];let mut cs=[0i32;16];let nc=cross_corrections(a,b,&m,&s,&mut ds,&mut cs);for t in 0..nc{let d=ds[t];let x=s.r[d]+a.dr[d]as i32+b.dr[d]as i32;let y=x+cs[t];e+=(y as i64)*(y as i64)-(x as i64)*(x as i64)}
  let h=candidate_hash(base_hash,a,b,&m);if (e<global||!tabu.contains(&h))&&best.map_or(true,|q:Quad|e<q.e){best=Some(Quad{i:a.i,j:a.j,u:b.i,v:b.j,e,h})}
 }}}Part{best,tested}
}

fn verify(s:&State,rows:[i32;4],alts:[i32;4],z4:[i32;8])->State{let t=State::new(s.a.clone());assert_eq!(t.e,s.e);assert_eq!(t.r,s.r);assert!(t.parity0());assert_eq!(t.rows(),rows);assert_eq!(t.alts(),alts);assert_eq!(t.z4(),z4);t}
fn json(s:&State,elapsed:f64,rounds:u64,tested:u64)->String{let seq=s.a.iter().map(|x|format!("[{}]",x.iter().map(|v|v.to_string()).collect::<Vec<_>>().join(","))).collect::<Vec<_>>().join(",");let r=s.r.iter().map(|x|x.to_string()).collect::<Vec<_>>().join(",");format!("{{\"construction\":\"base sequences BS(84,83)\",\"search\":\"agent exact 4-swap syndrome MITM\",\"solved\":{},\"independently_recomputed\":true,\"energy\":{},\"l1\":{},\"parity_bad\":0,\"elapsed_s\":{},\"rounds\":{},\"exact_quadruples_tested\":{},\"row_sums\":{:?},\"alternating_sums\":{:?},\"z4_components\":{:?},\"residual\":[{}],\"sequences\":[{}]}}\n",s.e==0,s.e,s.r.iter().map(|x|x.abs()).sum::<i32>(),elapsed,rounds,tested,s.rows(),s.alts(),s.z4(),r,seq)}

fn main(){let a:Vec<String>=env::args().collect();let secs=a.get(1).and_then(|x|x.parse().ok()).unwrap_or(300);let threads=a.get(2).and_then(|x|x.parse().ok()).unwrap_or(4);let path=a.get(3).map(String::as_str).expect("checkpoint");let mut s=parse(path).unwrap();assert!(s.parity0());let(rows,alts,z4)=(s.rows(),s.alts(),s.z4());let mut global=s.clone();let start=Instant::now();let end=start+Duration::from_secs(secs);let mut rounds=0;let mut tested=0;let mut trail=VecDeque::from([state_hash(&s)]);let mut stale=0;eprintln!("agent_bsd_quad seed={} energy={} l1={} rows={:?} alts={:?} z4={:?}",path,s.e,s.r.iter().map(|x|x.abs()).sum::<i32>(),rows,alts,z4);
 while Instant::now()<end&&global.e!=0{let m=Arc::new(moves(&s));let map=Arc::new(build_pairs(&s,&m));let keys=Arc::new(map.keys().copied().collect::<Vec<_>>());let pair_count:usize=map.values().map(Vec::len).sum();eprintln!("agent_bsd_quad shell round={} moves={} groups={} pairs={}",rounds+1,m.len(),map.len(),pair_count);let base_hash=state_hash(&s);let tabu=Arc::new(trail.iter().copied().collect::<HashSet<_>>());let base=Arc::new(s.clone());let mut hs=vec![];for id in 0..threads{let(q,w,x,y,t)=(base.clone(),m.clone(),map.clone(),keys.clone(),tabu.clone());let ge=global.e;hs.push(thread::spawn(move||scan(q,w,x,y,t,base_hash,ge,id,threads)))}let mut pick=None;for h in hs{let p=h.join().unwrap();tested+=p.tested;if let Some(q)=p.best{if pick.map_or(true,|x:Quad|q.e<x.e){pick=Some(q)}}}rounds+=1;let q=match pick{Some(x)=>x,None=>{trail.clear();trail.push_back(base_hash);continue}};for ix in [q.i,q.j,q.u,q.v]{s.swap(m[ix as usize])}s=verify(&s,rows,alts,z4);assert_eq!(s.e,q.e);assert_eq!(state_hash(&s),q.h);eprintln!("agent_bsd_quad shell_min energy={} l1={} tested={} elapsed_s={:.3}",s.e,s.r.iter().map(|x|x.abs()).sum::<i32>(),tested,start.elapsed().as_secs_f64());trail.push_back(q.h);while trail.len()>192{trail.pop_front();}if s.e<global.e{global=s.clone();fs::write("agent_bsd_e896_quad_tabu_live.json",json(&global,start.elapsed().as_secs_f64(),rounds,tested)).unwrap();eprintln!("agent_bsd_quad best energy={}",global.e);stale=0}else{stale+=1}if stale>64{s=global.clone();trail.push_back(state_hash(&s));stale=0}}
 let ans=verify(&global,rows,alts,z4);let out=if ans.e==0{"agent_bsd_e896_quad_tabu_candidate.json"}else{"agent_bsd_e896_quad_tabu_summary.json"};fs::write(out,json(&ans,start.elapsed().as_secs_f64(),rounds,tested)).unwrap();println!("agent_bsd_quad result solved={} energy={} l1={} rounds={} exact_quadruples={} output={}",ans.e==0,ans.e,ans.r.iter().map(|x|x.abs()).sum::<i32>(),rounds,tested,out)}
