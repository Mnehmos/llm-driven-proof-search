//! Exact two-swap macro-neighborhood search for a parity-zero BS(84,83) state.
//! Each constituent swap is within one index class modulo four, preserving the
//! row, alternating, and z=i margins.  The intermediate state may leave the
//! autocorrelation mod-4 fibre, but every accepted macro-state has all 83
//! residuals divisible by four and is recomputed independently.

use std::{collections::{HashSet,VecDeque}, env, fs, thread};
use std::sync::Arc;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

const L: [usize;4] = [84,84,83,83];
const H: usize = 83;

#[derive(Clone)] struct State { a:[Vec<i8>;4], r:[i32;H], e:i64 }
#[derive(Clone,Copy)] struct Mv { k:usize, p:usize, q:usize }

impl State {
    fn new(a:[Vec<i8>;4])->Self { let mut s=Self{a,r:[0;H],e:0};s.recompute();s }
    fn recompute(&mut self){
        self.r=[0;H];
        for k in 0..4 { for d in 1..L[k] { for i in 0..L[k]-d {
            self.r[d-1]+=self.a[k][i] as i32*self.a[k][i+d] as i32;
        }}}
        self.e=self.r.iter().map(|&x|(x as i64)*(x as i64)).sum();
    }
    fn flip(&mut self,k:usize,p:usize){
        let old=self.a[k][p] as i32;
        for d in 1..L[k] {
            let mut z=0;
            if p+d<L[k]{z+=self.a[k][p+d] as i32}
            if p>=d{z+=self.a[k][p-d] as i32}
            let dr=-2*old*z;let b=self.r[d-1] as i64;let c=b+dr as i64;
            self.e+=c*c-b*b;self.r[d-1]+=dr;
        }
        self.a[k][p]=-self.a[k][p];
    }
    fn swap(&mut self,m:Mv){debug_assert_ne!(self.a[m.k][m.p],self.a[m.k][m.q]);self.flip(m.k,m.p);self.flip(m.k,m.q)}
    fn parity0(&self)->bool{self.r.iter().all(|x|x.rem_euclid(4)==0)}
    fn rows(&self)->[i32;4]{std::array::from_fn(|k|self.a[k].iter().map(|&x|x as i32).sum())}
    fn alts(&self)->[i32;4]{std::array::from_fn(|k|self.a[k].iter().enumerate().map(|(i,&x)|if i&1==0{x as i32}else{-(x as i32)}).sum())}
    fn z4(&self)->[i32;8]{let mut z=[0;8];for k in 0..4{for(i,&x)in self.a[k].iter().enumerate(){match i&3{0=>z[2*k]+=x as i32,1=>z[2*k+1]+=x as i32,2=>z[2*k]-=x as i32,_=>z[2*k+1]-=x as i32}}}z}
}

#[derive(Clone,Copy)]struct Rng(u64);impl Rng{fn next(&mut self)->u64{let mut x=self.0;x^=x<<13;x^=x>>7;x^=x<<17;self.0=x;x}fn usize(&mut self,n:usize)->usize{self.next()as usize%n}}

fn parse(path:&str)->Option<State>{
    let text=fs::read_to_string(path).ok()?;let start=text.find("\"sequences\"")?;let b=text[start..].as_bytes();
    let need:usize=L.iter().sum();let mut v=Vec::with_capacity(need);let mut i=0;
    while i<b.len()&&v.len()<need{if b[i]==b'-'&&i+1<b.len()&&b[i+1]==b'1'{v.push(-1);i+=2}else if b[i]==b'1'{v.push(1);i+=1}else{i+=1}}
    if v.len()!=need{return None}let mut off=0;let a=std::array::from_fn(|k|{let x=v[off..off+L[k]].to_vec();off+=L[k];x});Some(State::new(a))
}

fn moves(s:&State)->Vec<Mv>{
    let mut out=Vec::with_capacity(1800);
    for k in 0..4{for c in 0..4{let mut p=c;while p<L[k]{let mut q=p+4;while q<L[k]{if s.a[k][p]!=s.a[k][q]{out.push(Mv{k,p,q})}q+=4}p+=4}}}
    out
}

fn hash_state(s:&State)->u64{let mut h=0xcbf29ce484222325u64;for x in &s.a{for &v in x{h^=(v as i16+2)as u64;h=h.wrapping_mul(0x100000001b3)}}h}

fn norm<const N:usize>(x:[i32;N])->i32{x.iter().map(|v|v*v).sum()}
fn verify(s:&State,rows:[i32;4],alts:[i32;4],z4:[i32;8])->State{
    let t=State::new(s.a.clone());assert_eq!(t.e,s.e);assert_eq!(t.r,s.r);assert!(t.parity0());assert_eq!(t.rows(),rows);assert_eq!(t.alts(),alts);assert_eq!(t.z4(),z4);assert_eq!(norm(t.rows()),334);assert_eq!(norm(t.alts()),334);assert_eq!(norm(t.z4()),334);t
}

fn json(s:&State,elapsed:f64,rounds:u64,pairs:u64)->String{
    let seq=s.a.iter().map(|x|format!("[{}]",x.iter().map(|v|v.to_string()).collect::<Vec<_>>().join(","))).collect::<Vec<_>>().join(",");
    let r=s.r.iter().map(|x|x.to_string()).collect::<Vec<_>>().join(",");
    format!("{{\"construction\":\"base sequences BS(84,83)\",\"search\":\"agent exact two-swap dual/quartic/parity0 macro tabu\",\"solved\":{},\"independently_recomputed\":true,\"energy\":{},\"l1\":{},\"parity_bad\":0,\"elapsed_s\":{:.6},\"rounds\":{},\"exact_pairs_tested\":{},\"row_sums\":{:?},\"alternating_sums\":{:?},\"z4_components\":{:?},\"residual\":[{}],\"sequences\":[{}]}}\n",s.e==0,s.e,s.r.iter().map(|x|x.abs()).sum::<i32>(),elapsed,rounds,pairs,s.rows(),s.alts(),s.z4(),r,seq)
}

struct ScanResult{best:Option<State>,exact:u64,tested:u64}

fn scan_part(base:Arc<State>,first:Arc<Vec<Mv>>,tabu:Arc<HashSet<u64>>,part:usize,parts:usize,global_e:i64,seed:u64)->ScanResult{
    let mut s=(*base).clone();let mut best:Option<State>=None;let mut exact=0u64;let mut tested=0u64;let mut rng=Rng(seed);
    for ix in (part..first.len()).step_by(parts){
        let m1=first[ix];s.swap(m1);
        for k in 0..4{for c in 0..4{
            let mut p=c;while p<L[k]{let mut q=p+4;while q<L[k]{
                if s.a[k][p]!=s.a[k][q]{
                    let m2=Mv{k,p,q};
                    if m2.k==m1.k&&m2.p==m1.p&&m2.q==m1.q{q+=4;continue}
                    s.swap(m2);tested+=1;
                    if s.parity0(){exact+=1;let allowed=s.e<global_e||!tabu.contains(&hash_state(&s));let take=allowed&&match &best{None=>true,Some(b)=>s.e<b.e||(s.e==b.e&&rng.usize(2)==0)};if take{best=Some(s.clone())}}
                    s.swap(m2);
                }
                q+=4;
            }p+=4;}
        }}
        s.swap(m1);
    }
    ScanResult{best,exact,tested}
}

fn main(){
    let a:Vec<String>=env::args().collect();let secs=a.get(1).and_then(|x|x.parse().ok()).unwrap_or(300u64);let threads=a.get(2).and_then(|x|x.parse().ok()).unwrap_or(4usize);
    let path=a.get(3).map(String::as_str).unwrap_or("agent_bsd_parity0_summary.json");let mut s=parse(path).expect("parity-zero checkpoint required");
    let repair=a.get(4).map(|x|x=="repair").unwrap_or(false);
    if let Some(spec)=a.get(4){if spec!="repair"{let v=spec.split(',').map(|x|x.parse::<usize>().unwrap()).collect::<Vec<_>>();assert_eq!(v.len(),3);s.swap(Mv{k:v[0],p:v[1],q:v[2]});}}
    if !repair{assert!(s.parity0())}let rows=s.rows();let alts=s.alts();let z4=s.z4();assert_eq!(norm(rows),334);assert_eq!(norm(alts),334);assert_eq!(norm(z4),334);if !repair{verify(&s,rows,alts,z4);}
    let start=Instant::now();let end=start+Duration::from_secs(secs);let mut global=s.clone();let mut rounds=0u64;let mut total_exact=0u64;let mut total_tested=0u64;let mut stale=0u64;let mut trail=VecDeque::new();trail.push_back(hash_state(&s));
    eprintln!("agent_bsd_pair seed={} energy={} l1={} rows={:?} alts={:?} z4={:?}",path,s.e,s.r.iter().map(|x|x.abs()).sum::<i32>(),rows,alts,z4);
    let mut repaired=false;
    while Instant::now()<end&&global.e!=0{
        let first=Arc::new(moves(&s));let base=Arc::new(s.clone());let tabu=Arc::new(trail.iter().copied().collect::<HashSet<_>>());let epoch=SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos()as u64;
        let mut hs=vec![];for id in 0..threads{let b=base.clone();let f=first.clone();let t=tabu.clone();let ge=global.e;hs.push(thread::spawn(move||scan_part(b,f,t,id,threads,ge,epoch^(id as u64+1)*0x9e3779b9)))}
        let mut chosen:Option<State>=None;for h in hs{let z=h.join().unwrap();total_exact+=z.exact;total_tested+=z.tested;if let Some(x)=z.best{if chosen.as_ref().map_or(true,|y|x.e<y.e){chosen=Some(x)}}}
        rounds+=1;let next=match chosen{Some(x)=>x,None=>{if repair{break}trail.clear();trail.push_back(hash_state(&s));continue}};
        if repair{global=verify(&next,rows,alts,z4);repaired=true;fs::write("agent_bsd_repair_live.json",json(&global,start.elapsed().as_secs_f64(),rounds,total_exact)).unwrap();break}
        if next.e<global.e{global=verify(&next,rows,alts,z4);fs::write("agent_bsd_e896_pair_live.json",json(&global,start.elapsed().as_secs_f64(),rounds,total_exact)).unwrap();eprintln!("agent_bsd_pair best energy={} l1={} round={} exact={} tested={} elapsed_s={:.3}",global.e,global.r.iter().map(|x|x.abs()).sum::<i32>(),rounds,total_exact,total_tested,start.elapsed().as_secs_f64());stale=0}else{stale+=1}
        s=next;trail.push_back(hash_state(&s));while trail.len()>96{trail.pop_front();}
        // At a two-swap local minimum, take the least uphill exact macro move.
        // Periodically return to the best state so the deterministic basin does
        // not consume the full run.
        if stale>12{s=global.clone();stale=0}
    }
    if repair&&!repaired{println!("agent_bsd_pair repair_found=false rounds={} exact_pairs={} tested_pairs={}",rounds,total_exact,total_tested);return}
    let ans=verify(&global,rows,alts,z4);let out=if ans.e==0{"agent_bsd_e896_pair_candidate.json"}else if repair{"agent_bsd_repair_summary.json"}else{"agent_bsd_e896_pair_summary.json"};fs::write(out,json(&ans,start.elapsed().as_secs_f64(),rounds,total_exact)).unwrap();
    println!("agent_bsd_pair result solved={} energy={} l1={} rounds={} exact_pairs={} tested_pairs={} output={}",ans.e==0,ans.e,ans.r.iter().map(|x|x.abs()).sum::<i32>(),rounds,total_exact,total_tested,out);
}
