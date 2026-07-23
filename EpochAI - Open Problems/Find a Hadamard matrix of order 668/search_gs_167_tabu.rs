//! Exhaustive-neighborhood tabu search for a cyclic GS difference family on Z_167.
//! Unlike the annealer, each iteration evaluates every row-sum-preserving swap.
use std::{env,fs,thread};
use std::sync::{Arc,Mutex};
use std::sync::atomic::{AtomicBool,AtomicI64,Ordering};
use std::time::{Duration,Instant,SystemTime,UNIX_EPOCH};
const N:usize=167; const H:usize=83;

#[derive(Clone)] struct State { a:[[i8;N];4], r:[i32;H], e:i64 }
impl State {
 fn new(a:[[i8;N];4])->Self { let mut s=Self{a,r:[0;H],e:0}; s.recompute(); s }
 fn recompute(&mut self) { self.r=[0;H]; for d in 1..=H { for k in 0..4 { for i in 0..N { self.r[d-1]+=self.a[k][i] as i32*self.a[k][(i+d)%N] as i32; }}} self.e=self.r.iter().map(|&x|(x as i64)*(x as i64)).sum(); }
 fn rows(&self)->[i32;4] { let mut z=[0;4]; for k in 0..4 { z[k]=self.a[k].iter().map(|&x|x as i32).sum(); } z }
 fn l1(&self)->i64 { self.r.iter().map(|x|x.abs() as i64).sum() }
 fn swap_delta(&self,k:usize,p:usize,q:usize,buf:&mut[i32;H])->i64 {
  let x=self.a[k][p] as i32; let y=self.a[k][q] as i32; debug_assert_eq!(x,-y);
  let gap0=(q+N-p)%N; let gap=gap0.min(N-gap0);
  let mut de=0i64;
  for d in 1..=H {
   let mut dr=-2*x*(self.a[k][(p+d)%N] as i32+self.a[k][(p+N-d)%N] as i32)
              -2*y*(self.a[k][(q+d)%N] as i32+self.a[k][(q+N-d)%N] as i32);
   if d==gap { dr+=4*x*y; }
   buf[d-1]=dr; let old=self.r[d-1] as i64; let new=old+dr as i64; de+=new*new-old*old;
  }
  de
 }
 fn swap_delta_l1(&self,k:usize,p:usize,q:usize,buf:&mut[i32;H])->i64 {
  let x=self.a[k][p] as i32; let y=self.a[k][q] as i32; debug_assert_eq!(x,-y);
  let gap0=(q+N-p)%N; let gap=gap0.min(N-gap0); let mut de=0i64;
  for d in 1..=H {
   let mut dr=-2*x*(self.a[k][(p+d)%N] as i32+self.a[k][(p+N-d)%N] as i32)
              -2*y*(self.a[k][(q+d)%N] as i32+self.a[k][(q+N-d)%N] as i32);
   if d==gap { dr+=4*x*y; }
   buf[d-1]=dr; de+=(self.r[d-1]+dr).abs() as i64-self.r[d-1].abs() as i64;
  }
  de
 }
 fn apply_swap(&mut self,k:usize,p:usize,q:usize,buf:&mut[i32;H]) {
  let de=self.swap_delta(k,p,q,buf); self.a[k][p]=-self.a[k][p]; self.a[k][q]=-self.a[k][q];
  for d in 0..H { self.r[d]+=buf[d]; } self.e+=de;
 }
}
#[derive(Clone,Copy)] struct Rng(u64); impl Rng { fn next(&mut self)->u64 { let mut x=self.0; x^=x<<13; x^=x>>7; x^=x<<17; self.0=x; x } fn usize(&mut self,n:usize)->usize { self.next() as usize%n } }
fn parse(path:&str)->Option<State> { let text=fs::read_to_string(path).ok()?; let start=text.find("\"sequences\"")?; let b=text[start..].as_bytes(); let mut v=Vec::with_capacity(668); let(mut i,mut n)=(0,0); while i<b.len()&&n<668 { if b[i]==b'-'&&i+1<b.len()&&b[i+1]==b'1' {v.push(-1);n+=1;i+=2} else if b[i]==b'1' {v.push(1);n+=1;i+=1} else {i+=1} } if n!=668{return None} let mut a=[[1i8;N];4]; for k in 0..4 {a[k].copy_from_slice(&v[k*N..(k+1)*N]);} Some(State::new(a)) }
fn json(s:&State,solved:bool,elapsed:f64,iters:u64)->String { let seq=s.a.iter().map(|x|format!("[{}]",x.iter().map(|v|v.to_string()).collect::<Vec<_>>().join(","))).collect::<Vec<_>>().join(","); let r=s.r.iter().map(|x|x.to_string()).collect::<Vec<_>>().join(","); format!("{{\"construction\":\"cyclic Goethals-Seidel order 167\",\"search\":\"exhaustive-neighborhood tabu\",\"solved\":{},\"energy\":{},\"elapsed_s\":{},\"iterations\":{},\"row_sums\":{:?},\"residual\":[{}],\"sequences\":[{}]}}\n",solved,s.e,elapsed,iters,s.rows(),r,seq) }
fn publish(s:&State,id:usize,start:Instant,atom:&AtomicI64,best:&Mutex<State>) { let mut seen=atom.load(Ordering::Relaxed); while s.e<seen { match atom.compare_exchange_weak(seen,s.e,Ordering::SeqCst,Ordering::Relaxed) { Ok(_)=>{*best.lock().unwrap()=s.clone(); let rr=s.rows(); let _=fs::write(format!("gs_167_tabu_{}_{}_{}_{}_live.json",rr[0],rr[1],rr[2],rr[3]),json(s,false,start.elapsed().as_secs_f64(),0)); eprintln!("best energy={} worker={} elapsed_s={:.3}",s.e,id,start.elapsed().as_secs_f64()); return}, Err(x)=>seen=x } } }
fn worker(id:usize,end:Instant,start:Instant,atom:Arc<AtomicI64>,best:Arc<Mutex<State>>,stop:Arc<AtomicBool>)->u64 {
 let epoch=SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos() as u64; let mut rng=Rng(epoch^(id as u64+11).wrapping_mul(0x9e3779b97f4a7c15));
 let mut s=best.lock().unwrap().clone(); let use_l1=id%2==1; let mut tabu=[[0u64;N];4]; let mut iter=0u64; let mut since_best=0u64; let mut dr=[0i32;H];
 while Instant::now()<end&&!stop.load(Ordering::Relaxed) {
  let global=atom.load(Ordering::Relaxed); let mut pick=(i64::MAX,0usize,0usize,0usize); let mut ties=0usize;
  for k in 0..4 { for p in 0..N { if s.a[k][p]!=1{continue} for q in 0..N { if s.a[k][q]!=-1{continue} let de=if use_l1{s.swap_delta_l1(k,p,q,&mut dr)}else{s.swap_delta(k,p,q,&mut dr)}; let ede=s.swap_delta(k,p,q,&mut dr); let aspir=s.e+ede<global; if !aspir&&(tabu[k][p]>iter||tabu[k][q]>iter){continue} if de<pick.0 {pick=(de,k,p,q);ties=1} else if de==pick.0 {ties+=1;if rng.usize(ties)==0{pick=(de,k,p,q)}} }}}
  if pick.0==i64::MAX { tabu=[[0u64;N];4]; continue; }
  s.apply_swap(pick.1,pick.2,pick.3,&mut dr); iter+=1; since_best+=1;
  let tenure=9+rng.usize(19) as u64+(since_best/2000).min(35); tabu[pick.1][pick.2]=iter+tenure; tabu[pick.1][pick.3]=iter+tenure;
  if s.e<global { publish(&s,id,start,&atom,&best); since_best=0; if s.e==0 {let mut chk=s.clone();chk.recompute();if chk.e==0{*best.lock().unwrap()=chk;stop.store(true,Ordering::SeqCst);break}} }
  if since_best>6000 { s=best.lock().unwrap().clone(); for _ in 0..(8+rng.usize(25)){let k=rng.usize(4);let mut p=rng.usize(N);while s.a[k][p]!=1{p=rng.usize(N)}let mut q=rng.usize(N);while s.a[k][q]!=-1{q=rng.usize(N)}s.apply_swap(k,p,q,&mut dr)} tabu=[[0u64;N];4]; since_best=0; }
 }
 iter
}
fn main(){let z:Vec<String>=env::args().collect();let secs=z.get(1).and_then(|x|x.parse().ok()).unwrap_or(900);let threads=z.get(2).and_then(|x|x.parse().ok()).unwrap_or(4);let initial=z.get(3).and_then(|p|parse(p)).expect("checkpoint JSON required");eprintln!("seed energy={} rows={:?}",initial.e,initial.rows());let start=Instant::now();let end=start+Duration::from_secs(secs);let atom=Arc::new(AtomicI64::new(initial.e));let best=Arc::new(Mutex::new(initial));let stop=Arc::new(AtomicBool::new(false));let mut hs=vec![];for id in 0..threads{let(a,b,c)=(atom.clone(),best.clone(),stop.clone());hs.push(thread::spawn(move||worker(id,end,start,a,b,c)))}let iters=hs.into_iter().map(|h|h.join().unwrap()).sum();let mut ans=best.lock().unwrap().clone();ans.recompute();let solved=ans.e==0;let rr=ans.rows();let out=if solved{"gs_167_candidate.json".to_string()}else{format!("gs_167_tabu_{}_{}_{}_{}_summary.json",rr[0],rr[1],rr[2],rr[3])};fs::write(&out,json(&ans,solved,start.elapsed().as_secs_f64(),iters)).unwrap();println!("result solved={} energy={} iterations={} output={}",solved,ans.e,iters,out)}
