//! Native stochastic search in the 167-bit special Golay family used by the
//! published 64-modular approximation to H(668).  Zero energy is a true Golay
//! quadruple and therefore a true Hadamard matrix, not merely a modular one.

use std::env;
use std::fs;
use std::sync::atomic::{AtomicBool, AtomicI64, Ordering};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

#[derive(Clone)]
struct State { s: [i8; 167], r: [i32; 83], energy: i64 }

fn q(i: usize) -> i8 { if i < 83 || (85..166).contains(&i) { 1 } else { -1 } }
fn f(i: usize) -> i8 { if i < 84 { 1 } else { -1 } }
fn edge(i: usize, j: usize) -> bool { f(i) == f(j) && q(i) == q(j) }

impl State {
    fn new(s: [i8; 167]) -> Self { let mut x = Self { s, r: [0; 83], energy: 0 }; x.recompute(); x }
    fn recompute(&mut self) {
        self.r = [0; 83];
        for d in 1..84 { for i in 0..167-d { if edge(i, i+d) { self.r[d-1] += self.s[i] as i32 * self.s[i+d] as i32; } } }
        self.energy = self.r.iter().map(|&x| (x as i64)*(x as i64)).sum();
    }
    fn flip(&mut self, p: usize) {
        let old = self.s[p] as i32;
        for d in 1..84 {
            let mut n = 0i32;
            if p+d < 167 && edge(p,p+d) { n += self.s[p+d] as i32; }
            if p >= d && edge(p-d,p) { n += self.s[p-d] as i32; }
            let delta = -2*old*n;
            let before = self.r[d-1] as i64;
            let after = before + delta as i64;
            self.energy += after*after-before*before;
            self.r[d-1] += delta;
        }
        self.s[p] = -self.s[p];
    }
    fn weighted(&self, w: &[i64;83]) -> i64 { let base:i64=self.r.iter().zip(w).map(|(&x,&y)| y*(x as i64)*(x as i64)).sum();let total:i64=self.r.iter().map(|&x|x as i64).sum();base+total*total/4 }
    fn weighted_l1(&self,w:&[i64;83])->i64{self.r.iter().zip(w).map(|(&x,&y)|y*(x.abs() as i64)).sum()}
}

#[derive(Clone,Copy)] struct Rng(u64);
impl Rng {
    fn next(&mut self)->u64 { let mut x=self.0; x^=x<<13;x^=x>>7;x^=x<<17;self.0=x;x }
    fn usize(&mut self,n:usize)->usize {(self.next() as usize)%n}
    fn unit(&mut self)->f64 {((self.next()>>11) as f64)/(1u64<<53) as f64}
}

fn random_state(rng: &mut Rng) -> State {
    let mut s=[1i8;167]; for x in &mut s { if rng.next()&1 != 0 {*x=-1;} } State::new(s)
}

fn parity_seed() -> State {
    State::new([-1,-1,-1,-1,1,1,-1,-1,-1,-1,1,-1,1,1,-1,-1,1,1,1,-1,1,1,1,1,-1,-1,1,-1,-1,-1,-1,-1,-1,-1,1,1,-1,1,1,-1,-1,-1,1,-1,-1,1,1,1,-1,-1,1,-1,1,-1,1,-1,-1,-1,1,1,-1,1,-1,-1,-1,1,-1,-1,1,1,-1,-1,-1,-1,1,-1,1,1,-1,-1,1,-1,1,1,-1,-1,1,-1,-1,-1,1,1,1,1,1,-1,-1,-1,1,1,-1,1,1,-1,1,-1,1,1,-1,1,1,1,1,-1,-1,-1,-1,-1,-1,1,1,-1,-1,-1,1,1,-1,-1,1,-1,-1,1,1,-1,1,-1,1,-1,-1,1,-1,1,1,1,-1,-1,-1,-1,-1,1,1,1,-1,-1,1,-1,-1,1,-1,1,-1,-1,1,-1,-1,-1,-1])
}

fn parity_basis_index(state:&mut State,g:usize,positions:&mut[usize;16],used:&mut usize){
    if g<41 {positions[*used]=g;positions[*used+1]=82-g;state.flip(g);state.flip(82-g);*used+=2}
    else if g<82 {let j=g-41;positions[*used]=84+j;positions[*used+1]=166-j;state.flip(84+j);state.flip(166-j);*used+=2}
    else {let p=[41usize,83,125][g-82];positions[*used]=p;state.flip(p);*used+=1}
}
fn parity_basis_move(state:&mut State,rng:&mut Rng,positions:&mut[usize;16],used:&mut usize){let g=rng.usize(85);parity_basis_index(state,g,positions,used)}
fn basis_contribution(state:&State,g:usize)->[i32;4]{let mut c=[0i32;4];let mut add=|p:usize|{let x=state.s[p] as i32;if p<84{c[0]+=x;c[2]+=x*q(p) as i32}else{c[1]+=x;c[3]+=x*q(p) as i32}};if g<41{add(g);add(82-g)}else if g<82{let j=g-41;add(84+j);add(166-j)}else{add([41usize,83,125][g-82])}c}
fn row_basis_move(state:&mut State,rng:&mut Rng,positions:&mut[usize;16],used:&mut usize){for _ in 0..32{let g=rng.usize(85);let h=rng.usize(85);if h==g{continue}let c=basis_contribution(state,g);let d=basis_contribution(state,h);let target=[-(c[0]+d[0]),-(c[1]+d[1]),-(c[2]+d[2]),-(c[3]+d[3])];let mut matches=[0usize;85];let mut n=0;for k in 0..85{if k!=g&&k!=h&&basis_contribution(state,k)==target{matches[n]=k;n+=1}}if n>0{let k=matches[rng.usize(n)];parity_basis_index(state,g,positions,used);parity_basis_index(state,h,positions,used);parity_basis_index(state,k,positions,used);return}if c==[0,0,0,0]{parity_basis_index(state,g,positions,used);return}if (0..4).all(|i|d[i]==-c[i]){parity_basis_index(state,g,positions,used);parity_basis_index(state,h,positions,used);return}}}

fn update(state:&State,id:usize,started:Instant,atomic:&AtomicI64,best:&Mutex<State>) {
    let mut seen=atomic.load(Ordering::Relaxed);
    while state.energy<seen { match atomic.compare_exchange_weak(seen,state.energy,Ordering::SeqCst,Ordering::Relaxed) {
        Ok(_)=>{*best.lock().unwrap()=state.clone();let signs=state.s.iter().map(|x|x.to_string()).collect::<Vec<_>>().join(",");let residual=state.r.iter().map(|x|x.to_string()).collect::<Vec<_>>().join(",");let _=fs::write("Find a Hadamard matrix of order 668/special_golay_167_live.json",format!("{{\"energy_normalized\":{},\"residual_divided_by_4\":[{}],\"s\":[{}]}}\n",state.energy,residual,signs));eprintln!("best energy={} worker={} elapsed_s={:.3}",state.energy,id,started.elapsed().as_secs_f64());return},
        Err(x)=>seen=x
    }}
}

fn run_worker(id:usize,deadline:Instant,started:Instant,atomic:Arc<AtomicI64>,best:Arc<Mutex<State>>,solved:Arc<AtomicBool>,parity:bool,row_mode:bool)->u64 {
    let epoch=SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos() as u64;
    let mut rng=Rng(epoch^(id as u64+1).wrapping_mul(0x9e3779b97f4a7c15)); let mut moves=0;
    while Instant::now()<deadline && !solved.load(Ordering::Relaxed) {
        let mut state=if !parity&&rng.usize(5)==0 {random_state(&mut rng)} else {best.lock().unwrap().clone()};
        for _ in 0..rng.usize(32) {if row_mode{let mut p=[0usize;16];let mut u=0;row_basis_move(&mut state,&mut rng,&mut p,&mut u)}else if parity{let mut p=[0usize;16];let mut u=0;parity_basis_move(&mut state,&mut rng,&mut p,&mut u)}else{state.flip(rng.usize(167))}}
        let mut weights=[1i64;83]; let mut stale=0usize; let mut local=state.energy;
        for step in 0..300_000usize {
            if step&8191==0 && (Instant::now()>=deadline||solved.load(Ordering::Relaxed)){break}
            let phase=step as f64/300000.0;
            let temp=(if id%3==0 {500.0}else if id%3==1 {150.0}else{45.0})*(0.0005f64).powf(phase)+0.02;
            let roll=rng.usize(1000); let count=if row_mode{if roll<800{1}else{2}}else if roll<680{1}else if roll<940{2}else if roll<995{3}else{4+rng.usize(5)};
            let use_l1=id%3==2;let before=if use_l1{state.weighted_l1(&weights)}else{state.weighted(&weights)}; let mut chosen=[0usize;16];let mut used=0usize;
            if row_mode && id%4==3 && count==1 {
                // A best-of neighborhood worker complements the cheap random
                // walkers: inspect coordinated row-kernel moves, then commit
                // the best one without ever leaving the required row tuple.
                let mut best_positions=[0usize;16];let mut best_used=0usize;let mut best_score=i64::MAX;
                for _ in 0..32 {
                    let mut trial=[0usize;16];let mut n=0usize;
                    row_basis_move(&mut state,&mut rng,&mut trial,&mut n);
                    let score=if use_l1{state.weighted_l1(&weights)}else{state.weighted(&weights)};
                    for &p in trial[..n].iter().rev(){state.flip(p)}
                    if n>0&&score<best_score{best_score=score;best_used=n;best_positions[..n].copy_from_slice(&trial[..n])}
                }
                for &p in &best_positions[..best_used]{state.flip(p);chosen[used]=p;used+=1}
            }
            else if row_mode {for _ in 0..count{row_basis_move(&mut state,&mut rng,&mut chosen,&mut used)}}
            else if parity&&id%4==3&&count==1&&roll%3==0 {let mut best_g=0usize;let mut best_score=i64::MAX;for _ in 0..12{let g=rng.usize(85);let mut test=[0usize;16];let mut n=0;parity_basis_index(&mut state,g,&mut test,&mut n);let score=if use_l1{state.weighted_l1(&weights)}else{state.weighted(&weights)};for &p in test[..n].iter().rev(){state.flip(p)}if score<best_score{best_score=score;best_g=g}}parity_basis_index(&mut state,best_g,&mut chosen,&mut used)}
            else if parity {for _ in 0..count{parity_basis_move(&mut state,&mut rng,&mut chosen,&mut used)}}
            else {for x in chosen.iter_mut().take(count){*x=rng.usize(167);state.flip(*x);used+=1}}
            moves+=1; let delta=(if use_l1{state.weighted_l1(&weights)}else{state.weighted(&weights)})-before;
            if delta>0 && rng.unit()>=(-(delta as f64)/temp).exp(){for &p in chosen[..used].iter().rev(){state.flip(p)}}
            else if state.energy<local {local=state.energy;stale=0;update(&state,id,started,&atomic,&best);if state.energy==0{let mut check=state.clone();check.recompute();if check.energy==0{*best.lock().unwrap()=check;solved.store(true,Ordering::SeqCst);break}}}
            else {stale+=1}
            if id%2==1 && stale>40000 {for j in 0..83{if state.r[j]!=0{weights[j]=(weights[j]+1+(state.r[j].abs()/4) as i64).min(64)}}stale=0}
            else if stale>80000 {for _ in 0..(8+rng.usize(24)){if row_mode{let mut p=[0usize;16];let mut u=0;row_basis_move(&mut state,&mut rng,&mut p,&mut u)}else if parity{let mut p=[0usize;16];let mut u=0;parity_basis_move(&mut state,&mut rng,&mut p,&mut u)}else{state.flip(rng.usize(167))}}stale=0}
        }
    } moves
}

fn expand_runs(runs:&[usize])->[i8;167]{let mut out=[1i8;167];let mut p=0;let mut sign=1;for &n in runs{for _ in 0..n{out[p]=sign;p+=1}sign=-sign}assert_eq!(p,167);out}

fn parse_seed(path:&str)->Option<[i8;167]>{let text=fs::read_to_string(path).ok()?;let start=text.find("\"s\"")?;let bytes=text[start..].as_bytes();let mut out=[1i8;167];let mut count=0usize;let mut i=0usize;while i<bytes.len()&&count<167{if bytes[i]==b'-'&&i+1<bytes.len()&&bytes[i+1]==b'1'{out[count]=-1;count+=1;i+=2}else if bytes[i]==b'1'{out[count]=1;count+=1;i+=1}else{i+=1}}if count==167{Some(out)}else{None}}

fn main(){
    let args:Vec<String>=env::args().collect();let seconds=args.get(1).and_then(|x|x.parse().ok()).unwrap_or(600);let threads=args.get(2).and_then(|x|x.parse().ok()).unwrap_or(10);
    let paper_runs=[4,4,4,4,4,2,1,1,2,1,1,2,1,1,2,1,1,2,1,1,1,5,4,4,4,4,2,1,1,2,1,1,2,1,1,2,1,1,2,1,1,2,1,1,4,4,4,4,3,1,2,1,1,2,1,1,2,1,1,2,1,1,2,1,3,4,4,4,4,3,1,2,1,1,2,1,1,2,1,1,2,1,1,2,1];
    let parity=args.get(3).map(|x|x=="parity"||x=="row").unwrap_or(false);let row_mode=args.get(3).map(|x|x=="row").unwrap_or(false);let mut seed=if parity{args.get(4).and_then(|p|parse_seed(p)).map(State::new).unwrap_or_else(parity_seed)}else{args.get(3).and_then(|p|parse_seed(p)).map(State::new).unwrap_or_else(||State::new(expand_runs(&paper_runs)))};let mut init_rng=Rng(668);if !parity{for _ in 0..200{let candidate=random_state(&mut init_rng);if candidate.energy<seed.energy{seed=candidate}}}
    eprintln!("seed energy={}",seed.energy);let started=Instant::now();let deadline=started+Duration::from_secs(seconds);let atomic=Arc::new(AtomicI64::new(seed.energy));let best=Arc::new(Mutex::new(seed));let solved=Arc::new(AtomicBool::new(false));let mut hs=vec![];
    for id in 0..threads{let a=atomic.clone();let b=best.clone();let s=solved.clone();hs.push(thread::spawn(move||run_worker(id,deadline,started,a,b,s,parity,row_mode)))}
    let moves:u64=hs.into_iter().map(|h|h.join().unwrap()).sum();let mut answer=best.lock().unwrap().clone();answer.recompute();let ok=answer.energy==0;
    let signs=answer.s.iter().map(|x|x.to_string()).collect::<Vec<_>>().join(",");let residual=answer.r.iter().map(|x|x.to_string()).collect::<Vec<_>>().join(",");
    let json=format!("{{\n  \"construction\": \"special Golay quadruple length 167\",\n  \"solved\": {},\n  \"energy_normalized\": {},\n  \"elapsed_s\": {:.6},\n  \"moves\": {},\n  \"residual_divided_by_4\": [{}],\n  \"s\": [{}]\n}}\n",ok,answer.energy,started.elapsed().as_secs_f64(),moves,residual,signs);
    let path=if ok{"Find a Hadamard matrix of order 668/special_golay_167_native_candidate.json"}else{"Find a Hadamard matrix of order 668/special_golay_167_native_summary.json"};fs::write(path,json).unwrap();println!("result solved={} energy={} moves={} elapsed_s={:.3} output={}",ok,answer.energy,moves,started.elapsed().as_secs_f64(),path)
}
