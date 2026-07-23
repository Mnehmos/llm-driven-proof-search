//! Parity-space memetic search for base sequences BS(84,83).
//!
//! For a binary sequence bit b=(1-a)/2, the mod-4 class of aperiodic
//! autocorrelation at shift d depends only on boundary bits.  Across the two
//! length-84 and two length-83 sequences, the 83 nonzero boundary signatures
//! form a basis.  Equal signatures occur in four-bit classes (the same
//! mirrored position in the two equal-length sequences).  Consequently:
//!   * a minimum-Hamming projection to residual == 0 (mod 4) chooses one bit
//!     in every defective class;
//!   * flipping any two bits in a class preserves every mod-4 equation; and
//!   * copying complete classes between parity-valid parents preserves them.
//!
//! This program uses randomized minimum-shell projections, exact class-wise
//! crossover, unrestricted parity-preserving pair flips, breakout weights,
//! and tabu diversification.  Unlike the earlier fixed-Fourier-fibre search,
//! it lets the row, alternating, and z=i components move.  Every published
//! state is rebuilt from its raw sequences and checked independently.

use std::env;
use std::fs;
use std::sync::{Arc, Mutex};
use std::sync::atomic::{AtomicBool, AtomicI64, AtomicU64, Ordering};
use std::thread;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

const L: [usize; 4] = [84, 84, 83, 83];
const H: usize = 83;

#[derive(Clone)]
struct State {
    a: [Vec<i8>; 4],
    r: [i32; H],
    e: i64,
}

impl State {
    fn new(a: [Vec<i8>; 4]) -> Self {
        let mut out = Self { a, r: [0; H], e: 0 };
        out.recompute();
        out
    }

    fn recompute(&mut self) {
        self.r = [0; H];
        for k in 0..4 {
            for d in 1..L[k] {
                for i in 0..L[k]-d {
                    self.r[d-1] += self.a[k][i] as i32 * self.a[k][i+d] as i32;
                }
            }
        }
        self.e = self.r.iter().map(|&x| (x as i64)*(x as i64)).sum();
    }

    fn flip(&mut self, k: usize, p: usize) {
        let old = self.a[k][p] as i32;
        for d in 1..L[k] {
            let mut z = 0;
            if p+d < L[k] { z += self.a[k][p+d] as i32; }
            if p >= d { z += self.a[k][p-d] as i32; }
            let dr = -2*old*z;
            let before = self.r[d-1] as i64;
            let after = before + dr as i64;
            self.e += after*after - before*before;
            self.r[d-1] += dr;
        }
        self.a[k][p] = -self.a[k][p];
    }

    fn toggle_move(&mut self, mv: &Move) {
        self.flip(mv.b1.0, mv.b1.1);
        if let Some((k,p)) = mv.b2 { self.flip(k,p); }
    }

    fn parity_bad(&self) -> usize {
        self.r.iter().filter(|&&x| x.rem_euclid(4) != 0).count()
    }

    fn l1(&self) -> i64 { self.r.iter().map(|x| x.abs() as i64).sum() }

    fn rows(&self) -> [i32;4] {
        std::array::from_fn(|k| self.a[k].iter().map(|&x|x as i32).sum())
    }

    fn alts(&self) -> [i32;4] {
        std::array::from_fn(|k| self.a[k].iter().enumerate()
            .map(|(i,&x)| if i&1 == 0 {x as i32} else {-(x as i32)}).sum())
    }

    fn z4(&self) -> [i32;8] {
        let mut out = [0;8];
        for k in 0..4 {
            for (i,&x) in self.a[k].iter().enumerate() {
                match i&3 {
                    0 => out[2*k] += x as i32,
                    1 => out[2*k+1] += x as i32,
                    2 => out[2*k] -= x as i32,
                    _ => out[2*k+1] -= x as i32,
                }
            }
        }
        out
    }
}

#[derive(Clone, Copy)]
struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13; x ^= x >> 7; x ^= x << 17;
        self.0 = x; x
    }
    fn usize(&mut self, n: usize) -> usize { self.next() as usize % n }
    fn coin(&mut self) -> bool { self.next() & 1 != 0 }
}

#[derive(Clone)]
struct Class { bits: [(usize,usize);4], sig: u128 }

#[derive(Clone, Copy)]
struct Move { b1: (usize,usize), b2: Option<(usize,usize)> }

fn parse(path: &str) -> Option<State> {
    let text = fs::read_to_string(path).ok()?;
    let start = text.find("\"sequences\"")?;
    let b = text[start..].as_bytes();
    let need: usize = L.iter().sum();
    let mut v = Vec::with_capacity(need);
    let mut i = 0;
    while i < b.len() && v.len() < need {
        if b[i] == b'-' && i+1 < b.len() && b[i+1] == b'1' {
            v.push(-1); i += 2;
        } else if b[i] == b'1' {
            v.push(1); i += 1;
        } else { i += 1; }
    }
    if v.len() != need { return None; }
    let mut off = 0;
    let a = std::array::from_fn(|k| {
        let x = v[off..off+L[k]].to_vec(); off += L[k]; x
    });
    Some(State::new(a))
}

fn bit_signature(len: usize, p: usize) -> u128 {
    let mut s = 0u128;
    for d in 1..=H {
        // A flipped bit changes R_d/2 (mod 2) exactly when it has one,
        // rather than zero or two, partners at distance d.
        let left = p >= d;
        let right = p+d < len;
        if left ^ right { s |= 1u128 << (d-1); }
    }
    s
}

fn classes() -> (Vec<Class>, [(usize,usize);2]) {
    let mut c = Vec::with_capacity(H);
    for j in 0..42 {
        let p = j; let q = 83-j;
        let sig = bit_signature(84,p);
        assert_eq!(sig, bit_signature(84,q));
        c.push(Class { bits: [(0,p),(0,q),(1,p),(1,q)], sig });
    }
    for j in 0..41 {
        let p = j; let q = 82-j;
        let sig = bit_signature(83,p);
        assert_eq!(sig, bit_signature(83,q));
        c.push(Class { bits: [(2,p),(2,q),(3,p),(3,q)], sig });
    }
    assert_eq!(c.len(), H);
    assert_eq!(bit_signature(83,41), 0);
    (c, [(2,41),(3,41)])
}

fn solve_defects(base: &State, cls: &[Class]) -> u128 {
    let mut vecs = [0u128; H];
    let mut comb = [0u128; H];
    let mut rank = 0;
    for (j,c) in cls.iter().enumerate() {
        let mut v = c.sig;
        let mut w = 1u128 << j;
        let mut inserted = false;
        for p in (0..H).rev() {
            if (v >> p)&1 == 0 { continue; }
            if vecs[p] != 0 { v ^= vecs[p]; w ^= comb[p]; }
            else { vecs[p]=v; comb[p]=w; rank += 1; inserted = true; break; }
        }
        assert!(inserted, "dependent boundary signature at class {j}");
    }
    assert_eq!(rank, H, "boundary signatures must have full rank");
    let mut target = 0u128;
    for d in 0..H {
        assert_eq!(base.r[d].rem_euclid(2), 0);
        if base.r[d].rem_euclid(4) != 0 { target |= 1u128 << d; }
    }
    let original = target;
    let mut answer = 0u128;
    for p in (0..H).rev() {
        if (target >> p)&1 == 0 { continue; }
        assert_ne!(vecs[p],0, "unsolved parity equation");
        target ^= vecs[p]; answer ^= comb[p];
    }
    assert_eq!(target,0);
    let mut check = 0u128;
    for j in 0..H { if (answer>>j)&1 != 0 { check ^= cls[j].sig; } }
    assert_eq!(check,original);
    answer
}

fn verify(s: &State, require_parity: bool) -> State {
    let t = State::new(s.a.clone());
    assert_eq!(t.r,s.r,"incremental residual drift");
    assert_eq!(t.e,s.e,"incremental energy drift");
    if require_parity { assert_eq!(t.parity_bad(),0,"parity-space drift"); }
    if t.e == 0 { assert!(t.r.iter().all(|&x|x==0)); }
    t
}

fn norm<const N:usize>(x: [i32;N]) -> i32 { x.iter().map(|v|v*v).sum() }

fn json(s: &State, elapsed: f64, iterations: u64, projections: usize,
        defect_classes: usize, solved: bool) -> String {
    let t = verify(s,true);
    let seq = t.a.iter().map(|x| format!("[{}]",x.iter().map(|v|v.to_string())
        .collect::<Vec<_>>().join(","))).collect::<Vec<_>>().join(",");
    let residual = t.r.iter().map(|x|x.to_string()).collect::<Vec<_>>().join(",");
    format!(concat!(
        "{{\"construction\":\"base sequences BS(84,83)\",",
        "\"search\":\"agent_bp2 parity-space memetic projection/crossover\",",
        "\"solved\":{},\"independently_recomputed\":true,",
        "\"residual_mod4_exact\":true,\"energy\":{},\"l1\":{},\"parity_bad\":0,",
        "\"elapsed_s\":{:.6},\"iterations\":{},\"initial_projections\":{},",
        "\"defect_classes_from_soft_seed\":{},",
        "\"row_sums\":{:?},\"row_norm\":{},",
        "\"alternating_sums\":{:?},\"alternating_norm\":{},",
        "\"z4_components\":{:?},\"z4_norm\":{},",
        "\"residual\":[{}],\"sequences\":[{}]}}\n"),
        solved,t.e,t.l1(),elapsed,iterations,projections,defect_classes,
        t.rows(),norm(t.rows()),t.alts(),norm(t.alts()),t.z4(),norm(t.z4()),
        residual,seq)
}

fn minimal_projection(base: &State, cls: &[Class], defects: u128, rng: &mut Rng)
        -> (State, [u8;H]) {
    let mut s = base.clone();
    let mut selected = [255u8;H];
    for j in 0..H {
        if (defects>>j)&1 != 0 {
            let q = rng.usize(4);
            selected[j]=q as u8;
            let (k,p)=cls[j].bits[q]; s.flip(k,p);
        }
    }
    assert_eq!(s.parity_bad(),0);
    (s,selected)
}

fn shell_descent(mut s: State, mut selected: [u8;H], cls: &[Class], defects: u128,
                 rng: &mut Rng) -> State {
    loop {
        let mut best = s.e;
        let mut pick: Option<(usize,usize)> = None;
        let mut ties=0;
        for j in 0..H {
            if (defects>>j)&1 == 0 { continue; }
            let old=selected[j] as usize;
            for q in 0..4 {
                if q==old {continue;}
                let b1=cls[j].bits[old]; let b2=cls[j].bits[q];
                s.flip(b1.0,b1.1); s.flip(b2.0,b2.1);
                if s.e < best { best=s.e; pick=Some((j,q)); ties=1; }
                else if s.e==best && s.e < s.e + 1 { // tie reservoir, guarded below
                    if pick.is_some() { ties+=1; if rng.usize(ties)==0 {pick=Some((j,q));} }
                }
                s.flip(b2.0,b2.1); s.flip(b1.0,b1.1);
            }
        }
        let Some((j,q))=pick else {break};
        if best >= s.e {break;}
        let old=selected[j] as usize;
        let b1=cls[j].bits[old]; let b2=cls[j].bits[q];
        s.flip(b1.0,b1.1); s.flip(b2.0,b2.1); selected[j]=q as u8;
    }
    verify(&s,true)
}

fn all_moves(cls: &[Class], centers: [(usize,usize);2]) -> Vec<Move> {
    let mut out=Vec::with_capacity(H*6+2);
    for c in cls {
        for p in 0..4 { for q in p+1..4 {
            out.push(Move{b1:c.bits[p],b2:Some(c.bits[q])});
        }}
    }
    out.push(Move{b1:centers[0],b2:None});
    out.push(Move{b1:centers[1],b2:None});
    out
}

fn fourier_margin_score(s:&State)->i64 {
    let dr=(norm(s.rows())-334) as i64;
    let da=(norm(s.alts())-334) as i64;
    let dz=(norm(s.z4())-334) as i64;
    assert_eq!(dr.rem_euclid(8),0);
    assert_eq!(da.rem_euclid(8),0);
    assert_eq!(dz.rem_euclid(8),0);
    (dr/8)*(dr/8)+(da/8)*(da/8)+(dz/8)*(dz/8)
}

fn fourier_exact(s:&State)->bool {
    norm(s.rows())==334 && norm(s.alts())==334 && norm(s.z4())==334
}

fn spectral_values(s:&State)->(i32,i32,i32) {
    let mut q3=0;
    let mut a5=0;
    let mut b5=0;
    for k in 0..4 {
        let mut v3=[0i32;3];
        let mut v5=[0i32;5];
        for (i,&x) in s.a[k].iter().enumerate() {
            v3[i%3]+=x as i32;
            v5[i%5]+=x as i32;
        }
        q3+=v3.iter().map(|x|x*x).sum::<i32>()-
            (v3[0]*v3[1]+v3[1]*v3[2]+v3[2]*v3[0]);
        let s0=v5.iter().map(|x|x*x).sum::<i32>();
        let s1=(0..5).map(|i|v5[i]*v5[(i+1)%5]).sum::<i32>();
        let s2=(0..5).map(|i|v5[i]*v5[(i+2)%5]).sum::<i32>();
        a5+=s0-s1;b5+=s1-s2;
    }
    (q3,a5,b5)
}

fn septimal_values(s:&State)->(i32,i32,i32) {
    let mut out=[0i32;3];
    for k in 0..4 {
        let mut v=[0i32;7];
        for (i,&x) in s.a[k].iter().enumerate() {v[i%7]+=x as i32;}
        let corr:[i32;4]=std::array::from_fn(|d|
            (0..7).map(|i|v[i]*v[(i+d)%7]).sum());
        for d in 0..3 {out[d]+=corr[d]-corr[d+1];}
    }
    (out[0],out[1],out[2])
}

fn spectral_margin_score(s:&State)->i64 {
    let (q3,a5,b5)=spectral_values(s);
    let (a7,b7,c7)=septimal_values(s);
    let d=[q3-334,a5-334,b5,a7-334,b7,c7];
    assert!(d.iter().all(|x|x.rem_euclid(4)==0));
    fourier_margin_score(s)+d.iter().map(|&x|{let y=(x/4)as i64;y*y}).sum::<i64>()
}

fn spectral_exact(s:&State)->bool {
    fourier_exact(s)&&spectral_values(s)==(334,334,0)&&septimal_values(s)==(334,0,0)
}

fn objective(s:&State, weights:&[i64;H], kind:usize, guide:bool, spectral:bool)->i64 {
    let base=match kind {
        0 => s.e,
        1 => s.r.iter().zip(weights).map(|(&r,&w)|w*(r as i64)*(r as i64)).sum(),
        2 => s.r.iter().zip(weights).map(|(&r,&w)|w*r.abs() as i64).sum(),
        _ => s.r.iter().zip(weights).map(|(&r,&w)|
            w*(r as i64)*(r as i64)+8*r.abs() as i64).sum(),
    };
    if guide {
        let margin=if spectral{spectral_margin_score(s)}else{fourier_margin_score(s)};
        base + [16i64,32,8,64][kind]*margin
    } else {base}
}

fn classwise_child(a:&State,b:&State,cls:&[Class],centers:[(usize,usize);2],rng:&mut Rng)->State {
    let mut x=a.a.clone();
    for c in cls {
        if rng.coin() {
            for &(k,p) in &c.bits { x[k][p]=b.a[k][p]; }
        }
    }
    for &(k,p) in &centers { if rng.coin(){x[k][p]=b.a[k][p];} }
    let s=State::new(x);
    assert_eq!(s.parity_bad(),0,"class-wise crossover broke parity");
    s
}

fn sparse_class_child(a:&State,b:&State,cls:&[Class],centers:[(usize,usize);2],
                      rng:&mut Rng,count:usize)->State {
    let mut x=a.a.clone();
    let mut chosen=[false;H];
    let mut n=0;
    while n<count.min(H) {
        let j=rng.usize(H);
        if chosen[j] {continue;}
        chosen[j]=true;n+=1;
        for &(k,p) in &cls[j].bits {x[k][p]=b.a[k][p];}
    }
    for &(k,p) in &centers {if rng.usize(8)==0{x[k][p]=b.a[k][p];}}
    let s=State::new(x);
    assert_eq!(s.parity_bad(),0,"sparse class crossover broke parity");
    s
}

fn perturb(s:&mut State,moves:&[Move],rng:&mut Rng,n:usize) {
    for _ in 0..n { let mv=moves[rng.usize(moves.len())]; s.toggle_move(&mv); }
    assert_eq!(s.parity_bad(),0);
}

struct Shared {
    global_e: AtomicI64,
    global: Mutex<State>,
    pool: Mutex<Vec<State>>,
    fourier_e: AtomicI64,
    fourier: Mutex<Option<State>>,
    stop: AtomicBool,
    iterations: AtomicU64,
    start: Instant,
    projections: usize,
    defects: usize,
    guide: bool,
    spectral: bool,
}

fn pool_insert(s:&State,shared:&Shared) {
    let checked=verify(s,true);
    let mut pool=shared.pool.lock().unwrap();
    // Exact duplicate detection is cheap at this pool size.
    if pool.iter().any(|x|x.a==checked.a) {return;}
    pool.push(checked);
    pool.sort_by_key(|x|if shared.guide{x.e+16*if shared.spectral{spectral_margin_score(x)}else{fourier_margin_score(x)}}else{x.e});
    if pool.len()>48 {pool.truncate(48);}
}

fn publish(s:&State,id:usize,shared:&Shared) {
    let checked=verify(s,true);
    pool_insert(&checked,shared);
    if shared.guide && if shared.spectral{spectral_exact(&checked)}else{fourier_exact(&checked)} {
        let mut fseen=shared.fourier_e.load(Ordering::Relaxed);
        while checked.e<fseen {
            match shared.fourier_e.compare_exchange_weak(fseen,checked.e,
                    Ordering::SeqCst,Ordering::Relaxed) {
                Ok(_)=>{
                    *shared.fourier.lock().unwrap()=Some(checked.clone());
                    let body=json(&checked,shared.start.elapsed().as_secs_f64(),
                        shared.iterations.load(Ordering::Relaxed),shared.projections,
                        shared.defects,checked.e==0);
                    let _=fs::write("agent_bp2_fourier_exact_live.json",body);
                    eprintln!("agent_bp2 guided-exact best energy={} l1={} rows={:?} alts={:?} z4={:?} spectral={:?}/{:?} worker={} elapsed_s={:.3}",
                        checked.e,checked.l1(),checked.rows(),checked.alts(),checked.z4(),
                        spectral_values(&checked),septimal_values(&checked),id,
                        shared.start.elapsed().as_secs_f64());
                    break;
                }
                Err(x)=>fseen=x,
            }
        }
    }
    let mut seen=shared.global_e.load(Ordering::Relaxed);
    while checked.e < seen {
        match shared.global_e.compare_exchange_weak(seen,checked.e,Ordering::SeqCst,Ordering::Relaxed) {
            Ok(_) => {
                *shared.global.lock().unwrap()=checked.clone();
                let body=json(&checked,shared.start.elapsed().as_secs_f64(),
                    shared.iterations.load(Ordering::Relaxed),shared.projections,shared.defects,
                    checked.e==0);
                let live=if shared.guide{"agent_bp2_fourier_live.json"}else{"agent_bp2_live.json"};
                let _=fs::write(live,body);
                eprintln!("agent_bp2 best energy={} l1={} rows={:?}/{} alts={:?}/{} z4norm={} worker={} elapsed_s={:.3}",
                    checked.e,checked.l1(),checked.rows(),norm(checked.rows()),checked.alts(),
                    norm(checked.alts()),norm(checked.z4()),id,shared.start.elapsed().as_secs_f64());
                if checked.e==0 {shared.stop.store(true,Ordering::SeqCst);}
                break;
            }
            Err(x)=>seen=x,
        }
    }
}

fn pool_seed(shared:&Shared,cls:&[Class],centers:[(usize,usize);2],rng:&mut Rng)->State {
    let pool=shared.pool.lock().unwrap();
    if pool.len()==1 {return pool[0].clone();}
    let n=pool.len().min(24);
    let i=rng.usize(n); let mut j=rng.usize(n-1); if j>=i {j+=1;}
    classwise_child(&pool[i],&pool[j],cls,centers,rng)
}

fn worker(id:usize,end:Instant,shared:Arc<Shared>,cls:Arc<Vec<Class>>,
          centers:[(usize,usize);2],moves:Arc<Vec<Move>>)->u64 {
    let epoch=SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos() as u64;
    let mut rng=Rng(epoch ^ (id as u64+911).wrapping_mul(0x9e3779b97f4a7c15));
    let kind=id&3;
    let mut s=pool_seed(&shared,&cls,centers,&mut rng);
    let initial_perturb=8+rng.usize(24);
    perturb(&mut s,&moves,&mut rng,initial_perturb);
    let mut weights=[1i64;H];
    let mut tabu=[[0u64;84];4];
    let mut iter=0u64;
    let mut stale=0u64;
    let mut local_best=objective(&s,&weights,kind,shared.guide,shared.spectral);
    let mut since_pool=0u64;

    while Instant::now()<end && !shared.stop.load(Ordering::Relaxed) {
        let aspiration=shared.global_e.load(Ordering::Relaxed);
        let mut pick:Option<(i64,i64,usize)>=None;
        let mut ties=0usize;
        for (mi,mv) in moves.iter().enumerate() {
            s.toggle_move(mv);
            let allowed=s.e<aspiration || (tabu[mv.b1.0][mv.b1.1]<=iter &&
                mv.b2.map(|(k,p)|tabu[k][p]<=iter).unwrap_or(true));
            if allowed {
                let score=objective(&s,&weights,kind,shared.guide,shared.spectral);
                let better=match pick {None=>true,Some((bs,be,_))=>score<bs || (score==bs&&s.e<be)};
                if better {pick=Some((score,s.e,mi));ties=1;}
                else if let Some((bs,be,_))=pick {
                    if score==bs&&s.e==be {ties+=1;if rng.usize(ties)==0{pick=Some((score,s.e,mi));}}
                }
            }
            s.toggle_move(mv);
        }
        let Some((_,_,mi))=pick else {tabu=[[0u64;84];4];continue};
        let mv=moves[mi]; s.toggle_move(&mv);
        iter+=1;stale+=1;since_pool+=1;
        let tenure=7+rng.usize(28) as u64+(stale/300).min(40);
        tabu[mv.b1.0][mv.b1.1]=iter+tenure;
        if let Some((k,p))=mv.b2 {tabu[k][p]=iter+tenure;}
        let score=objective(&s,&weights,kind,shared.guide,shared.spectral);
        if score<local_best {
            local_best=score;stale=0;
            publish(&s,id,&shared);
        }
        if s.e==0 {publish(&s,id,&shared);break;}
        if kind!=0 && stale>0 && stale%350==0 {
            for d in 0..H {if s.r[d]!=0 {weights[d]=(weights[d]+1+(s.r[d].abs()/4)as i64).min(128);}}
            local_best=objective(&s,&weights,kind,shared.guide,shared.spectral);
        }
        if since_pool>=900 {
            pool_insert(&s,&shared);since_pool=0;
        }
        if stale>1400 {
            s=pool_seed(&shared,&cls,centers,&mut rng);
            let restart_perturb=12+rng.usize(80);
            perturb(&mut s,&moves,&mut rng,restart_perturb);
            if rng.usize(3)==0 {weights=[1i64;H];}
            tabu=[[0u64;84];4];
            local_best=objective(&s,&weights,kind,shared.guide,shared.spectral);stale=0;since_pool=0;
        }
        if iter&1023==0 {
            verify(&s,true);
            shared.iterations.fetch_add(1024,Ordering::Relaxed);
        }
    }
    shared.iterations.fetch_add(iter&1023,Ordering::Relaxed);
    iter
}

fn scan_two_moves(base:&State) {
    let (cls,centers)=classes();
    let moves=all_moves(&cls,centers);
    let mut s=verify(base,true);
    let mut best=s.clone();
    let mut best_guide=s.clone();
    let mut best_fourier:Option<State>=if fourier_exact(&s){Some(s.clone())}else{None};
    let mut checked=0u64;
    for i in 0..moves.len() {
        s.toggle_move(&moves[i]);
        if s.e<best.e {best=verify(&s,true);}
        if s.e+16*fourier_margin_score(&s)<best_guide.e+16*fourier_margin_score(&best_guide) {
            best_guide=verify(&s,true);
        }
        if fourier_exact(&s)&&best_fourier.as_ref().map(|x|s.e<x.e).unwrap_or(true) {
            best_fourier=Some(verify(&s,true));
        }
        for j in i+1..moves.len() {
            s.toggle_move(&moves[j]); checked+=1;
            if s.e<best.e {best=verify(&s,true);}
            if s.e+16*fourier_margin_score(&s)<best_guide.e+16*fourier_margin_score(&best_guide) {
                best_guide=verify(&s,true);
            }
            if fourier_exact(&s)&&best_fourier.as_ref().map(|x|s.e<x.e).unwrap_or(true) {
                best_fourier=Some(verify(&s,true));
            }
            s.toggle_move(&moves[j]);
        }
        s.toggle_move(&moves[i]);
        if (i+1)%50==0 {eprintln!("agent_bp2 scan2 moves={} pairs={} bestE={} guidedE={} guidedMargin={}",
            i+1,checked,best.e,best_guide.e,fourier_margin_score(&best_guide));}
    }
    verify(&s,true);
    fs::write("agent_bp2_scan2_best.json",json(&best,0.0,checked,0,0,best.e==0)).unwrap();
    fs::write("agent_bp2_scan2_guided.json",json(&best_guide,0.0,checked,0,0,best_guide.e==0)).unwrap();
    if let Some(ref f)=best_fourier {
        fs::write("agent_bp2_scan2_fourier_exact.json",json(&f,0.0,checked,0,0,f.e==0)).unwrap();
    }
    println!("agent_bp2 scan2 complete pairs={} baseE={} bestE={} bestL1={} guidedE={} guidedMargin={} guidedNorms={}/{}/{} FourierExactE={}",
        checked,base.e,best.e,best.l1(),best_guide.e,fourier_margin_score(&best_guide),
        norm(best_guide.rows()),norm(best_guide.alts()),norm(best_guide.z4()),
        best_fourier.as_ref().map(|x|x.e.to_string()).unwrap_or_else(||"none".to_string()));
}

fn main() {
    let args:Vec<String>=env::args().collect();
    let secs=args.get(1).and_then(|x|x.parse().ok()).unwrap_or(600u64);
    let threads=args.get(2).and_then(|x|x.parse().ok()).unwrap_or(4usize);
    let path=args.get(3).map(String::as_str).unwrap_or("agent_bsd_soft_summary.json");
    let projections=args.get(4).and_then(|x|x.parse().ok()).unwrap_or(256usize);
    let mode=args.get(5).map(String::as_str).unwrap_or("");
    let spectral=mode=="spectralguide"||mode=="mixspectral";
    let guide=mode=="guide"||mode=="mixguide"||spectral;
    let mix=mode=="mix"||mode=="mixguide"||mode=="mixspectral";
    let base=parse(path).expect("checkpoint containing four sequences required");
    if mode=="scan2" {scan_two_moves(&base);return;}
    let (cls,centers)=classes();
    let defects=solve_defects(&base,&cls);
    let defect_count=defects.count_ones() as usize;
    eprintln!("agent_bp2 seed={} energy={} l1={} parity_bad={} defect_classes={} projections={}",
        path,base.e,base.l1(),base.parity_bad(),defect_count,projections);

    let epoch=SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos() as u64;
    let mut rng=Rng(epoch^0xa0761d6478bd642f);
    let mix_parent=if mix {
        let path2=args.get(6).expect("mix mode requires second checkpoint path");
        let p=verify(&parse(path2).expect("invalid second mix checkpoint"),true);
        eprintln!("agent_bp2 mix_parent={} energy={} l1={} margins={}",path2,p.e,p.l1(),fourier_margin_score(&p));
        Some(p)
    } else {None};
    let mut initial=Vec::with_capacity(projections.max(2));
    for i in 0..projections {
        let t=if let Some(ref p2)=mix_parent {
            if i==0 {base.clone()}
            else if i==1 {p2.clone()}
            else if i%5==0 {classwise_child(&base,p2,&cls,centers,&mut rng)}
            else {
                let count=2+rng.usize(29);
                if i&1==0 {sparse_class_child(&base,p2,&cls,centers,&mut rng,count)}
                else {sparse_class_child(p2,&base,&cls,centers,&mut rng,count)}
            }
        } else {
            let (s,sel)=minimal_projection(&base,&cls,defects,&mut rng);
            shell_descent(s,sel,&cls,defects,&mut rng)
        };
        initial.push(t);
        if (i+1)%32==0 {
            let b=initial.iter().map(|x|x.e).min().unwrap();
            eprintln!("agent_bp2 projection_shell completed={} best_energy={}",i+1,b);
        }
    }
    initial.sort_by_key(|s|if guide{s.e+16*if spectral{spectral_margin_score(s)}else{fourier_margin_score(s)}}else{s.e});
    initial.dedup_by(|a,b|a.a==b.a);
    if initial.len()>48 {initial.truncate(48);}
    let best=verify(&initial[0],true);
    eprintln!("agent_bp2 shell_best energy={} l1={} rows={:?}/{} alts={:?}/{} z4norm={} pool={}",
        best.e,best.l1(),best.rows(),norm(best.rows()),best.alts(),norm(best.alts()),
        norm(best.z4()),initial.len());

    let start=Instant::now();
    let initial_fourier=initial.iter().filter(|s|if spectral{spectral_exact(s)}else{fourier_exact(s)})
        .min_by_key(|s|s.e).cloned();
    let initial_fourier_e=initial_fourier.as_ref().map(|s|s.e).unwrap_or(i64::MAX);
    let shared=Arc::new(Shared{
        global_e:AtomicI64::new(best.e),global:Mutex::new(best.clone()),
        pool:Mutex::new(initial),fourier_e:AtomicI64::new(initial_fourier_e),
        fourier:Mutex::new(initial_fourier),stop:AtomicBool::new(best.e==0),
        iterations:AtomicU64::new(0),start,projections,defects:defect_count,guide,spectral,
    });
    let initial_live=if guide{"agent_bp2_fourier_live.json"}else{"agent_bp2_live.json"};
    fs::write(initial_live,json(&best,0.0,0,projections,defect_count,best.e==0)).unwrap();
    let cls=Arc::new(cls);let moves=Arc::new(all_moves(&cls,centers));
    eprintln!("agent_bp2 parity_moves={} threads={} seconds={} fourier_guide={} spectral_guide={}",moves.len(),threads,secs,guide,spectral);
    let end=start+Duration::from_secs(secs);
    let mut handles=Vec::new();
    for id in 0..threads {
        let sh=shared.clone();let c=cls.clone();let m=moves.clone();
        handles.push(thread::spawn(move||worker(id,end,sh,c,centers,m)));
    }
    let _worker_iters:u64=handles.into_iter().map(|h|h.join().unwrap()).sum();
    let answer=verify(&shared.global.lock().unwrap(),true);
    let solved=answer.e==0;
    let out=if solved{"agent_bp2_candidate.json"}else if guide{"agent_bp2_fourier_summary.json"}
        else{"agent_bp2_summary.json"};
    fs::write(out,json(&answer,start.elapsed().as_secs_f64(),
        shared.iterations.load(Ordering::Relaxed),projections,defect_count,solved)).unwrap();
    if guide {
        if let Some(f)=shared.fourier.lock().unwrap().clone() {
            fs::write("agent_bp2_fourier_exact_summary.json",json(&f,start.elapsed().as_secs_f64(),
                shared.iterations.load(Ordering::Relaxed),projections,defect_count,f.e==0)).unwrap();
        }
    }
    println!("agent_bp2 result solved={} energy={} l1={} parity_bad={} rows={:?}/{} alts={:?}/{} z4norm={} output={}",
        solved,answer.e,answer.l1(),answer.parity_bad(),answer.rows(),norm(answer.rows()),
        answer.alts(),norm(answer.alts()),norm(answer.z4()),out);
}
