//! Dual-margin / quartic-margin search for BS(84,83).
//!
//! Every elementary move swaps opposite signs in one sequence at positions
//! congruent modulo `modulus`.  Modulus 2 preserves both the ordinary row sum
//! and the alternating row sum.  Modulus 4 additionally preserves the real
//! and imaginary parts at z=i, a necessary Fourier identity for base
//! sequences.  Candidates are fully recomputed before publication.

use std::{collections::HashMap, env, fs, thread};
use std::sync::{Arc, Mutex};
use std::sync::atomic::{AtomicBool, AtomicI64, Ordering};
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
        let mut s = Self { a, r: [0; H], e: 0 };
        s.recompute();
        s
    }

    fn recompute(&mut self) {
        self.r = [0; H];
        for k in 0..4 {
            for d in 1..L[k] {
                for i in 0..L[k] - d {
                    self.r[d - 1] += self.a[k][i] as i32 * self.a[k][i + d] as i32;
                }
            }
        }
        self.e = self.r.iter().map(|&x| (x as i64) * (x as i64)).sum();
    }

    fn flip(&mut self, k: usize, p: usize) {
        let old = self.a[k][p] as i32;
        for d in 1..L[k] {
            let mut z = 0;
            if p + d < L[k] { z += self.a[k][p + d] as i32; }
            if p >= d { z += self.a[k][p - d] as i32; }
            let dr = -2 * old * z;
            let before = self.r[d - 1] as i64;
            let after = before + dr as i64;
            self.e += after * after - before * before;
            self.r[d - 1] += dr;
        }
        self.a[k][p] = -self.a[k][p];
    }

    fn swap(&mut self, k: usize, p: usize, q: usize) {
        debug_assert_ne!(self.a[k][p], self.a[k][q]);
        self.flip(k, p);
        self.flip(k, q);
    }

    fn rows(&self) -> [i32; 4] {
        std::array::from_fn(|k| self.a[k].iter().map(|&x| x as i32).sum())
    }

    fn alts(&self) -> [i32; 4] {
        std::array::from_fn(|k| self.a[k].iter().enumerate()
            .map(|(i, &x)| if i & 1 == 0 { x as i32 } else { -(x as i32) }).sum())
    }

    fn z4(&self) -> [i32; 8] {
        let mut out = [0; 8];
        for k in 0..4 {
            for (i, &x) in self.a[k].iter().enumerate() {
                match i & 3 {
                    0 => out[2*k] += x as i32,
                    1 => out[2*k+1] += x as i32,
                    2 => out[2*k] -= x as i32,
                    _ => out[2*k+1] -= x as i32,
                }
            }
        }
        out
    }

    fn parity_bad(&self) -> usize {
        self.r.iter().filter(|&&x| x.rem_euclid(4) != 0).count()
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
}

fn parse(path: &str) -> Option<State> {
    let text = fs::read_to_string(path).ok()?;
    let start = text.find("\"sequences\"")?;
    let b = text[start..].as_bytes();
    let need: usize = L.iter().sum();
    let mut v = Vec::with_capacity(need);
    let mut i = 0;
    while i < b.len() && v.len() < need {
        if b[i] == b'-' && i + 1 < b.len() && b[i+1] == b'1' {
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

fn norm4<const N: usize>(x: [i32; N]) -> i32 { x.iter().map(|v| v*v).sum() }

fn independently_verified(s: &State, rows: [i32; 4], alts: [i32; 4], z4: Option<[i32; 8]>,
                          require_parity0: bool) -> State {
    let mut t = State::new(s.a.clone());
    assert_eq!(t.rows(), rows, "ordinary margin drift");
    assert_eq!(t.alts(), alts, "alternating margin drift");
    assert_eq!(norm4(t.rows()), 334);
    assert_eq!(norm4(t.alts()), 334);
    if let Some(want) = z4 {
        assert_eq!(t.z4(), want, "z=i component drift");
        assert_eq!(norm4(t.z4()), 334);
    }
    if require_parity0 { assert_eq!(t.parity_bad(), 0, "residual mod-4 drift"); }
    assert_eq!(t.r.iter().step_by(2).sum::<i32>(), 0);
    assert_eq!(t.r.iter().skip(1).step_by(2).sum::<i32>(), 0);
    t.recompute();
    t
}

fn json(s: &State, modulus: usize, rows: [i32; 4], alts: [i32; 4], elapsed: f64,
        iterations: u64, solved: bool, require_parity0: bool) -> String {
    let seq = s.a.iter().map(|x| format!("[{}]", x.iter().map(|v| v.to_string())
        .collect::<Vec<_>>().join(","))).collect::<Vec<_>>().join(",");
    let residual = s.r.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(",");
    format!(concat!(
        "{{\"construction\":\"base sequences BS(84,83)\",",
        "\"search\":\"agent dual-margin exact-fibre tabu\",",
        "\"solved\":{},\"independently_recomputed\":true,",
        "\"move_modulus\":{},\"require_residual_mod4_zero\":{},",
        "\"energy\":{},\"l1\":{},\"parity_bad\":{},",
        "\"elapsed_s\":{:.6},\"iterations\":{},",
        "\"row_sums\":{:?},\"alternating_sums\":{:?},",
        "\"z4_components\":{:?},\"residual\":[{}],\"sequences\":[{}]}}\n"),
        solved, modulus, require_parity0, s.e,
        s.r.iter().map(|x| x.abs() as i64).sum::<i64>(), s.parity_bad(),
        elapsed, iterations, rows, alts, s.z4(), residual, seq)
}

fn quartic_seeds(base: &State, require_parity0: bool) -> Vec<State> {
    // Enumerate the complete one-dual-swap shell and retain the best-energy
    // representative of every z=i fibre whose component norm is exactly 334.
    let mut best: HashMap<[i32; 8], State> = HashMap::new();
    if norm4(base.z4()) == 334 && (!require_parity0 || base.parity_bad() == 0) {
        best.insert(base.z4(), base.clone());
    }
    for k in 0..4 {
        for p in 0..L[k] {
            for q in p+1..L[k] {
                if (p ^ q) & 1 != 0 || base.a[k][p] == base.a[k][q] { continue; }
                let mut s = base.clone(); s.swap(k, p, q);
                let z = s.z4();
                if norm4(z) != 334 || (require_parity0 && s.parity_bad() != 0) { continue; }
                match best.get(&z) {
                    None => { best.insert(z, s); },
                    Some(old) if s.e < old.e => { best.insert(z, s); },
                    _ => {},
                }
            }
        }
    }
    let mut out: Vec<State> = best.into_values().collect();
    out.sort_by_key(|s| s.e);
    out
}

fn objective(s: &State, weights: &[i64; H], kind: usize, parity_penalty: i64) -> i64 {
    let base = match kind {
        0 => s.e,
        1 => s.r.iter().zip(weights).map(|(&r,&w)| w*(r as i64)*(r as i64)).sum(),
        2 => s.r.iter().zip(weights).map(|(&r,&w)| w*r.abs() as i64).sum(),
        _ => s.r.iter().zip(weights).map(|(&r,&w)|
            w*(r as i64)*(r as i64) + 8*r.abs() as i64).sum(),
    };
    base + parity_penalty * s.parity_bad() as i64
}

fn random_swap(s: &mut State, rng: &mut Rng, modulus: usize, require_parity0: bool) {
    loop {
        let k = rng.usize(4);
        let c = rng.usize(modulus);
        let mut plus = [0usize; 84]; let mut np = 0;
        let mut minus = [0usize; 84]; let mut nm = 0;
        for p in (c..L[k]).step_by(modulus) {
            if s.a[k][p] == 1 { plus[np] = p; np += 1; }
            else { minus[nm] = p; nm += 1; }
        }
        if np != 0 && nm != 0 {
            let p = plus[rng.usize(np)]; let q = minus[rng.usize(nm)];
            s.swap(k, p, q);
            if !require_parity0 || s.parity_bad() == 0 { return; }
            s.swap(k, p, q);
        }
    }
}

struct Shared {
    overall_e: AtomicI64,
    overall: Mutex<State>,
    fibre_e: Vec<AtomicI64>,
    fibres: Vec<Mutex<State>>,
    stop: AtomicBool,
    total_iters: Mutex<u64>,
    rows: [i32; 4],
    alts: [i32; 4],
    modulus: usize,
    require_parity0: bool,
    guide_parity0: bool,
    soft_parity0: bool,
    start: Instant,
}

fn publish(s: &State, fibre: usize, id: usize, shared: &Shared) {
    let z = if shared.modulus == 4 { Some(s.z4()) } else { None };
    let checked = independently_verified(s, shared.rows, shared.alts, z, shared.require_parity0);
    let valid_for_fibre = !shared.guide_parity0 || checked.parity_bad() == 0;
    let pool_score = if shared.soft_parity0 { checked.e + 256*checked.parity_bad() as i64 }
        else { checked.e };
    let mut fibre_improved = false;
    if valid_for_fibre {
        let mut seen = shared.fibre_e[fibre].load(Ordering::Relaxed);
        while pool_score < seen {
            match shared.fibre_e[fibre].compare_exchange_weak(seen, pool_score,
                    Ordering::SeqCst, Ordering::Relaxed) {
                Ok(_) => {
                    *shared.fibres[fibre].lock().unwrap() = checked.clone();
                    fibre_improved = true; break;
                },
                Err(x) => seen = x,
            }
        }
    }
    if (shared.guide_parity0 || shared.soft_parity0) && fibre_improved {
        let iters = *shared.total_iters.lock().unwrap();
        let body = json(&checked, shared.modulus, shared.rows, shared.alts,
            shared.start.elapsed().as_secs_f64(), iters, checked.e == 0, true);
        let live = if shared.soft_parity0 { "agent_bsd_soft6_live.json" }
            else { "agent_bsd_parityguide_live.json" };
        let _ = fs::write(live, body);
        if shared.soft_parity0 {
            let _ = fs::write(format!("agent_bsd_soft_pb{}_live.json", checked.parity_bad()),
                json(&checked, shared.modulus, shared.rows, shared.alts,
                    shared.start.elapsed().as_secs_f64(), iters, checked.e == 0, false));
        }
        eprintln!("agent_bsd guided pool_score={} energy={} l1={} parity_bad={} worker={} fibre={} z4={:?} elapsed_s={:.3}",
            pool_score, checked.e, checked.r.iter().map(|x|x.abs()).sum::<i32>(), checked.parity_bad(), id, fibre,
            checked.z4(), shared.start.elapsed().as_secs_f64());
    }
    let mut overall_seen = shared.overall_e.load(Ordering::Relaxed);
    while checked.e < overall_seen {
        match shared.overall_e.compare_exchange_weak(overall_seen, checked.e,
                Ordering::SeqCst, Ordering::Relaxed) {
            Ok(_) => {
                *shared.overall.lock().unwrap() = checked.clone();
                let iters = *shared.total_iters.lock().unwrap();
                let body = json(&checked, shared.modulus, shared.rows, shared.alts,
                    shared.start.elapsed().as_secs_f64(), iters, checked.e == 0,
                    shared.require_parity0);
                if !shared.guide_parity0 && !shared.soft_parity0 {
                    let live = if shared.require_parity0 { "agent_bsd_plus2_parity0_live.json" }
                        else { "agent_bsd_unrestricted_live.json" };
                    let _ = fs::write(live, body);
                    eprintln!("agent_bsd best energy={} l1={} worker={} fibre={} z4={:?} elapsed_s={:.3}",
                        checked.e, checked.r.iter().map(|x|x.abs()).sum::<i32>(), id, fibre,
                        checked.z4(), shared.start.elapsed().as_secs_f64());
                }
                if checked.e == 0 { shared.stop.store(true, Ordering::SeqCst); }
                break;
            },
            Err(x) => overall_seen = x,
        }
    }
}

fn worker(id: usize, fibre: usize, end: Instant, shared: Arc<Shared>) -> u64 {
    let epoch = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos() as u64;
    let mut rng = Rng(epoch ^ (id as u64 + 101).wrapping_mul(0x9e3779b97f4a7c15));
    let mut s = shared.fibres[fibre].lock().unwrap().clone();
    let target_z = if shared.modulus == 4 { Some(s.z4()) } else { None };
    let mut tabu = [[0u64; 84]; 4];
    let mut weights = [1i64; H];
    let kind = id & 3;
    let parity_penalty = if shared.guide_parity0 || shared.soft_parity0 {
        if shared.soft_parity0 { [128i64,256,384,512][id & 3] }
        else { let base = if kind == 2 { 2 } else { 8 }; base << ((id / 4) % 3) }
    } else { 0 };
    let mut iter = 0u64;
    let mut stale = 0u64;
    let mut local_best = objective(&s, &weights, kind, parity_penalty);
    for _ in 0..id % 7 { random_swap(&mut s, &mut rng, shared.modulus, shared.require_parity0); }

    while Instant::now() < end && !shared.stop.load(Ordering::Relaxed) {
        let mut pick: Option<(i64, i64, usize, usize, usize)> = None;
        let mut ties = 0usize;
        let aspiration = shared.overall_e.load(Ordering::Relaxed);
        for k in 0..4 {
            for c in 0..shared.modulus {
                let mut plus = [0usize; 84]; let mut np = 0;
                let mut minus = [0usize; 84]; let mut nm = 0;
                for p in (c..L[k]).step_by(shared.modulus) {
                    if s.a[k][p] == 1 { plus[np] = p; np += 1; }
                    else { minus[nm] = p; nm += 1; }
                }
                for &p in &plus[..np] { for &q in &minus[..nm] {
                    s.swap(k, p, q);
                    let e2 = s.e;
                    let exact_ok = !shared.require_parity0 || s.parity_bad() == 0;
                    let allowed = exact_ok && (e2 < aspiration ||
                        (tabu[k][p] <= iter && tabu[k][q] <= iter));
                    if allowed {
                        let score = objective(&s, &weights, kind, parity_penalty);
                        let better = match pick {
                            None => true,
                            Some((bs, be, _, _, _)) => score < bs || (score == bs && e2 < be),
                        };
                        if better {
                            pick = Some((score, e2, k, p, q)); ties = 1;
                        } else if let Some((bs, be, _, _, _)) = pick {
                            if score == bs && e2 == be {
                                ties += 1;
                                if rng.usize(ties) == 0 { pick = Some((score, e2, k, p, q)); }
                            }
                        }
                    }
                    s.swap(k, p, q);
                }}
            }
        }
        let (_, _, k, p, q) = match pick {
            Some(x) => x,
            None => { tabu = [[0u64;84];4]; continue; },
        };
        s.swap(k, p, q);
        iter += 1; stale += 1;
        let tenure = 5 + rng.usize(18) as u64 + (stale / 1000).min(30);
        tabu[k][p] = iter + tenure; tabu[k][q] = iter + tenure;

        let current_metric = objective(&s, &weights, kind, parity_penalty);
        let pool_score = if shared.soft_parity0 { s.e+256*s.parity_bad() as i64 } else { s.e };
        let guide_valid_improvement = ((shared.guide_parity0 && s.parity_bad() == 0) || shared.soft_parity0) &&
            pool_score < shared.fibre_e[fibre].load(Ordering::Relaxed);
        if current_metric < local_best || guide_valid_improvement {
            if current_metric < local_best { local_best = current_metric; stale = 0; }
            publish(&s, fibre, id, &shared);
        }
        if s.e == 0 {
            publish(&s, fibre, id, &shared); break;
        }
        if kind != 0 && stale != 0 && stale % 1200 == 0 {
            for d in 0..H {
                if s.r[d] != 0 { weights[d] = (weights[d] + 1 + (s.r[d].abs()/4) as i64).min(96); }
            }
        }
        if stale > 5000 {
            s = shared.fibres[fibre].lock().unwrap().clone();
            for _ in 0..(4 + rng.usize(24)) {
                random_swap(&mut s, &mut rng, shared.modulus, shared.require_parity0);
            }
            tabu = [[0u64;84];4];
            if kind == 0 || rng.usize(3) == 0 { weights = [1i64;H]; }
            local_best = objective(&s, &weights, kind, parity_penalty); stale = 0;
        }
        if iter & 2047 == 0 {
            let check = independently_verified(&s, shared.rows, shared.alts, target_z,
                shared.require_parity0);
            assert_eq!(check.e, s.e, "incremental energy drift");
            assert_eq!(check.r, s.r, "incremental residual drift");
            *shared.total_iters.lock().unwrap() += 2048;
        }
    }
    iter
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let secs = args.get(1).and_then(|x| x.parse().ok()).unwrap_or(600u64);
    let threads = args.get(2).and_then(|x| x.parse().ok()).unwrap_or(4usize);
    let path = args.get(3).map(String::as_str).unwrap_or("bs_84_83_tabu_live.json");
    let modulus = args.get(4).and_then(|x| x.parse().ok()).unwrap_or(4usize);
    let search_mode = args.get(5).map(String::as_str).unwrap_or("");
    let require_parity0 = search_mode == "parity0";
    let guide_parity0 = search_mode == "guide";
    let soft_parity0 = search_mode == "soft";
    assert!(modulus == 2 || modulus == 4);
    let base = parse(path).expect("checkpoint containing sequences required");
    let rows = base.rows(); let alts = base.alts();
    assert_eq!(norm4(rows), 334); assert_eq!(norm4(alts), 334);
    let seeds = if modulus == 4 { quartic_seeds(&base, require_parity0 || guide_parity0) }
        else { vec![base.clone()] };
    assert!(!seeds.is_empty(), "no norm-334 quartic seed in one-swap shell");
    eprintln!("agent_bsd seed={} energy={} rows={:?} alts={:?} base_z4={:?} fibres={}",
        path, base.e, rows, alts, base.z4(), seeds.len());
    for (i,s) in seeds.iter().enumerate() {
        eprintln!("  fibre={} energy={} l1={} z4={:?}", i, s.e,
            s.r.iter().map(|x|x.abs()).sum::<i32>(), s.z4());
        independently_verified(s, rows, alts, if modulus==4 {Some(s.z4())} else {None},
            require_parity0 || guide_parity0);
    }
    let best_seed = seeds.iter().min_by_key(|s| s.e).unwrap().clone();
    let start = Instant::now(); let end = start + Duration::from_secs(secs);
    let shared = Arc::new(Shared {
        overall_e: AtomicI64::new(best_seed.e), overall: Mutex::new(best_seed),
        fibre_e: seeds.iter().map(|s| AtomicI64::new(if soft_parity0 {
            s.e+256*s.parity_bad() as i64
        } else {s.e})).collect(),
        fibres: seeds.iter().cloned().map(Mutex::new).collect(),
        stop: AtomicBool::new(false), total_iters: Mutex::new(0),
        rows, alts, modulus, require_parity0, guide_parity0, soft_parity0, start,
    });
    let mut handles = vec![];
    for id in 0..threads {
        let sh = shared.clone(); let fibre = id % seeds.len();
        handles.push(thread::spawn(move || worker(id, fibre, end, sh)));
    }
    let iterations: u64 = handles.into_iter().map(|h| h.join().unwrap()).sum();
    let ans = if guide_parity0 || soft_parity0 {
        shared.fibres.iter().map(|x| x.lock().unwrap().clone())
            .min_by_key(|s| if soft_parity0{s.e+256*s.parity_bad()as i64}else{s.e}).unwrap()
    } else { shared.overall.lock().unwrap().clone() };
    let checked = independently_verified(&ans, rows, alts,
        if modulus==4 {Some(ans.z4())} else {None}, require_parity0);
    let solved = checked.e == 0;
    if guide_parity0 { assert_eq!(checked.parity_bad(), 0); }
    let out = if solved { "agent_bsd_candidate.json" } else if require_parity0 {
        "agent_bsd_plus2_parity0_summary.json"
    } else if guide_parity0 { "agent_bsd_parityguide_summary.json" }
    else if soft_parity0 { "agent_bsd_soft6_summary.json" }
    else { "agent_bsd_unrestricted_summary.json" };
    fs::write(out, json(&checked, modulus, rows, alts, start.elapsed().as_secs_f64(),
        iterations, solved, require_parity0 || guide_parity0)).unwrap();
    println!("agent_bsd result solved={} energy={} l1={} modulus={} fibres={} iterations={} output={}",
        solved, checked.e, checked.r.iter().map(|x|x.abs()).sum::<i32>(), modulus,
        seeds.len(), iterations, out);
}
