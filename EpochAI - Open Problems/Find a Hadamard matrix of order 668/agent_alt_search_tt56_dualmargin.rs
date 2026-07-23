//! TT(56) search inside simultaneous z=1 and z=-1 norm fibers.
//!
//! A genuine Turyn-type quadruple obeys
//!   a(1)^2+b(1)^2+2c(1)^2+2d(1)^2 = 334
//! and the same identity at z=-1.  The older fixed-row run enforced only the
//! first identity.  Here every move swaps opposite signs at positions of the
//! same parity, so both the ordinary and alternating row sums remain fixed.

use std::env;
use std::fs;
use std::sync::atomic::{AtomicBool, AtomicI64, Ordering};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

const LENGTHS: [usize; 4] = [56, 56, 56, 55];
const WEIGHTS: [i32; 4] = [1, 1, 2, 2];
const TOTAL: usize = 223;

#[derive(Clone)]
struct State {
    seq: Vec<Vec<i8>>,
    residual: [i32; 55],
    energy: i64,
}

impl State {
    fn new(seq: Vec<Vec<i8>>) -> Self {
        let mut state = Self { seq, residual: [0; 55], energy: 0 };
        state.recompute();
        state
    }

    fn recompute(&mut self) {
        self.residual = [0; 55];
        for shift in 1..56 {
            let mut value = 0i32;
            for k in 0..4 {
                for i in 0..self.seq[k].len().saturating_sub(shift) {
                    value += WEIGHTS[k] * self.seq[k][i] as i32 * self.seq[k][i + shift] as i32;
                }
            }
            self.residual[shift - 1] = value;
        }
        self.energy = self.residual.iter().map(|&x| (x as i64) * (x as i64)).sum();
    }

    fn flip(&mut self, k: usize, p: usize) {
        let old = self.seq[k][p] as i32;
        let n = self.seq[k].len();
        let weight = WEIGHTS[k];
        for shift in 1..56 {
            let mut neighbours = 0i32;
            if p + shift < n { neighbours += self.seq[k][p + shift] as i32; }
            if p >= shift { neighbours += self.seq[k][p - shift] as i32; }
            let delta = -2 * weight * old * neighbours;
            let j = shift - 1;
            let before = self.residual[j] as i64;
            let after = before + delta as i64;
            self.energy += after * after - before * before;
            self.residual[j] += delta;
        }
        self.seq[k][p] = -self.seq[k][p];
    }

    fn rows(&self) -> [i32; 4] {
        let mut out = [0; 4];
        for k in 0..4 { out[k] = self.seq[k].iter().map(|&x| x as i32).sum(); }
        out
    }

    fn alternating_rows(&self) -> [i32; 4] {
        let mut out = [0; 4];
        for k in 0..4 {
            out[k] = self.seq[k].iter().enumerate()
                .map(|(i, &x)| if i & 1 == 0 { x as i32 } else { -(x as i32) }).sum();
        }
        out
    }
}

#[derive(Clone, Copy)]
struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(if seed == 0 { 0x9e3779b97f4a7c15 } else { seed }) }
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }
    fn usize(&mut self, n: usize) -> usize { (self.next() as usize) % n }
    fn unit(&mut self) -> f64 { ((self.next() >> 11) as f64) / ((1u64 << 53) as f64) }
}

fn parse_seed(path: &str) -> Vec<Vec<i8>> {
    let text = fs::read_to_string(path).expect("seed file");
    let start = text.find("\"sequences\"").expect("sequences key");
    let bytes = text[start..].as_bytes();
    let mut values = Vec::with_capacity(TOTAL);
    let mut i = 0;
    while i < bytes.len() && values.len() < TOTAL {
        if bytes[i] == b'-' && i + 1 < bytes.len() && bytes[i + 1] == b'1' {
            values.push(-1); i += 2;
        } else if bytes[i] == b'1' {
            values.push(1); i += 1;
        } else { i += 1; }
    }
    assert_eq!(values.len(), TOTAL);
    let mut out = Vec::new();
    let mut offset = 0;
    for &n in &LENGTHS { out.push(values[offset..offset + n].to_vec()); offset += n; }
    out
}

fn norm(rows: [i32; 4]) -> i32 {
    rows[0] * rows[0] + rows[1] * rows[1] + 2 * rows[2] * rows[2] + 2 * rows[3] * rows[3]
}

fn target_alt_rows(rows: [i32; 4], current: [i32; 4]) -> Vec<[i32; 4]> {
    let mut out = Vec::new();
    for a in (-56..=56).step_by(2) {
        for b in (-56..=56).step_by(2) {
            for c in (-56..=56).step_by(2) {
                for d in (-55..=55).step_by(2) {
                    let target = [a, b, c, d];
                    if norm(target) != 334 { continue; }
                    let mut ok = true;
                    for k in 0..4 {
                        let even_n = (LENGTHS[k] + 1) / 2;
                        let odd_n = LENGTHS[k] / 2;
                        if (rows[k] + target[k]) % 2 != 0 || (rows[k] - target[k]) % 2 != 0 { ok = false; break; }
                        let even_sum = (rows[k] + target[k]) / 2;
                        let odd_sum = (rows[k] - target[k]) / 2;
                        if even_sum.abs() > even_n as i32 || odd_sum.abs() > odd_n as i32 ||
                           (even_sum - even_n as i32) % 2 != 0 || (odd_sum - odd_n as i32) % 2 != 0 {
                            ok = false; break;
                        }
                    }
                    if ok { out.push(target); }
                }
            }
        }
    }
    out.sort_by_key(|t| (0..4).map(|k| (t[k] - current[k]).abs() / 4).sum::<i32>());
    out
}

fn project(mut state: State, target: [i32; 4]) -> State {
    for k in 0..4 {
        loop {
            let now = state.alternating_rows()[k];
            if now == target[k] { break; }
            let decrease = now > target[k];
            let mut best: Option<(i64, usize, usize)> = None;
            for p in 0..LENGTHS[k] {
                for q in (p + 1)..LENGTHS[k] {
                    if (p & 1) == (q & 1) || state.seq[k][p] == state.seq[k][q] { continue; }
                    let delta = if p & 1 == 0 {
                        -2 * state.seq[k][p] as i32 + 2 * state.seq[k][q] as i32
                    } else {
                        2 * state.seq[k][p] as i32 - 2 * state.seq[k][q] as i32
                    };
                    if (decrease && delta != -4) || (!decrease && delta != 4) { continue; }
                    state.flip(k, p); state.flip(k, q);
                    let e = state.energy;
                    state.flip(k, q); state.flip(k, p);
                    if best.map_or(true, |x| e < x.0) { best = Some((e, p, q)); }
                }
            }
            let (_, p, q) = best.expect("feasible parity projection");
            state.flip(k, p); state.flip(k, q);
        }
    }
    assert_eq!(state.alternating_rows(), target);
    state
}

fn same_parity_swap(state: &State, rng: &mut Rng) -> (usize, usize, usize) {
    loop {
        let k = rng.usize(4);
        let parity = rng.usize(2);
        let positions: Vec<usize> = (parity..LENGTHS[k]).step_by(2).collect();
        let p = positions[rng.usize(positions.len())];
        let q = positions[rng.usize(positions.len())];
        if p != q && state.seq[k][p] != state.seq[k][q] { return (k, p, q); }
    }
}

fn json_state(state: &State, elapsed: Duration, solved: bool, moves: u64) -> String {
    let seqs = state.seq.iter().map(|s| format!("[{}]", s.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(","))).collect::<Vec<_>>().join(",\n    ");
    format!(
        "{{\n  \"construction\": \"TT(56), simultaneous z=1/z=-1 margins\",\n  \"solved\": {},\n  \"energy\": {},\n  \"elapsed_s\": {:.6},\n  \"moves\": {},\n  \"row_sums\": {:?},\n  \"alternating_row_sums\": {:?},\n  \"residual\": {:?},\n  \"sequences\": [\n    {}\n  ]\n}}\n",
        solved, state.energy, elapsed.as_secs_f64(), moves, state.rows(), state.alternating_rows(), state.residual, seqs
    )
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let seed_path = args.get(1).map(String::as_str).unwrap_or("turyn_type_56_search_summary.json");
    let seconds: u64 = args.get(2).and_then(|x| x.parse().ok()).unwrap_or(300);
    let workers: usize = args.get(3).and_then(|x| x.parse().ok()).unwrap_or(2);
    let base = State::new(parse_seed(seed_path));
    assert_eq!(norm(base.rows()), 334, "seed must satisfy z=1 norm");
    let targets = Arc::new(target_alt_rows(base.rows(), base.alternating_rows()));
    eprintln!("base energy={} rows={:?} alt={:?} alt_norm={} targets={}", base.energy, base.rows(), base.alternating_rows(), norm(base.alternating_rows()), targets.len());

    let started = Instant::now();
    let deadline = started + Duration::from_secs(seconds);
    let solved = Arc::new(AtomicBool::new(false));
    let best_energy = Arc::new(AtomicI64::new(i64::MAX));
    let best_state = Arc::new(Mutex::new(base.clone()));
    let move_count = Arc::new(Mutex::new(0u64));
    let mut handles = Vec::new();

    for id in 0..workers {
        let base = base.clone();
        let targets = targets.clone();
        let solved = solved.clone();
        let best_energy = best_energy.clone();
        let best_state = best_state.clone();
        let move_count = move_count.clone();
        handles.push(thread::spawn(move || {
            let epoch = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos() as u64;
            let mut rng = Rng::new(epoch ^ ((id as u64 + 1) * 0x517cc1b727220a95));
            let mut local_moves = 0u64;
            let mut restart = 0usize;
            while Instant::now() < deadline && !solved.load(Ordering::Relaxed) {
                let target = targets[(id + restart * workers) % targets.len()];
                let mut state = project(base.clone(), target);
                for _ in 0..(restart % 24) {
                    let (k, p, q) = same_parity_swap(&state, &mut rng);
                    state.flip(k, p); state.flip(k, q);
                }
                let cycle = 400_000usize;
                for step in 0..cycle {
                    if step & 8191 == 0 && (Instant::now() >= deadline || solved.load(Ordering::Relaxed)) { break; }
                    let phase = step as f64 / cycle as f64;
                    let temperature = (if id & 1 == 0 { 220.0 } else { 80.0 }) * (0.0005f64).powf(phase) + 0.02;
                    let before = state.energy;
                    let count = if rng.usize(100) < 88 { 1 } else { 2 };
                    let mut changes = Vec::new();
                    for _ in 0..count {
                        let (k, p, q) = same_parity_swap(&state, &mut rng);
                        state.flip(k, p); state.flip(k, q); changes.push((k, p, q));
                    }
                    local_moves += 1;
                    let delta = state.energy - before;
                    if delta > 0 && rng.unit() >= (-(delta as f64) / temperature).exp() {
                        for &(k, p, q) in changes.iter().rev() { state.flip(k, q); state.flip(k, p); }
                    } else if state.energy < best_energy.load(Ordering::Relaxed) {
                        let mut seen = best_energy.load(Ordering::Relaxed);
                        while state.energy < seen {
                            match best_energy.compare_exchange_weak(seen, state.energy, Ordering::SeqCst, Ordering::Relaxed) {
                                Ok(_) => {
                                    let mut check = state.clone(); check.recompute();
                                    assert_eq!(check.energy, state.energy);
                                    assert_eq!(norm(check.rows()), 334);
                                    assert_eq!(norm(check.alternating_rows()), 334);
                                    *best_state.lock().unwrap() = check.clone();
                                    let _ = fs::write("agent_alt_tt56_dualmargin_live.json", json_state(&check, started.elapsed(), check.energy == 0, local_moves));
                                    eprintln!("best={} worker={} rows={:?} alt={:?} elapsed={:.1}", check.energy, id, check.rows(), check.alternating_rows(), started.elapsed().as_secs_f64());
                                    if check.energy == 0 { solved.store(true, Ordering::SeqCst); }
                                    break;
                                }
                                Err(actual) => seen = actual,
                            }
                        }
                    }
                }
                restart += 1;
            }
            *move_count.lock().unwrap() += local_moves;
        }));
    }
    for h in handles { h.join().unwrap(); }
    let mut best = best_state.lock().unwrap().clone(); best.recompute();
    let is_solved = best.energy == 0;
    let output = if is_solved { "agent_alt_tt56_candidate.json" } else { "agent_alt_tt56_dualmargin_summary.json" };
    fs::write(output, json_state(&best, started.elapsed(), is_solved, *move_count.lock().unwrap())).unwrap();
    println!("output={} solved={} energy={} rows={:?} alt={:?}", output, is_solved, best.energy, best.rows(), best.alternating_rows());
}
