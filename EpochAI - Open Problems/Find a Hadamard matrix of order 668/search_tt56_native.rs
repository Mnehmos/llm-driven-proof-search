//! Parallel unrestricted stochastic search for Turyn-type sequences TT(56).
//!
//! Unlike the earlier fixed-row-sum search, this program permits single-bit
//! flips, so a trajectory can move between every admissible row-sum class.
//! It accepts a result only when all 55 integer autocorrelation residuals are
//! exactly zero.

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
        let w = WEIGHTS[k];
        for shift in 1..56 {
            let mut neighbours = 0i32;
            if p + shift < n { neighbours += self.seq[k][p + shift] as i32; }
            if p >= shift { neighbours += self.seq[k][p - shift] as i32; }
            let delta = -2 * w * old * neighbours;
            let index = shift - 1;
            let before = self.residual[index] as i64;
            let after = before + delta as i64;
            self.energy += after * after - before * before;
            self.residual[index] += delta;
        }
        self.seq[k][p] = -self.seq[k][p];
    }

    fn row_sums(&self) -> [i32; 4] {
        let mut result = [0; 4];
        for (k, seq) in self.seq.iter().enumerate() {
            result[k] = seq.iter().map(|&x| x as i32).sum();
        }
        result
    }

    fn weighted_energy(&self, weights: &[i64; 55]) -> i64 {
        let base: i64 = self.residual.iter().zip(weights).map(|(&x, &w)| w * (x as i64) * (x as i64)).sum();
        let total: i64 = self.residual.iter().map(|&x| x as i64).sum();
        base + total * total / 4
    }

    fn weighted_l1(&self, weights: &[i64; 55]) -> i64 {
        let base: i64 = self.residual.iter().zip(weights).map(|(&x, &w)| w * x.abs() as i64).sum();
        let total: i64 = self.residual.iter().map(|&x| x as i64).sum();
        base + 2 * total.abs()
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
    fn unit(&mut self) -> f64 { ((self.next() >> 11) as f64) * (1.0 / ((1u64 << 53) as f64)) }
}

fn flat_position(mut p: usize) -> (usize, usize) {
    for (k, &n) in LENGTHS.iter().enumerate() {
        if p < n { return (k, p); }
        p -= n;
    }
    unreachable!()
}

fn parse_seed(path: &str) -> Option<Vec<Vec<i8>>> {
    let text = fs::read_to_string(path).ok()?;
    let start = text.find("\"sequences\"")?;
    let mut values = Vec::with_capacity(TOTAL);
    let bytes = text[start..].as_bytes();
    let mut i = 0;
    while i < bytes.len() && values.len() < TOTAL {
        if bytes[i] == b'-' && i + 1 < bytes.len() && bytes[i + 1] == b'1' {
            values.push(-1i8); i += 2;
        } else if bytes[i] == b'1' {
            values.push(1i8); i += 1;
        } else { i += 1; }
    }
    if values.len() != TOTAL { return None; }
    let mut seq = Vec::new();
    let mut offset = 0;
    for &n in &LENGTHS {
        seq.push(values[offset..offset + n].to_vec());
        offset += n;
    }
    Some(seq)
}

fn random_state(rng: &mut Rng) -> State {
    let seq = LENGTHS.iter().map(|&n| (0..n).map(|_| if rng.next() & 1 == 0 { 1 } else { -1 }).collect()).collect();
    State::new(seq)
}

fn update_best(state: &State, worker: usize, started: Instant, best_energy: &AtomicI64, best: &Mutex<State>) {
    let mut seen = best_energy.load(Ordering::Relaxed);
    while state.energy < seen {
        match best_energy.compare_exchange_weak(seen, state.energy, Ordering::SeqCst, Ordering::Relaxed) {
            Ok(_) => {
                *best.lock().unwrap() = state.clone();
                let _ = fs::write(
                    "Find a Hadamard matrix of order 668/tt56_live.json",
                    json_state(state, false, started.elapsed(), 0, 0),
                );
                eprintln!("best energy={} worker={} elapsed_s={:.3} rows={:?}", state.energy, worker, started.elapsed().as_secs_f64(), state.row_sums());
                return;
            }
            Err(actual) => seen = actual,
        }
    }
}

fn worker(
    id: usize,
    deadline: Instant,
    started: Instant,
    seed_state: State,
    best_energy: Arc<AtomicI64>,
    best: Arc<Mutex<State>>,
    solved: Arc<AtomicBool>,
) -> u64 {
    let epoch = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos() as u64;
    let mut rng = Rng::new(epoch ^ (id as u64 + 1).wrapping_mul(0x9e3779b97f4a7c15));
    let mut moves = 0u64;
    let mut restart = 0usize;
    while Instant::now() < deadline && !solved.load(Ordering::Relaxed) {
        let global = best.lock().unwrap().clone();
        let mut state = if restart % 7 == 6 { random_state(&mut rng) } else if restart == 0 { seed_state.clone() } else { global };
        let kick = if restart == 0 { id * 2 } else { 4 + rng.usize(40) };
        for _ in 0..kick {
            let (k, p) = flat_position(rng.usize(TOTAL));
            state.flip(k, p);
        }

        let cycle = 250_000usize;
        let mut stale = 0usize;
        let mut local_best = state.energy;
        let mut constraint_weights = [1i64; 55];
        for step in 0..cycle {
            if step & 8191 == 0 && (Instant::now() >= deadline || solved.load(Ordering::Relaxed)) { break; }
            let phase = (step as f64) / (cycle as f64);
            let temperature = if id % 3 == 0 {
                900.0 * (0.002f64).powf(phase) + 0.2
            } else if id % 3 == 1 {
                280.0 * (0.0005f64).powf(phase) + 0.05
            } else {
                90.0 * (0.0002f64).powf(phase) + 0.02
            };
            let roll = rng.usize(1000);
            let count = if roll < 650 { 1 } else if roll < 920 { 2 } else if roll < 990 { 3 } else { 4 + rng.usize(5) };
            let use_l1 = id % 4 == 2;
            let before_score = if use_l1 { state.weighted_l1(&constraint_weights) } else { state.weighted_energy(&constraint_weights) };
            let mut chosen = [(0usize, 0usize); 8];
            if id % 4 == 3 && count == 1 && roll % 5 == 0 {
                // Sample a small neighbourhood and take its best single flip.
                // This gives one quarter of the workers a min-conflicts bias.
                let mut best_pos = flat_position(rng.usize(TOTAL));
                let mut best_score = i64::MAX;
                for _ in 0..32 {
                    let pos = flat_position(rng.usize(TOTAL));
                    state.flip(pos.0, pos.1);
                    let score = if use_l1 { state.weighted_l1(&constraint_weights) } else { state.weighted_energy(&constraint_weights) };
                    state.flip(pos.0, pos.1);
                    if score < best_score { best_score = score; best_pos = pos; }
                }
                chosen[0] = best_pos;
                state.flip(best_pos.0, best_pos.1);
            } else {
                for slot in chosen.iter_mut().take(count) {
                    *slot = flat_position(rng.usize(TOTAL));
                    state.flip(slot.0, slot.1);
                }
            }
            moves += 1;
            let after_score = if use_l1 { state.weighted_l1(&constraint_weights) } else { state.weighted_energy(&constraint_weights) };
            let delta = after_score - before_score;
            let accept = delta <= 0 || rng.unit() < (-(delta as f64) / temperature).exp();
            if !accept {
                for &(k, p) in chosen[..count].iter().rev() { state.flip(k, p); }
            } else if state.energy < local_best {
                local_best = state.energy;
                stale = 0;
                update_best(&state, id, started, &best_energy, &best);
                if state.energy == 0 {
                    let mut check = state.clone(); check.recompute();
                    if check.energy == 0 {
                        *best.lock().unwrap() = check;
                        solved.store(true, Ordering::SeqCst);
                        break;
                    }
                }
            } else {
                stale += 1;
            }

            // A strong kick prevents long residence in a low-temperature basin.
            if id % 2 == 1 && stale > 40_000 {
                // Breakout weighting: emphasize every still-violated lag, forcing
                // the trajectory to leave a basin that ignores sparse equations.
                for j in 0..55 {
                    if state.residual[j] != 0 {
                        constraint_weights[j] = (constraint_weights[j] + 1 + (state.residual[j].abs() as i64 / 4)).min(64);
                    }
                }
                stale = 0;
            } else if stale > 80_000 {
                for _ in 0..(8 + rng.usize(24)) {
                    let (k, p) = flat_position(rng.usize(TOTAL)); state.flip(k, p);
                }
                stale = 0;
            }
        }
        restart += 1;
    }
    moves
}

fn json_state(state: &State, solved: bool, elapsed: Duration, moves: u64, threads: usize) -> String {
    let sequences = state.seq.iter().map(|s| format!("[{}]", s.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(","))).collect::<Vec<_>>().join(",\n    ");
    let residual = state.residual.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(",");
    format!(
        "{{\n  \"construction\": \"Turyn-type sequences TT(56)\",\n  \"solved\": {},\n  \"energy\": {},\n  \"elapsed_s\": {:.6},\n  \"moves\": {},\n  \"threads\": {},\n  \"row_sums\": {:?},\n  \"residual\": [{}],\n  \"sequences\": [\n    {}\n  ]\n}}\n",
        solved, state.energy, elapsed.as_secs_f64(), moves, threads, state.row_sums(), residual, sequences
    )
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let seconds: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(600);
    let threads: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(10);
    let seed_path = args.get(3).map(String::as_str).unwrap_or("Find a Hadamard matrix of order 668/turyn_type_56_search_summary.json");
    let seq = parse_seed(seed_path).expect("could not parse 223 seed signs from JSON");
    let seed_state = State::new(seq);
    eprintln!("seed energy={} rows={:?}", seed_state.energy, seed_state.row_sums());

    let started = Instant::now();
    let deadline = started + Duration::from_secs(seconds);
    let best_energy = Arc::new(AtomicI64::new(seed_state.energy));
    let best = Arc::new(Mutex::new(seed_state.clone()));
    let solved = Arc::new(AtomicBool::new(false));
    let mut handles = Vec::new();
    for id in 0..threads {
        let state = seed_state.clone();
        let be = best_energy.clone();
        let b = best.clone();
        let stop = solved.clone();
        handles.push(thread::spawn(move || worker(id, deadline, started, state, be, b, stop)));
    }
    let moves: u64 = handles.into_iter().map(|h| h.join().unwrap()).sum();
    let mut answer = best.lock().unwrap().clone();
    answer.recompute();
    let is_solved = answer.energy == 0;
    let output = json_state(&answer, is_solved, started.elapsed(), moves, threads);
    let path = if is_solved { "Find a Hadamard matrix of order 668/tt56_native_candidate.json" } else { "Find a Hadamard matrix of order 668/tt56_native_summary.json" };
    fs::write(path, output).expect("write search result");
    println!("result solved={} energy={} rows={:?} moves={} elapsed_s={:.3} output={}", is_solved, answer.energy, answer.row_sums(), moves, started.elapsed().as_secs_f64(), path);
}
