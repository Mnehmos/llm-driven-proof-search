//! Periodic complementary search in the disjoint T-sequence subspace of Z_167.
//!
//! Each coordinate stores one of eight signed Walsh symbols (type 0..3 and
//! sign +/-).  The four Walsh transforms A,B,C,D are binary.  For every shift
//! d, their combined periodic autocorrelation is four times the combined
//! periodic autocorrelation of the four disjoint ternary T-sequences.  Thus a
//! zero residual here is an exact cyclic Goethals-Seidel input for H(668).
//!
//! Moves permute symbols among coordinates.  They preserve all four binary row
//! sums, including the necessary sum-of-four-squares identity, exactly.

use std::env;
use std::fs;
use std::io::{self, Read};
use std::sync::atomic::{AtomicBool, AtomicI64, Ordering};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

const N: usize = 167;
const HALF: usize = 83;
const PATS: [[i32; 4]; 4] = [
    [1, 1, 1, 1], [1, 1, -1, -1], [1, -1, 1, -1], [1, -1, -1, 1],
];

#[derive(Clone)]
struct State {
    symbols: [u8; N],
    residual: [i16; HALF],
    energy: i64,
}

fn sign(symbol: u8) -> i16 { if symbol & 1 == 0 { -1 } else { 1 } }
fn kind(symbol: u8) -> u8 { symbol >> 1 }
fn contribution(a: u8, b: u8) -> i16 {
    if kind(a) == kind(b) { sign(a) * sign(b) } else { 0 }
}

impl State {
    fn new(symbols: [u8; N]) -> Self {
        let mut s = Self { symbols, residual: [0; HALF], energy: 0 };
        s.recompute();
        s
    }

    fn recompute(&mut self) {
        self.residual = [0; HALF];
        for d in 1..=HALF {
            self.residual[d - 1] = (0..N)
                .map(|i| contribution(self.symbols[i], self.symbols[(i + d) % N]))
                .sum();
        }
        self.energy = self.residual.iter().map(|&x| (x as i64) * (x as i64)).sum();
    }

    fn binary_rows(&self) -> [i32; 4] {
        let mut rows = [0; 4];
        for &symbol in &self.symbols {
            let s = sign(symbol) as i32;
            for j in 0..4 { rows[j] += s * PATS[kind(symbol) as usize][j]; }
        }
        rows
    }

    fn l1(&self) -> i64 { self.residual.iter().map(|x| x.abs() as i64).sum() }
    fn parity_bad(&self) -> i64 { self.residual.iter().filter(|x| *x & 1 != 0).count() as i64 }
    fn breakout_score(&self) -> i64 { 4 * self.l1() + 8 * self.parity_bad() }

    fn replace(&mut self, positions: &[usize], new: &[u8]) {
        let old: Vec<u8> = positions.iter().map(|&p| self.symbols[p]).collect();
        assert_eq!(positions.len(), new.len());
        let mut delta = [0i16; HALF];

        for (slot, &p) in positions.iter().enumerate() {
            for q in 0..N {
                if q == p { continue; }
                if let Some(other_slot) = positions.iter().position(|&x| x == q) {
                    if slot >= other_slot { continue; }
                    let raw = p.abs_diff(q);
                    let d = raw.min(N - raw);
                    delta[d - 1] += contribution(new[slot], new[other_slot])
                        - contribution(old[slot], old[other_slot]);
                } else {
                    let raw = p.abs_diff(q);
                    let d = raw.min(N - raw);
                    delta[d - 1] += contribution(new[slot], self.symbols[q])
                        - contribution(old[slot], self.symbols[q]);
                }
            }
        }

        for d in 0..HALF {
            let before = self.residual[d] as i64;
            let after = before + delta[d] as i64;
            self.energy += after * after - before * before;
            self.residual[d] += delta[d];
        }
        for (slot, &p) in positions.iter().enumerate() { self.symbols[p] = new[slot]; }
    }

    fn permute(&mut self, positions: &[usize], permutation: &[usize]) {
        let old: Vec<u8> = positions.iter().map(|&p| self.symbols[p]).collect();
        let new: Vec<u8> = permutation.iter().map(|&j| old[j]).collect();
        self.replace(positions, &new);
    }
}

#[derive(Clone, Copy)]
struct Rng(u64);
impl Rng {
    fn new(x: u64) -> Self { Self(if x == 0 { 0x9e3779b97f4a7c15 } else { x }) }
    fn next(&mut self) -> u64 { let mut x = self.0; x ^= x << 13; x ^= x >> 7; x ^= x << 17; self.0 = x; x }
    fn usize(&mut self, n: usize) -> usize { self.next() as usize % n }
    fn unit(&mut self) -> f64 { ((self.next() >> 11) as f64) / ((1u64 << 53) as f64) }
}

fn parse_array(text: &str, key: &str, count: usize) -> Vec<i32> {
    let start = text.find(key).expect("JSON key");
    let bytes = text[start..].as_bytes();
    let mut out = Vec::with_capacity(count);
    let mut i = bytes.iter().position(|&x| x == b'[').expect("array") + 1;
    while i < bytes.len() && out.len() < count {
        if bytes[i] == b'-' && i + 1 < bytes.len() && bytes[i + 1].is_ascii_digit() {
            out.push(-((bytes[i + 1] - b'0') as i32)); i += 2;
        } else if bytes[i].is_ascii_digit() {
            out.push((bytes[i] - b'0') as i32); i += 1;
        } else { i += 1; }
    }
    assert_eq!(out.len(), count);
    out
}

fn parse_seed(path: &str) -> [u8; N] {
    let mut text = String::new();
    if path == "-" { io::stdin().read_to_string(&mut text).unwrap(); }
    else { text = fs::read_to_string(path).expect("seed file"); }
    let types = parse_array(&text, "\"types\"", N);
    let signs = parse_array(&text, "\"signs\"", N);
    let mut symbols = [0u8; N];
    for i in 0..N { symbols[i] = (2 * types[i] + if signs[i] > 0 { 1 } else { 0 }) as u8; }
    symbols
}

fn random_move(state: &State, rng: &mut Rng, width: usize) -> (Vec<usize>, Vec<usize>) {
    let mut positions = Vec::with_capacity(width);
    while positions.len() < width {
        let p = rng.usize(N);
        if !positions.contains(&p) { positions.push(p); }
    }
    let mut perm: Vec<usize> = (0..width).collect();
    for i in (1..width).rev() { let j = rng.usize(i + 1); perm.swap(i, j); }
    if perm.iter().enumerate().all(|(i, &j)| i == j) { perm.rotate_left(1); }
    if positions.iter().enumerate().all(|(i, &p)| state.symbols[p] == state.symbols[positions[perm[i]]]) {
        perm.rotate_left(1);
    }
    (positions, perm)
}

fn random_neutral_pair(state: &State, rng: &mut Rng) -> (Vec<usize>, Vec<u8>) {
    loop {
        let p = rng.usize(N);
        let q = rng.usize(N);
        if p == q || kind(state.symbols[p]) != kind(state.symbols[q]) || sign(state.symbols[p]) == sign(state.symbols[q]) { continue; }
        let old_kind = kind(state.symbols[p]) as usize;
        let mut new_kind = rng.usize(4);
        while new_kind == old_kind { new_kind = rng.usize(4); }
        let first_positive = rng.next() & 1 != 0;
        let a = (2 * new_kind + if first_positive { 1 } else { 0 }) as u8;
        return (vec![p, q], vec![a, a ^ 1]);
    }
}

fn json_state(state: &State, elapsed: Duration, moves: u64, solved: bool) -> String {
    let types = state.symbols.iter().map(|&x| kind(x).to_string()).collect::<Vec<_>>().join(",");
    let signs = state.symbols.iter().map(|&x| sign(x).to_string()).collect::<Vec<_>>().join(",");
    let residual = state.residual.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(",");
    let sequences = (0..4).map(|j| {
        let row = state.symbols.iter().map(|&x| {
            ((sign(x) as i32) * PATS[kind(x) as usize][j]).to_string()
        }).collect::<Vec<_>>().join(",");
        format!("[{}]", row)
    }).collect::<Vec<_>>().join(",\n    ");
    format!(
        "{{\n  \"construction\": \"periodic disjoint T-sequences on Z_167\",\n  \"solved\": {},\n  \"energy\": {},\n  \"binary_paf_energy\": {},\n  \"elapsed_s\": {:.6},\n  \"moves\": {},\n  \"binary_row_sums\": {:?},\n  \"residual\": [{}],\n  \"types\": [{}],\n  \"signs\": [{}],\n  \"sequences\": [\n    {}\n  ]\n}}\n",
        solved, state.energy, 16 * state.energy, elapsed.as_secs_f64(), moves,
        state.binary_rows(), residual, types, signs, sequences
    )
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let seed_path = args.get(1).map(String::as_str).unwrap_or("-");
    let seconds: u64 = args.get(2).and_then(|x| x.parse().ok()).unwrap_or(300);
    let workers: usize = args.get(3).and_then(|x| x.parse().ok()).unwrap_or(2);
    let base = State::new(parse_seed(seed_path));
    let rows = base.binary_rows();
    assert_eq!(rows.iter().map(|x| x * x).sum::<i32>(), 668, "row-square gate");
    eprintln!("base periodic energy={} binary_paf_energy={} rows={:?} residual={:?}", base.energy, 16 * base.energy, rows, base.residual);

    let started = Instant::now();
    let deadline = started + Duration::from_secs(seconds);
    let best_energy = Arc::new(AtomicI64::new(base.energy));
    let best_state = Arc::new(Mutex::new(base.clone()));
    let solved = Arc::new(AtomicBool::new(false));
    let moves_total = Arc::new(Mutex::new(0u64));
    let mut handles = Vec::new();

    for id in 0..workers {
        let base = base.clone();
        let best_energy = best_energy.clone();
        let best_state = best_state.clone();
        let solved = solved.clone();
        let moves_total = moves_total.clone();
        handles.push(thread::spawn(move || {
            let epoch = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos() as u64;
            let mut rng = Rng::new(epoch ^ ((id as u64 + 1).wrapping_mul(0x517cc1b727220a95)));
            let mut local_moves = 0u64;
            let mut restart = 0usize;
            while Instant::now() < deadline && !solved.load(Ordering::Relaxed) {
                let mut state = if restart == 0 { base.clone() } else { best_state.lock().unwrap().clone() };
                for _ in 0..(4 + restart % 24) {
                    let width = 3 + rng.usize(8);
                    let (p, q) = random_move(&state, &mut rng, width);
                    state.permute(&p, &q);
                }
                let cycle = 600_000usize;
                for step in 0..cycle {
                    if step & 4095 == 0 && (Instant::now() >= deadline || solved.load(Ordering::Relaxed)) { break; }
                    let phase = step as f64 / cycle as f64;
                    let temp0 = if id % 3 == 0 { 24.0 } else if id % 3 == 1 { 8.0 } else { 60.0 };
                    let temperature = temp0 * (0.0005f64).powf(phase) + 0.03;
                    let roll = rng.usize(1000);
                    let (positions, new_symbols) = if roll < 160 {
                        random_neutral_pair(&state, &mut rng)
                    } else {
                        let width = if roll < 600 { 2 } else if roll < 830 { 3 } else if roll < 950 { 4 + rng.usize(3) } else { 7 + rng.usize(10) };
                        let (positions, permutation) = random_move(&state, &mut rng, width);
                        let old: Vec<u8> = positions.iter().map(|&p| state.symbols[p]).collect();
                        let new_symbols = permutation.iter().map(|&j| old[j]).collect();
                        (positions, new_symbols)
                    };
                    let old_symbols: Vec<u8> = positions.iter().map(|&p| state.symbols[p]).collect();
                    let use_breakout = id & 1 == 1;
                    let before = if use_breakout { state.breakout_score() } else { state.energy };
                    state.replace(&positions, &new_symbols);
                    local_moves += 1;
                    let after = if use_breakout { state.breakout_score() } else { state.energy };
                    let delta = after - before;
                    if delta > 0 && rng.unit() >= (-(delta as f64) / temperature).exp() {
                        state.replace(&positions, &old_symbols);
                    } else if state.energy < best_energy.load(Ordering::Relaxed) {
                        let mut seen = best_energy.load(Ordering::Relaxed);
                        while state.energy < seen {
                            match best_energy.compare_exchange_weak(seen, state.energy, Ordering::SeqCst, Ordering::Relaxed) {
                                Ok(_) => {
                                    let mut check = state.clone(); check.recompute();
                                    assert_eq!(check.energy, state.energy);
                                    assert_eq!(check.binary_rows(), rows);
                                    *best_state.lock().unwrap() = check.clone();
                                    let _ = fs::write("agent_alt_t167_periodic_live.json", json_state(&check, started.elapsed(), local_moves, check.energy == 0));
                                    eprintln!("best={} binary={} worker={} elapsed={:.1}", check.energy, 16 * check.energy, id, started.elapsed().as_secs_f64());
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
            *moves_total.lock().unwrap() += local_moves;
        }));
    }
    for h in handles { h.join().unwrap(); }
    let mut best = best_state.lock().unwrap().clone(); best.recompute();
    let is_solved = best.energy == 0;
    let output = if is_solved { "agent_alt_t167_candidate.json" } else { "agent_alt_t167_periodic_summary.json" };
    fs::write(output, json_state(&best, started.elapsed(), *moves_total.lock().unwrap(), is_solved)).unwrap();
    println!("output={} solved={} energy={} binary_paf_energy={} rows={:?}", output, is_solved, best.energy, 16 * best.energy, best.binary_rows());
}
