//! Cross-fibre local search for BS(84,83), kept separate from the main search.
//!
//! A reversal-orbit move preserves the mod-four autocorrelation signature but
//! cannot change the antisymmetric signature of any row.  This solver adds
//! coupled four-bit moves.  In two rows it toggles the same two reversal
//! orbits, choosing opposite signs within each row.  Hence every row sum and
//! every autocorrelation modulo four remain fixed, while the individual row
//! signatures can change.  The two odd rows also admit a centre-coupled move.

use std::{env, fs, thread};
use std::sync::{Arc, Mutex};
use std::sync::atomic::{AtomicBool, AtomicI64, Ordering};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

const LENGTHS: [usize; 4] = [84, 84, 83, 83];
const SHIFTS: usize = 83;
const TARGET_ROWS: [i32; 4] = [14, -8, -7, -5];

#[derive(Clone)]
struct State {
    a: [Vec<i8>; 4],
    r: [i32; SHIFTS],
    energy: i64,
}

impl State {
    fn new(a: [Vec<i8>; 4]) -> Self {
        let mut state = Self { a, r: [0; SHIFTS], energy: 0 };
        state.recompute();
        state
    }

    fn recompute(&mut self) {
        self.r = [0; SHIFTS];
        for k in 0..4 {
            for d in 1..LENGTHS[k] {
                for i in 0..LENGTHS[k] - d {
                    self.r[d - 1] += self.a[k][i] as i32 * self.a[k][i + d] as i32;
                }
            }
        }
        self.energy = self.r.iter().map(|&x| (x as i64) * (x as i64)).sum();
    }

    fn flip(&mut self, k: usize, p: usize) {
        let old = self.a[k][p] as i32;
        let n = LENGTHS[k];
        for d in 1..n {
            let mut neighbor_sum = 0i32;
            if p + d < n { neighbor_sum += self.a[k][p + d] as i32; }
            if p >= d { neighbor_sum += self.a[k][p - d] as i32; }
            let delta = -2 * old * neighbor_sum;
            let before = self.r[d - 1] as i64;
            let after = before + delta as i64;
            self.energy += after * after - before * before;
            self.r[d - 1] += delta;
        }
        self.a[k][p] = -self.a[k][p];
    }

    fn rows(&self) -> [i32; 4] {
        std::array::from_fn(|k| self.a[k].iter().map(|&x| x as i32).sum())
    }

    fn parity_bad(&self) -> usize {
        self.r.iter().filter(|&&x| x.rem_euclid(4) != 0).count()
    }

    fn l1_quarters(&self) -> i64 {
        self.r.iter().map(|&x| (x / 4).abs() as i64).sum()
    }

    fn nonzero(&self) -> i64 {
        self.r.iter().filter(|&&x| x != 0).count() as i64
    }

    fn score(&self, weights: &[i64; SHIFTS], mode: usize) -> i64 {
        match mode {
            0 => self.r.iter().zip(weights).map(|(&x, &w)| {
                let q = (x / 4) as i64; w * q * q
            }).sum(),
            1 => self.r.iter().zip(weights).map(|(&x, &w)| {
                w * (x / 4).abs() as i64
            }).sum(),
            2 => {
                let e: i64 = self.r.iter().map(|&x| {
                    let q = (x / 4) as i64; q * q
                }).sum();
                e + 3 * self.nonzero()
            },
            _ => self.r.iter().zip(weights).map(|(&x, &w)| {
                let q = (x / 4) as i64;
                w * (q * q + 2 * q.abs())
            }).sum(),
        }
    }
}

#[derive(Clone, Copy)]
struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }
    fn usize(&mut self, n: usize) -> usize { self.next() as usize % n }
    fn unit(&mut self) -> f64 { (self.next() >> 11) as f64 / (1u64 << 53) as f64 }
}

#[derive(Clone, Copy)]
struct Move {
    positions: [(usize, usize); 16],
    len: usize,
}
impl Move {
    fn empty() -> Self { Self { positions: [(0, 0); 16], len: 0 } }
    fn push(&mut self, item: (usize, usize)) {
        assert!(self.len < self.positions.len());
        assert!(!self.positions[..self.len].contains(&item));
        self.positions[self.len] = item;
        self.len += 1;
    }
}

fn apply_move(state: &mut State, mv: &Move) {
    for &(k, p) in &mv.positions[..mv.len] { state.flip(k, p); }
}
fn undo_move(state: &mut State, mv: &Move) {
    for &(k, p) in mv.positions[..mv.len].iter().rev() { state.flip(k, p); }
}

fn choose_endpoint(state: &State, k: usize, orbit: usize, sign: i8, rng: &mut Rng) -> Option<usize> {
    let n = LENGTHS[k];
    let p = orbit;
    let q = n - 1 - orbit;
    let mut candidates = [0usize; 2];
    let mut count = 0;
    if state.a[k][p] == sign { candidates[count] = p; count += 1; }
    if state.a[k][q] == sign { candidates[count] = q; count += 1; }
    if count == 0 { None } else { Some(candidates[rng.usize(count)]) }
}

// A fixed-signature reversal-orbit move.
fn intra_move(state: &State, rng: &mut Rng) -> Option<Move> {
    for _ in 0..96 {
        let k = rng.usize(4);
        let n = LENGTHS[k];
        let h = n / 2;
        if rng.usize(3) < 2 {
            let p = rng.usize(h);
            let q = n - 1 - p;
            if state.a[k][p] != state.a[k][q] {
                let mut mv = Move::empty(); mv.push((k, p)); mv.push((k, q));
                return Some(mv);
            }
        } else {
            let p = rng.usize(h);
            let q = rng.usize(h);
            if p == q { continue; }
            let p2 = n - 1 - p;
            let q2 = n - 1 - q;
            if state.a[k][p] == state.a[k][p2]
                && state.a[k][q] == state.a[k][q2]
                && state.a[k][p] != state.a[k][q]
            {
                let mut mv = Move::empty();
                for x in [p, p2, q, q2] { mv.push((k, x)); }
                return Some(mv);
            }
        }
    }
    None
}

// Toggle two common orbit coordinates in the equal-length row pair A,B or C,D.
// Each row flips one + and one -, so row sums are fixed.  At every orbit the
// two equal-length rows toggle together, which preserves all 83 mod-four
// equations.  (Mixing an even and odd length is not safe at the large shifts.)
fn cross_fibre_move(state: &State, rng: &mut Rng) -> Option<Move> {
    for _ in 0..192 {
        let (k, l) = if rng.usize(2) == 0 { (0usize, 1usize) } else { (2usize, 3usize) };
        let h = (LENGTHS[k] / 2).min(LENGTHS[l] / 2);
        let p = rng.usize(h);
        let mut q = rng.usize(h - 1);
        if q >= p { q += 1; }
        let mut mv = Move::empty();
        let orientation = if rng.usize(2) == 0 { 1i8 } else { -1i8 };
        let pk = choose_endpoint(state, k, p, orientation, rng);
        let qk = choose_endpoint(state, k, q, -orientation, rng);
        // The second row can use either orientation independently.
        let orientation_l = if rng.usize(2) == 0 { 1i8 } else { -1i8 };
        let pl = choose_endpoint(state, l, p, orientation_l, rng);
        let ql = choose_endpoint(state, l, q, -orientation_l, rng);
        if let (Some(pk), Some(qk), Some(pl), Some(ql)) = (pk, qk, pl, ql) {
            mv.push((k, pk)); mv.push((k, qk));
            mv.push((l, pl)); mv.push((l, ql));
            return Some(mv);
        }
    }
    None
}

// In the two odd rows, the centre has no parity signature.  Pairing its flip
// with the same orbit in C and D toggles that orbit twice and balances both
// row sums.
fn odd_centre_move(state: &State, rng: &mut Rng) -> Option<Move> {
    for _ in 0..96 {
        let orbit = rng.usize(41);
        let mut mv = Move::empty();
        let mut ok = true;
        for k in [2usize, 3usize] {
            let center = 41;
            if let Some(endpoint) = choose_endpoint(state, k, orbit, -state.a[k][center], rng) {
                mv.push((k, center)); mv.push((k, endpoint));
            } else { ok = false; break; }
        }
        if ok { return Some(mv); }
    }
    None
}

// Toggle four signature coordinates together in A,B or C,D.  Requiring two
// selected + endpoints and two selected - endpoints in each row preserves its
// sum, but can cross components that have no feasible balanced two-coordinate
// move.  This is not redundant with a path of always-feasible narrow moves.
fn wide_cross_move(state: &State, rng: &mut Rng) -> Option<Move> {
    for _ in 0..256 {
        let (k, l) = if rng.usize(2) == 0 { (0usize, 1usize) } else { (2usize, 3usize) };
        let h = LENGTHS[k] / 2;
        let mut orbit = [0usize; 4];
        let mut distinct = true;
        for i in 0..4 {
            orbit[i] = rng.usize(h);
            if orbit[..i].contains(&orbit[i]) { distinct = false; break; }
        }
        if !distinct { continue; }
        let mut mv = Move::empty();
        let mut ok = true;
        for row in [k, l] {
            // One of the six two-plus sign patterns.
            let plus_a = rng.usize(4);
            let mut plus_b = rng.usize(3);
            if plus_b >= plus_a { plus_b += 1; }
            for (i, &p) in orbit.iter().enumerate() {
                let sign = if i == plus_a || i == plus_b { 1 } else { -1 };
                if let Some(endpoint) = choose_endpoint(state, row, p, sign, rng) {
                    mv.push((row, endpoint));
                } else { ok = false; break; }
            }
            if !ok { break; }
        }
        if ok { return Some(mv); }
    }
    None
}

fn random_move(state: &State, rng: &mut Rng) -> Option<Move> {
    let roll = rng.usize(100);
    if roll < 35 { cross_fibre_move(state, rng) }
    else if roll < 45 { wide_cross_move(state, rng) }
    else if roll < 53 { odd_centre_move(state, rng) }
    else { intra_move(state, rng) }
}

fn parse(path: &str) -> Option<State> {
    let text = fs::read_to_string(path).ok()?;
    let start = text.find("\"sequences\"")?;
    let bytes = text[start..].as_bytes();
    let mut values = Vec::with_capacity(334);
    let mut i = 0;
    while i < bytes.len() && values.len() < 334 {
        if bytes[i] == b'-' && i + 1 < bytes.len() && bytes[i + 1] == b'1' {
            values.push(-1); i += 2;
        } else if bytes[i] == b'1' {
            values.push(1); i += 1;
        } else { i += 1; }
    }
    if values.len() != 334 { return None; }
    let mut offset = 0;
    let a = std::array::from_fn(|k| {
        let row = values[offset..offset + LENGTHS[k]].to_vec();
        offset += LENGTHS[k];
        row
    });
    Some(State::new(a))
}

fn json(state: &State, solved: bool, elapsed: f64, moves: u64) -> String {
    let seqs = state.a.iter().map(|row| format!("[{}]", row.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(","))).collect::<Vec<_>>().join(",\n    ");
    let residual = state.r.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(",");
    format!(
        "{{\n  \"construction\": \"base sequences BS(84,83)\",\n  \"search\": \"agent coupled antisymmetric-signature cross-fibre search\",\n  \"solved\": {},\n  \"energy\": {},\n  \"l1\": {},\n  \"nonzero\": {},\n  \"parity_bad\": {},\n  \"elapsed_s\": {:.6},\n  \"moves\": {},\n  \"row_sums\": {:?},\n  \"residual\": [{}],\n  \"sequences\": [\n    {}\n  ]\n}}\n",
        solved, state.energy, 4 * state.l1_quarters(), state.nonzero(), state.parity_bad(),
        elapsed, moves, state.rows(), residual, seqs
    )
}

fn publish(state: &State, id: usize, started: Instant, atomic: &AtomicI64, best: &Mutex<State>, moves: u64) {
    let mut seen = atomic.load(Ordering::Relaxed);
    while state.energy < seen {
        match atomic.compare_exchange_weak(seen, state.energy, Ordering::SeqCst, Ordering::Relaxed) {
            Ok(_) => {
                let mut checked = state.clone(); checked.recompute();
                assert_eq!(checked.energy, state.energy);
                assert_eq!(checked.rows(), TARGET_ROWS);
                assert_eq!(checked.parity_bad(), 0);
                // CAS publication and mutex publication can arrive in a
                // different order.  Never let a delayed higher-energy writer
                // overwrite the true shared incumbent.
                let mut guard = best.lock().unwrap();
                if checked.energy < guard.energy {
                    *guard = checked.clone();
                    let _ = fs::write("agent_bs_crossfiber_live.json", json(&checked, checked.energy == 0, started.elapsed().as_secs_f64(), moves));
                    eprintln!("best={} l1={} nz={} worker={} elapsed_s={:.2}", checked.energy, 4 * checked.l1_quarters(), checked.nonzero(), id, started.elapsed().as_secs_f64());
                }
                return;
            }
            Err(actual) => seen = actual,
        }
    }
}

fn worker(id: usize, deadline: Instant, started: Instant, atomic: Arc<AtomicI64>, best: Arc<Mutex<State>>, stop: Arc<AtomicBool>) -> u64 {
    let epoch = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos() as u64;
    let mut rng = Rng(epoch ^ (id as u64 + 17).wrapping_mul(0x9e3779b97f4a7c15));
    let mode = id % 4;
    let mut total_moves = 0u64;
    while Instant::now() < deadline && !stop.load(Ordering::Relaxed) {
        let mut state = best.lock().unwrap().clone();
        for _ in 0..(8 + rng.usize(40)) {
            if let Some(mv) = random_move(&state, &mut rng) { apply_move(&mut state, &mv); }
        }
        let mut weights = [1i64; SHIFTS];
        let mut local_best = state.energy;
        let mut stale = 0usize;
        for step in 0..240_000usize {
            if step & 4095 == 0 && (Instant::now() >= deadline || stop.load(Ordering::Relaxed)) { break; }
            let phase = (step % 60_000) as f64 / 60_000.0;
            let base_temp = match mode { 0 => 90.0, 1 => 24.0, 2 => 60.0, _ => 120.0 };
            let temp = base_temp * (0.001f64).powf(phase) + 0.02;
            let before = state.score(&weights, mode);
            let count = match rng.usize(1000) { x if x < 720 => 1, x if x < 950 => 2, x if x < 992 => 3, _ => 4 + rng.usize(4) };
            let mut chosen = [Move::empty(); 8];
            let mut used = 0usize;
            if mode == 3 && count == 1 {
                // A sampled steepest-response worker is useful on the final
                // low-energy plateaus where improving moves are very sparse.
                let mut best_trial: Option<Move> = None;
                let mut best_score = i64::MAX;
                for _ in 0..128 {
                    if let Some(mv) = random_move(&state, &mut rng) {
                        apply_move(&mut state, &mv);
                        let trial_score = state.score(&weights, mode);
                        undo_move(&mut state, &mv);
                        if trial_score < best_score {
                            best_score = trial_score;
                            best_trial = Some(mv);
                        }
                    }
                }
                if let Some(mv) = best_trial {
                    apply_move(&mut state, &mv);
                    chosen[0] = mv; used = 1;
                }
            } else {
                for _ in 0..count {
                    if let Some(mv) = random_move(&state, &mut rng) {
                        apply_move(&mut state, &mv);
                        chosen[used] = mv; used += 1;
                    }
                }
            }
            if used == 0 { continue; }
            total_moves += 1;
            let delta = state.score(&weights, mode) - before;
            if delta > 0 && rng.unit() >= (-(delta as f64) / temp).exp() {
                for mv in chosen[..used].iter().rev() { undo_move(&mut state, mv); }
            } else if state.energy < local_best {
                local_best = state.energy; stale = 0;
                publish(&state, id, started, &atomic, &best, total_moves);
                if state.energy == 0 {
                    let mut checked = state.clone(); checked.recompute();
                    if checked.energy == 0 && checked.rows() == TARGET_ROWS && checked.parity_bad() == 0 {
                        *best.lock().unwrap() = checked;
                        stop.store(true, Ordering::SeqCst);
                        break;
                    }
                }
            } else { stale += 1; }

            if stale > 28_000 && mode % 2 == 1 {
                for j in 0..SHIFTS {
                    if state.r[j] != 0 { weights[j] = (weights[j] + 1 + (state.r[j].abs() / 4) as i64).min(96); }
                }
                stale = 0;
            } else if stale > 55_000 {
                state = best.lock().unwrap().clone();
                for _ in 0..(12 + rng.usize(32)) {
                    if let Some(mv) = random_move(&state, &mut rng) { apply_move(&mut state, &mv); }
                }
                weights = [1; SHIFTS]; stale = 0; local_best = state.energy;
            }

            if total_moves % 200_000 == 0 {
                let mut checked = state.clone(); checked.recompute();
                assert_eq!(checked.energy, state.energy);
                assert_eq!(checked.rows(), TARGET_ROWS);
                assert_eq!(checked.parity_bad(), 0);
            }
        }
    }
    total_moves
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let seconds = args.get(1).and_then(|x| x.parse().ok()).unwrap_or(600u64);
    let threads = args.get(2).and_then(|x| x.parse().ok()).unwrap_or(4usize);
    let input = args.get(3).expect("usage: agent_bs_crossfiber SECONDS THREADS PARITY_GOOD_JSON");
    let initial = parse(input).expect("could not parse BS(84,83) sequences");
    assert_eq!(initial.rows(), TARGET_ROWS, "input must have target row tuple");
    assert_eq!(initial.parity_bad(), 0, "input must be in the exact mod-four fibre");
    eprintln!("seed energy={} l1={} rows={:?}", initial.energy, 4 * initial.l1_quarters(), initial.rows());
    let started = Instant::now();
    let deadline = started + Duration::from_secs(seconds);
    let atomic = Arc::new(AtomicI64::new(initial.energy));
    let best = Arc::new(Mutex::new(initial));
    let stop = Arc::new(AtomicBool::new(false));
    let mut handles = Vec::new();
    for id in 0..threads {
        let (a, b, c) = (atomic.clone(), best.clone(), stop.clone());
        handles.push(thread::spawn(move || worker(id, deadline, started, a, b, c)));
    }
    let moves: u64 = handles.into_iter().map(|h| h.join().unwrap()).sum();
    let mut answer = best.lock().unwrap().clone(); answer.recompute();
    assert_eq!(answer.rows(), TARGET_ROWS);
    assert_eq!(answer.parity_bad(), 0);
    let solved = answer.energy == 0;
    let output = if solved { "agent_bs_candidate.json" } else { "agent_bs_crossfiber_summary.json" };
    fs::write(output, json(&answer, solved, started.elapsed().as_secs_f64(), moves)).unwrap();
    println!("solved={} energy={} l1={} nz={} moves={} output={}", solved, answer.energy, 4 * answer.l1_quarters(), answer.nonzero(), moves, output);
}
