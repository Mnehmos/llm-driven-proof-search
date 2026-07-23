//! Search for a binary Legendre pair of length 333 while preserving exact
//! compressions modulo both 37 and 9.  Each sequence is represented as a
//! 37-by-9 CRT grid.  A 2-by-2 switch preserves every row and column sum.
use std::{env, fs, thread};
use std::sync::{Arc, Mutex, OnceLock};
use std::sync::atomic::{AtomicBool, AtomicI64, Ordering};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

const N: usize = 333;
const H: usize = 166;
const P: usize = 37;
const Q: usize = 9;
const DEFAULT_COL: [[usize; Q]; 2] = [
    [16, 19, 17, 15, 20, 15, 27, 21, 17],
    [18, 17, 20, 21, 18, 17, 22, 18, 16],
];
static COLS: OnceLock<[[usize; Q]; 2]> = OnceLock::new();
static PREFIX: OnceLock<String> = OnceLock::new();
fn cols() -> &'static [[usize; Q]; 2] { COLS.get().unwrap_or(&DEFAULT_COL) }
fn output_name(suffix:&str)->String{format!("{}_{}",PREFIX.get().map(String::as_str).unwrap_or("lp333_dual"),suffix)}

#[derive(Clone)]
struct State {
    a: [[i8; N]; 2],
    r: [i32; H],
    e: i64,
}

impl State {
    fn new(a: [[i8; N]; 2]) -> Self {
        let mut z = Self { a, r: [0; H], e: 0 };
        z.recompute();
        z
    }
    fn recompute(&mut self) {
        self.r = [2; H];
        for d in 1..=H {
            for s in 0..2 {
                for i in 0..N {
                    self.r[d - 1] += self.a[s][i] as i32 * self.a[s][(i + d) % N] as i32;
                }
            }
        }
        self.e = self.r.iter().map(|&x| (x as i64) * (x as i64)).sum();
    }
    fn flip(&mut self, s: usize, p: usize) {
        let old = self.a[s][p] as i32;
        for d in 1..=H {
            let z = self.a[s][(p + d) % N] as i32 + self.a[s][(p + N - d) % N] as i32;
            let dr = -2 * old * z;
            let before = self.r[d - 1] as i64;
            let after = before + dr as i64;
            self.e += after * after - before * before;
            self.r[d - 1] += dr;
        }
        self.a[s][p] = -self.a[s][p];
    }
    fn score(&self, weights: &[i64; H], l1: bool) -> i64 {
        if l1 {
            self.r.iter().zip(weights).map(|(&x, &w)| w * x.abs() as i64).sum()
        } else {
            self.r.iter().zip(weights).map(|(&x, &w)| w * (x as i64) * (x as i64)).sum()
        }
    }
    fn sums(&self) -> [i32; 2] {
        [self.a[0].iter().map(|&x| x as i32).sum(), self.a[1].iter().map(|&x| x as i32).sum()]
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

fn chi(x: usize) -> i32 {
    if x == 0 { 0 } else if (1..P).any(|y| (y * y) % P == x) { 1 } else { -1 }
}
fn row_sum(s: usize, r: usize) -> i32 {
    if r == 0 { 1 } else if s == 0 { 3 * chi(r) } else { -3 * chi(r) }
}
fn row_degree(s: usize, r: usize) -> usize { ((row_sum(s, r) + Q as i32) / 2) as usize }

// The original index x has x mod 37 = r and x mod 9 = c.
fn idx(r: usize, c: usize) -> usize { r + P * ((c + Q - r % Q) % Q) }

// Bipartite Havel-Hakimi realizes the exact row and column degree sequences.
fn realization(s: usize, rng: &mut Rng) -> [[bool; Q]; P] {
    let mut grid = [[false; Q]; P];
    let mut remaining = cols()[s];
    let mut rows: Vec<(usize, u64)> = (0..P).map(|r| (r, rng.next())).collect();
    rows.sort_by(|&(r1, t1), &(r2, t2)| row_degree(s, r2).cmp(&row_degree(s, r1)).then(t1.cmp(&t2)));
    for (r, _) in rows {
        let d = row_degree(s, r);
        let mut cs: Vec<(usize, usize, u64)> = (0..Q).map(|c| (remaining[c], c, rng.next())).collect();
        cs.sort_by(|a, b| b.0.cmp(&a.0).then(a.2.cmp(&b.2)));
        assert!(cs[d - 1].0 > 0, "non-graphical margin encountered");
        for &(_, c, _) in &cs[..d] {
            grid[r][c] = true;
            remaining[c] -= 1;
        }
    }
    assert_eq!(remaining, [0; Q]);
    grid
}

fn random_state(rng: &mut Rng) -> State {
    let mut a = [[-1i8; N]; 2];
    for s in 0..2 {
        let grid = realization(s, rng);
        for r in 0..P { for c in 0..Q { a[s][idx(r, c)] = if grid[r][c] { 1 } else { -1 }; } }
    }
    let mut z = State::new(a);
    for _ in 0..20_000 {
        let _ = switch_move(&mut z, rng, &mut [(0, 0); 4]);
    }
    z
}

fn load_raw(path: &str) -> Option<State> {
    let text = fs::read_to_string(path).ok()?;
    let payload = if let Some(p) = text.find("\"sequences\"") { &text[p..] } else { &text };
    let values: Vec<i8> = payload.split(|ch: char| !(ch == '-' || ch.is_ascii_digit()))
        .filter(|x| !x.is_empty()).take(2 * N).map(|x| x.parse::<i8>()).collect::<Result<_,_>>().ok()?;
    if values.len() != 2 * N || values.iter().any(|&x| x != 1 && x != -1) { return None; }
    let mut a = [[0i8; N]; 2];
    for s in 0..2 { a[s].copy_from_slice(&values[s*N..(s+1)*N]); }
    let z = State::new(a); validate_margins(&z); Some(z)
}

// Returns false only if no switch was sampled after a generous bounded retry.
fn switch_move(st: &mut State, rng: &mut Rng, undo: &mut [(usize, usize); 4]) -> bool {
    for _ in 0..256 {
        let s = rng.usize(2);
        let r1 = rng.usize(P);
        let mut r2 = rng.usize(P - 1); if r2 >= r1 { r2 += 1; }
        let c1 = rng.usize(Q);
        let mut c2 = rng.usize(Q - 1); if c2 >= c1 { c2 += 1; }
        let p = [idx(r1, c1), idx(r1, c2), idx(r2, c1), idx(r2, c2)];
        let v = [st.a[s][p[0]], st.a[s][p[1]], st.a[s][p[2]], st.a[s][p[3]]];
        if v[0] == v[3] && v[1] == v[2] && v[0] != v[1] {
            for j in 0..4 { undo[j] = (s, p[j]); st.flip(s, p[j]); }
            return true;
        }
    }
    false
}

fn cycle3_move(st: &mut State, rng: &mut Rng, undo: &mut [(usize, usize); 6]) -> bool {
    for _ in 0..256 {
        let s=rng.usize(2);let r0=rng.usize(P);let mut r1=rng.usize(P-1);if r1>=r0{r1+=1}
        let mut r2=rng.usize(P-2);let(lo,hi)=if r0<r1{(r0,r1)}else{(r1,r0)};if r2>=lo{r2+=1}if r2>=hi{r2+=1}
        let c0=rng.usize(Q);let mut c1=rng.usize(Q-1);if c1>=c0{c1+=1}
        let mut c2=rng.usize(Q-2);let(lo2,hi2)=if c0<c1{(c0,c1)}else{(c1,c0)};if c2>=lo2{c2+=1}if c2>=hi2{c2+=1}
        let p=[idx(r0,c0),idx(r0,c1),idx(r1,c1),idx(r1,c2),idx(r2,c2),idx(r2,c0)];
        let v=p.map(|x|st.a[s][x]);
        if v[0]==v[2]&&v[2]==v[4]&&v[1]==v[3]&&v[3]==v[5]&&v[0]!=v[1]{
            for j in 0..6{undo[j]=(s,p[j]);st.flip(s,p[j]);}return true
        }
    }false
}

fn compress37(st: &State) -> [[i32; P]; 2] {
    std::array::from_fn(|s| std::array::from_fn(|r| (0..Q).map(|c| st.a[s][idx(r, c)] as i32).sum()))
}
fn compress9(st: &State) -> [[i32; Q]; 2] {
    std::array::from_fn(|s| std::array::from_fn(|c| (0..P).map(|r| st.a[s][idx(r, c)] as i32).sum()))
}
fn validate_margins(st: &State) {
    assert_eq!(st.sums(), [1, 1]);
    let a = compress37(st); let b = compress9(st);
    for s in 0..2 { for r in 0..P { assert_eq!(a[s][r], row_sum(s, r)); } }
    for s in 0..2 { for c in 0..Q { assert_eq!(((b[s][c] + P as i32) / 2) as usize, cols()[s][c]); } }
}
fn load_columns(path: &str) -> Option<[[usize; Q]; 2]> {
    let text=fs::read_to_string(path).ok()?; let p=text.find("\"column_plus_counts\"")?;
    let v:Vec<usize>=text[p..].split(|ch:char|!ch.is_ascii_digit()).filter(|x|!x.is_empty()).take(2*Q).map(|x|x.parse()).collect::<Result<_,_>>().ok()?;
    if v.len()!=2*Q{return None} let mut z=[[0usize;Q];2]; for s in 0..2{z[s].copy_from_slice(&v[s*Q..(s+1)*Q]);} Some(z)
}
fn json(st: &State, solved: bool, elapsed: f64, moves: u64) -> String {
    let seq = st.a.iter().map(|x| format!("[{}]", x.iter().map(|v| v.to_string()).collect::<Vec<_>>().join(","))).collect::<Vec<_>>().join(",");
    let rr = st.r.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(",");
    format!("{{\"construction\":\"Legendre pair length 333\",\"fixed_compressions\":[\"quadratic-character length 37\",\"exact length 9\"],\"solved\":{},\"energy\":{},\"elapsed_s\":{},\"moves\":{},\"sums\":{:?},\"residual_paf_plus_2\":[{}],\"compression37\":{:?},\"compression9\":{:?},\"sequences\":[{}]}}\n", solved, st.e, elapsed, moves, st.sums(), rr, compress37(st), compress9(st), seq)
}
fn publish(st: &State, id: usize, start: Instant, atom: &AtomicI64, best: &Mutex<State>) {
    let mut seen = atom.load(Ordering::Relaxed);
    while st.e < seen {
        match atom.compare_exchange_weak(seen, st.e, Ordering::SeqCst, Ordering::Relaxed) {
            Ok(_) => {
                validate_margins(st);
                *best.lock().unwrap() = st.clone();
                let _ = fs::write(output_name("live.json"), json(st, false, start.elapsed().as_secs_f64(), 0));
                eprintln!("best energy={} worker={} nonzero={} maxabs={} elapsed_s={:.3}", st.e, id, st.r.iter().filter(|&&x|x!=0).count(), st.r.iter().map(|x|x.abs()).max().unwrap(), start.elapsed().as_secs_f64());
                return;
            }
            Err(x) => seen = x,
        }
    }
}

fn worker(id: usize, end: Instant, start: Instant, atom: Arc<AtomicI64>, best: Arc<Mutex<State>>, stop: Arc<AtomicBool>) -> u64 {
    let epoch = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos() as u64;
    let mut rng = Rng(epoch ^ (id as u64 + 401).wrapping_mul(0x9e3779b97f4a7c15));
    let mut moves = 0u64;
    while Instant::now() < end && !stop.load(Ordering::Relaxed) {
        let mut st = if rng.usize(6) == 0 { random_state(&mut rng) } else { best.lock().unwrap().clone() };
        for _ in 0..rng.usize(300) { let _ = switch_move(&mut st, &mut rng, &mut [(0, 0); 4]); }
        let mut weights = [1i64; H];
        let mut stale = 0usize;
        let mut local = st.e;
        for step in 0..600_000usize {
            if step & 8191 == 0 && (Instant::now() >= end || stop.load(Ordering::Relaxed)) { break; }
            let phase = step as f64 / 600_000.0;
            let l1 = id % 4 == 2;
            let base = if l1 { 150.0 } else if id % 3 == 0 { 7000.0 } else if id % 3 == 1 { 2000.0 } else { 600.0 };
            let temp = base * (0.00015f64).powf(phase) + 0.02;
            let before = st.score(&weights, l1);
            let roll = rng.usize(1000);
            let use_cycle=roll>=950;
            let count = if roll < 720 { 1 } else if roll < 920 { 2 } else { 3 };
            let mut undo = [[(0usize, 0usize); 4]; 3];
            let mut cycle_undo=[(0usize,0usize);6];let mut cycle_used=false;
            let mut used = 0usize;
            if use_cycle {cycle_used=cycle3_move(&mut st,&mut rng,&mut cycle_undo);}
            else if id % 4 == 3 && count == 1 {
                let mut best_score = i64::MAX; let mut best_move = [(0usize, 0usize); 4]; let mut found = false;
                for _ in 0..128 {
                    let mut trial = [(0usize, 0usize); 4];
                    if !switch_move(&mut st, &mut rng, &mut trial) { continue; }
                    let score = st.score(&weights, l1);
                    for &(s,p) in trial.iter().rev() { st.flip(s,p); }
                    if score < best_score { best_score = score; best_move = trial; found = true; }
                }
                if found { for j in 0..4 { let (s,p)=best_move[j]; undo[0][j]=(s,p); st.flip(s,p); } used=1; }
            } else {
                for _ in 0..count { if switch_move(&mut st, &mut rng, &mut undo[used]) { used += 1; } }
            }
            if used == 0 && !cycle_used { continue; }
            moves += 1;
            let de = st.score(&weights, l1) - before;
            if de > 0 && rng.unit() >= (-(de as f64) / temp).exp() {
                if cycle_used{for &(s,p) in cycle_undo.iter().rev(){st.flip(s,p)}}
                else{for j in (0..used).rev() { for &(s, p) in undo[j].iter().rev() { st.flip(s, p); } }}
            } else if st.e < local {
                local = st.e; stale = 0; publish(&st, id, start, &atom, &best);
                if st.e == 0 {
                    let mut check = st.clone(); check.recompute(); validate_margins(&check);
                    if check.e == 0 { *best.lock().unwrap() = check; stop.store(true, Ordering::SeqCst); break; }
                }
            } else { stale += 1; }
            if id % 2 == 1 && stale > 60_000 {
                for j in 0..H { if st.r[j] != 0 { weights[j] = (weights[j] + 1 + (st.r[j].abs() / 4) as i64).min(96); } }
                stale = 0;
            } else if stale > 160_000 { break; }
        }
    }
    moves
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let secs = args.get(1).and_then(|x| x.parse().ok()).unwrap_or(1800);
    let threads = args.get(2).and_then(|x| x.parse().ok()).unwrap_or(3);
    if let Some(path)=args.get(4) { COLS.set(load_columns(path).expect("invalid length-9 compression file")).unwrap(); }
    if let Some(prefix)=args.get(5) { PREFIX.set(prefix.clone()).unwrap(); }
    let mut rng = Rng(333009037);
    let initial = args.get(3).and_then(|p| load_raw(p)).unwrap_or_else(|| random_state(&mut rng));
    validate_margins(&initial);
    eprintln!("seed energy={} sums={:?}", initial.e, initial.sums());
    let start = Instant::now(); let end = start + Duration::from_secs(secs);
    let atom = Arc::new(AtomicI64::new(initial.e));
    let best = Arc::new(Mutex::new(initial));
    let stop = Arc::new(AtomicBool::new(false));
    let mut handles = vec![];
    for id in 0..threads {
        let (a, b, c) = (atom.clone(), best.clone(), stop.clone());
        handles.push(thread::spawn(move || worker(id, end, start, a, b, c)));
    }
    let moves = handles.into_iter().map(|h| h.join().unwrap()).sum();
    let mut answer = best.lock().unwrap().clone(); answer.recompute(); validate_margins(&answer);
    let solved = answer.e == 0;
    let out = if solved { output_name("candidate.json") } else { output_name("summary.json") };
    fs::write(&out, json(&answer, solved, start.elapsed().as_secs_f64(), moves)).unwrap();
    println!("result solved={} energy={} moves={} output={}", solved, answer.e, moves, out);
}
