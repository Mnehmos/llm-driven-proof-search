//! Deterministic steering search for an exact depth-16 prefix-LCM survivor.
//!
//! For `L = lcm(1,...,16) = 720720`, this scans `n = L*A` and tests the
//! actual conditions
//!
//!     tau(n-k) <= k+2,  1 <= k <= 16.
//!
//! Shifts 2, 3, 4, 6, 8, and 12 force `(L/k)*A-1` to be prime.  Shift 1
//! permits a prime or a prime square.  These seven necessary conditions are
//! sieved and tested first.  Every survivor is then factored completely with
//! deterministic Pollard--Brent plus deterministic full-u64 Miller--Rabin;
//! the factorization product and primality of every returned factor are
//! audited before its divisor count is used.
//!
//! This executable is computational steering, not a formal proof.  Any found
//! witness must be replayed as an explicit Lean certificate.

use std::collections::BTreeMap;
use std::env;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::Instant;

const L: u64 = 720_720;
const PRIME_SHIFTS: [usize; 7] = [1, 2, 3, 4, 6, 8, 12];
const PRIME_COEFFS: [u64; 7] = [720_720, 360_360, 240_240, 180_180, 120_120, 90_090, 60_060];
const TEST_ORDER: [usize; 7] = [6, 5, 4, 3, 2, 1, 0];
const CHUNK: u64 = 1_000_000;

#[derive(Clone)]
struct RootRule {
    residue: u32,
    forms: u8,
}

#[derive(Clone)]
struct PrimeFilter {
    p: u32,
    rules: Vec<RootRule>,
}

#[derive(Clone, Debug)]
struct ExactRow {
    k: usize,
    value: u64,
    factors: Vec<(u64, u32)>,
    tau: u64,
}

#[derive(Clone, Debug)]
struct Witness {
    a: u64,
    rows: Vec<ExactRow>,
}

fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let r = a % b;
        a = b;
        b = r;
    }
    a
}

fn mul_mod(a: u64, b: u64, m: u64) -> u64 {
    ((a as u128 * b as u128) % m as u128) as u64
}

fn pow_mod(mut a: u64, mut e: u64, m: u64) -> u64 {
    let mut r = 1u64;
    while e != 0 {
        if e & 1 == 1 {
            r = mul_mod(r, a, m);
        }
        a = mul_mod(a, a, m);
        e >>= 1;
    }
    r
}

/// Deterministic Miller--Rabin on the full `u64` range.
fn is_prime(n: u64) -> bool {
    if n < 2 {
        return false;
    }
    for &p in &[2u64, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37] {
        if n % p == 0 {
            return n == p;
        }
    }
    let s = (n - 1).trailing_zeros();
    let d = (n - 1) >> s;
    'bases: for &base in &[2u64, 325, 9_375, 28_178, 450_775, 9_780_504, 1_795_265_022] {
        let a = base % n;
        if a == 0 {
            continue;
        }
        let mut x = pow_mod(a, d, n);
        if x == 1 || x == n - 1 {
            continue;
        }
        for _ in 1..s {
            x = mul_mod(x, x, n);
            if x == n - 1 {
                continue 'bases;
            }
        }
        return false;
    }
    true
}

fn is_prime_square(n: u64) -> bool {
    let mut r = (n as f64).sqrt() as u64;
    while r.checked_mul(r).is_some_and(|x| x > n) {
        r -= 1;
    }
    while r.checked_add(1).and_then(|x| x.checked_mul(x)).is_some_and(|x| x <= n) {
        r += 1;
    }
    r.checked_mul(r) == Some(n) && is_prime(r)
}

fn small_primes(limit: usize) -> Vec<u32> {
    let mut sieve = vec![true; limit.saturating_add(1)];
    if !sieve.is_empty() {
        sieve[0] = false;
    }
    if limit >= 1 {
        sieve[1] = false;
    }
    let mut p = 2usize;
    while p <= limit / p {
        if sieve[p] {
            let mut m = p * p;
            while m <= limit {
                sieve[m] = false;
                m += p;
            }
        }
        p += 1;
    }
    sieve
        .iter()
        .enumerate()
        .filter_map(|(n, &ok)| ok.then_some(n as u32))
        .collect()
}

fn make_filters(limit: usize) -> Vec<PrimeFilter> {
    small_primes(limit)
        .into_iter()
        .map(|p| {
            let mut grouped = BTreeMap::<u32, u8>::new();
            for (i, &c) in PRIME_COEFFS.iter().enumerate() {
                let r = c % p as u64;
                if r != 0 {
                    let inv = pow_mod(r, p as u64 - 2, p as u64) as u32;
                    *grouped.entry(inv).or_insert(0) |= 1u8 << i;
                }
            }
            PrimeFilter {
                p,
                rules: grouped
                    .into_iter()
                    .map(|(residue, forms)| RootRule { residue, forms })
                    .collect(),
            }
        })
        .collect()
}

/// Necessary small-prime filtering, retaining the exact `q=p` exception and
/// the shift-1 `q=p^2` exception.
fn passes_filters(a: u64, filters: &[PrimeFilter]) -> bool {
    for filter in filters {
        let residue = (a % filter.p as u64) as u32;
        let Ok(pos) = filter.rules.binary_search_by_key(&residue, |r| r.residue) else {
            continue;
        };
        let rule = &filter.rules[pos];
        for i in 0..PRIME_COEFFS.len() {
            if rule.forms & (1u8 << i) == 0 {
                continue;
            }
            let q = PRIME_COEFFS[i] * a - 1;
            let p = filter.p as u64;
            if q == p || (i == 0 && p.checked_mul(p) == Some(q)) {
                continue;
            }
            return false;
        }
    }
    true
}

fn passes_seven_shapes(a: u64, mr_tests: &AtomicU64) -> bool {
    for &i in &TEST_ORDER {
        let q = PRIME_COEFFS[i] * a - 1;
        mr_tests.fetch_add(1, Ordering::Relaxed);
        if is_prime(q) {
            continue;
        }
        if i == 0 && is_prime_square(q) {
            continue;
        }
        return false;
    }
    true
}

fn rho_step(x: u64, c: u64, n: u64) -> u64 {
    (mul_mod(x, x, n) + c) % n
}

/// Deterministic Pollard--Brent splitter.  Returned values are always checked
/// by exact division, and terminal factors are checked by deterministic MR.
fn pollard_brent(n: u64) -> u64 {
    for &p in &[2u64, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37] {
        if n % p == 0 {
            return p;
        }
    }
    let mut c = 1u64;
    loop {
        let mut y = 2u64.wrapping_add(c) % n;
        let mut r = 1u64;
        let m = 128u64;
        let mut g = 1u64;
        let mut x = 0u64;
        let mut ys = 0u64;
        while g == 1 {
            x = y;
            for _ in 0..r {
                y = rho_step(y, c, n);
            }
            let mut k = 0u64;
            while k < r && g == 1 {
                ys = y;
                let count = m.min(r - k);
                let mut q = 1u64;
                for _ in 0..count {
                    y = rho_step(y, c, n);
                    q = mul_mod(q, x.abs_diff(y), n);
                }
                g = gcd(q, n);
                k += count;
            }
            r = r.checked_mul(2).expect("Pollard--Brent cycle length overflow");
        }
        if g == n {
            loop {
                ys = rho_step(ys, c, n);
                g = gcd(x.abs_diff(ys), n);
                if g > 1 {
                    break;
                }
            }
        }
        if g < n && n % g == 0 {
            return g;
        }
        c = c.checked_add(1).expect("Pollard--Brent seed exhaustion");
    }
}

fn factor_recursive(n: u64, out: &mut Vec<u64>) {
    if n == 1 {
        return;
    }
    if is_prime(n) {
        out.push(n);
        return;
    }
    let d = pollard_brent(n);
    assert!(1 < d && d < n && n % d == 0);
    factor_recursive(d, out);
    factor_recursive(n / d, out);
}

fn factor_and_tau(n: u64) -> (Vec<(u64, u32)>, u64) {
    assert!(n > 0);
    let mut flat = Vec::new();
    factor_recursive(n, &mut flat);
    flat.sort_unstable();
    let mut product = 1u128;
    for &p in &flat {
        assert!(is_prime(p), "nonprime terminal factor {p}");
        product *= p as u128;
    }
    assert_eq!(product, n as u128, "factorization product mismatch");
    let mut grouped = Vec::<(u64, u32)>::new();
    for p in flat {
        if let Some(last) = grouped.last_mut() {
            if last.0 == p {
                last.1 += 1;
                continue;
            }
        }
        grouped.push((p, 1));
    }
    let tau = grouped.iter().fold(1u64, |acc, &(_, e)| {
        acc.checked_mul(e as u64 + 1).expect("tau overflow")
    });
    (grouped, tau)
}

fn exact_depth16(a: u64, factorizations: &AtomicU64, failure_hist: &[AtomicU64; 17]) -> Option<Witness> {
    let n = L * a;
    let mut rows = Vec::with_capacity(16);
    for k in 1usize..=16 {
        let value = n - k as u64;
        let (factors, tau) = factor_and_tau(value);
        factorizations.fetch_add(1, Ordering::Relaxed);
        rows.push(ExactRow {
            k,
            value,
            factors,
            tau,
        });
        if tau > k as u64 + 2 {
            failure_hist[k].fetch_add(1, Ordering::Relaxed);
            return None;
        }
    }
    Some(Witness { a, rows })
}

fn audit(filters: &[PrimeFilter], max_a: u64) {
    for (i, &k) in PRIME_SHIFTS.iter().enumerate() {
        assert_eq!(PRIME_COEFFS[i], L / k as u64);
    }
    assert!(L.checked_mul(max_a).is_some(), "max_A overflows n=L*A");
    for filter in filters {
        assert!(
            filter.rules.len() < filter.p as usize,
            "seven necessary forms are inadmissible modulo {}",
            filter.p
        );
    }
    for n in 0u64..=100_000 {
        let trial = n >= 2 && (2..=((n as f64).sqrt() as u64)).all(|d| n % d != 0);
        assert_eq!(is_prime(n), trial, "MR self-check failed at {n}");
    }
    for n in 1u64..=20_000 {
        let (factors, tau) = factor_and_tau(n);
        let trial_tau = (1..=n).filter(|d| n % d == 0).count() as u64;
        assert_eq!(tau, trial_tau, "tau self-check failed at {n}: {factors:?}");
    }
    println!("L={L}; exact budgets tau(L*A-k)<=k+2 for 1<=k<=16");
    println!("necessary prime-like shifts={PRIME_SHIFTS:?}; coefficients={PRIME_COEFFS:?}");
    println!("deterministic MR and Pollard--Brent/tau self-checks passed");
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let max_a: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1_000_000_000);
    let threads: usize = args
        .get(2)
        .and_then(|s| s.parse().ok())
        .unwrap_or_else(|| thread::available_parallelism().map_or(1, usize::from));
    let sieve_limit: usize = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(10_000);
    assert!(max_a >= 1);
    assert!(threads >= 1);

    let filters = Arc::new(make_filters(sieve_limit));
    audit(&filters, max_a);
    println!("scan: 1 <= A <= {max_a}, {threads} threads, necessary-form sieve <= {sieve_limit}");

    let next_a = Arc::new(AtomicU64::new(1));
    let tested = Arc::new(AtomicU64::new(0));
    let sieve_survivors = Arc::new(AtomicU64::new(0));
    let mr_tests = Arc::new(AtomicU64::new(0));
    let seven_shapes = Arc::new(AtomicU64::new(0));
    let factorizations = Arc::new(AtomicU64::new(0));
    let failure_hist = Arc::new(std::array::from_fn::<_, 17, _>(|_| AtomicU64::new(0)));
    let stop = Arc::new(AtomicBool::new(false));
    let answer = Arc::new(Mutex::new(None::<Witness>));
    let started = Instant::now();

    let mut handles = Vec::new();
    for _ in 0..threads {
        let filters = Arc::clone(&filters);
        let next_a = Arc::clone(&next_a);
        let tested = Arc::clone(&tested);
        let sieve_survivors = Arc::clone(&sieve_survivors);
        let mr_tests = Arc::clone(&mr_tests);
        let seven_shapes = Arc::clone(&seven_shapes);
        let factorizations = Arc::clone(&factorizations);
        let failure_hist = Arc::clone(&failure_hist);
        let stop = Arc::clone(&stop);
        let answer = Arc::clone(&answer);
        handles.push(thread::spawn(move || {
            while !stop.load(Ordering::Relaxed) {
                let lo = next_a.fetch_add(CHUNK, Ordering::Relaxed);
                if lo > max_a {
                    break;
                }
                let hi = lo.saturating_add(CHUNK).min(max_a.saturating_add(1));
                for a in lo..hi {
                    if stop.load(Ordering::Relaxed) {
                        break;
                    }
                    tested.fetch_add(1, Ordering::Relaxed);
                    if !passes_filters(a, &filters) {
                        continue;
                    }
                    sieve_survivors.fetch_add(1, Ordering::Relaxed);
                    if !passes_seven_shapes(a, &mr_tests) {
                        continue;
                    }
                    seven_shapes.fetch_add(1, Ordering::Relaxed);
                    if let Some(witness) = exact_depth16(a, &factorizations, &failure_hist) {
                        *answer.lock().unwrap() = Some(witness);
                        stop.store(true, Ordering::Relaxed);
                        break;
                    }
                }
            }
        }));
    }
    for handle in handles {
        handle.join().unwrap();
    }

    let elapsed = started.elapsed().as_secs_f64();
    let tested = tested.load(Ordering::Relaxed);
    let sieve_survivors = sieve_survivors.load(Ordering::Relaxed);
    let mr_tests = mr_tests.load(Ordering::Relaxed);
    let seven_shapes = seven_shapes.load(Ordering::Relaxed);
    let factorizations = factorizations.load(Ordering::Relaxed);
    println!("tested A: {tested}");
    println!("necessary-form sieve survivors: {sieve_survivors}");
    println!("deterministic MR shape tests: {mr_tests}");
    println!("seven-shape survivors: {seven_shapes}");
    println!("exact shifted factorizations: {factorizations}");
    println!("first-failure histogram among seven-shape survivors:");
    for k in 1..=16 {
        let count = failure_hist[k].load(Ordering::Relaxed);
        if count != 0 {
            println!("  k={k}: {count}");
        }
    }
    println!(
        "elapsed: {:.3}s; A/s: {:.0}; sieve survivors/s: {:.1}",
        elapsed,
        tested as f64 / elapsed,
        sieve_survivors as f64 / elapsed
    );

    match answer.lock().unwrap().clone() {
        Some(witness) => {
            println!("DEPTH-16 WITNESS A={} n={}", witness.a, L * witness.a);
            for row in witness.rows {
                println!(
                    "  k={:2} value={} factors={:?} tau={} budget={}",
                    row.k,
                    row.value,
                    row.factors,
                    row.tau,
                    row.k + 2
                );
            }
        }
        None => println!("NO DEPTH-16 SURVIVOR in the audited range 1 <= A <= {max_a}"),
    }
}
