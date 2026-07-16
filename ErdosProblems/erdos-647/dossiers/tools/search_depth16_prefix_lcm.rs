//! Deterministic steering search for a depth-16 prefix-LCM witness.
//!
//! We seek an `A` such that all sixteen integers
//!
//!     (720720 / k) * A - 1,  1 <= k <= 16,
//!
//! are prime.  Then `n = 720720*A` satisfies the first sixteen divisor
//! budgets by the separately formalized conditional-window theorem.
//!
//! This program is computational steering, not proof.  Primality is tested by
//! the deterministic Miller--Rabin basis set valid for every 64-bit integer.
//! A found witness must still be replayed in Lean before it is theorem-grade.
//!
//! Build:
//!   rustc -O search_depth16_prefix_lcm.rs -o search_depth16_prefix_lcm.exe
//! Run:
//!   search_depth16_prefix_lcm.exe [max_A] [threads] [small_prime_limit]

use std::collections::BTreeSet;
use std::env;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::Instant;

const L: u64 = 720_720;
const COEFFS: [u64; 16] = [
    720_720, 360_360, 240_240, 180_180, 144_144, 120_120, 102_960, 90_090, 80_080, 72_072, 65_520,
    60_060, 55_440, 51_480, 48_048, 45_045,
];

// The tuple forces A even (from the k=16 odd coefficient) and A=0 mod 17.
const FORCED_STEP: u64 = 34;
const CHUNK_MULTIPLIERS: u64 = 1_000_000;

#[derive(Clone)]
struct PrimeFilter {
    p: u32,
    forbidden: Vec<u32>,
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

/// Deterministic Miller--Rabin for the full `u64` range.
fn is_prime_u64(n: u64) -> bool {
    if n < 2 {
        return false;
    }
    for &p in &[2u64, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37] {
        if n % p == 0 {
            return n == p;
        }
    }
    let mut d = n - 1;
    let mut s = 0u32;
    while d & 1 == 0 {
        d >>= 1;
        s += 1;
    }
    // Jim Sinclair/Jacobsen 7-base set, deterministic below 2^64.
    for &a in &[2u64, 325, 9_375, 28_178, 450_775, 9_780_504, 1_795_265_022] {
        let a = a % n;
        if a == 0 {
            continue;
        }
        let mut x = pow_mod(a, d, n);
        if x == 1 || x == n - 1 {
            continue;
        }
        let mut witnessed_composite = true;
        for _ in 1..s {
            x = mul_mod(x, x, n);
            if x == n - 1 {
                witnessed_composite = false;
                break;
            }
        }
        if witnessed_composite {
            return false;
        }
    }
    true
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
    while p * p <= limit {
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
            let mut roots = BTreeSet::new();
            for &c in &COEFFS {
                let r = c % p as u64;
                if r != 0 {
                    // p is prime, so r^(p-2) is its inverse modulo p.
                    roots.insert(pow_mod(r, p as u64 - 2, p as u64) as u32);
                }
            }
            PrimeFilter {
                p,
                forbidden: roots.into_iter().collect(),
            }
        })
        .collect()
}

fn passes_filters(a: u64, filters: &[PrimeFilter]) -> bool {
    for f in filters {
        let r = (a % f.p as u64) as u32;
        if f.forbidden.binary_search(&r).is_ok() {
            return false;
        }
    }
    true
}

fn tuple_values(a: u64) -> Option<[u64; 16]> {
    let mut values = [0u64; 16];
    for (i, &c) in COEFFS.iter().enumerate() {
        values[i] = c.checked_mul(a)?.checked_sub(1)?;
    }
    Some(values)
}

fn audit(filters: &[PrimeFilter], max_a: u64) {
    assert_eq!(COEFFS.iter().copied().collect::<BTreeSet<_>>().len(), 16);
    for k in 1..=16usize {
        assert_eq!(COEFFS[k - 1], L / k as u64);
    }
    assert!(
        L.checked_mul(max_a).is_some(),
        "max_A overflows the largest form"
    );
    let largest_filter_prime = filters.last().map_or(0, |f| f.p as u64);
    assert!(
        COEFFS[15] * FORCED_STEP - 1 > largest_filter_prime,
        "small-prime filtering would need to preserve q=p exceptions"
    );

    println!("L={L}; 16 distinct coefficients={COEFFS:?}");
    println!("forced arithmetic progression: A = 0 (mod 34)");
    for f in filters {
        assert!(
            f.forbidden.len() < f.p as usize,
            "inadmissible tuple modulo {}",
            f.p
        );
    }
    println!("admissibility root counts (p, forbidden, allowed):");
    for f in filters.iter().filter(|f| f.p <= 47) {
        println!(
            "  p={} forbidden={} allowed={}",
            f.p,
            f.forbidden.len(),
            f.p as usize - f.forbidden.len()
        );
    }
    let f2 = filters.iter().find(|f| f.p == 2).unwrap();
    let f17 = filters.iter().find(|f| f.p == 17).unwrap();
    assert_eq!(f2.forbidden, vec![1]);
    assert_eq!(f17.forbidden.len(), 16);
    assert!(!f17.forbidden.contains(&0));

    // Cross-check Miller--Rabin against exact trial division on a bounded range.
    for n in 0u64..=100_000 {
        let trial = n >= 2 && (2..=((n as f64).sqrt() as u64)).all(|d| n % d != 0);
        assert_eq!(is_prime_u64(n), trial, "primality self-check failed at {n}");
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let max_a: u64 = args
        .get(1)
        .and_then(|s| s.parse().ok())
        .unwrap_or(1_000_000_000);
    let threads: usize = args
        .get(2)
        .and_then(|s| s.parse().ok())
        .unwrap_or_else(|| thread::available_parallelism().map_or(1, usize::from));
    let sieve_limit: usize = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(10_000);
    assert!(max_a >= FORCED_STEP);

    let filters = Arc::new(make_filters(sieve_limit));
    audit(&filters, max_a);
    println!(
        "scan: 34 <= A <= {max_a}, {} threads, small primes <= {sieve_limit}",
        threads
    );

    let max_m = max_a / FORCED_STEP;
    let next_m = Arc::new(AtomicU64::new(1));
    let tested = Arc::new(AtomicU64::new(0));
    let filter_survivors = Arc::new(AtomicU64::new(0));
    let mr_tests = Arc::new(AtomicU64::new(0));
    let stop = Arc::new(AtomicBool::new(false));
    let answer: Arc<Mutex<Option<(u64, [u64; 16])>>> = Arc::new(Mutex::new(None));
    let started = Instant::now();

    let mut handles = Vec::new();
    for _ in 0..threads {
        let filters = Arc::clone(&filters);
        let next_m = Arc::clone(&next_m);
        let tested = Arc::clone(&tested);
        let filter_survivors = Arc::clone(&filter_survivors);
        let mr_tests = Arc::clone(&mr_tests);
        let stop = Arc::clone(&stop);
        let answer = Arc::clone(&answer);
        handles.push(thread::spawn(move || {
            while !stop.load(Ordering::Relaxed) {
                let lo = next_m.fetch_add(CHUNK_MULTIPLIERS, Ordering::Relaxed);
                if lo > max_m {
                    break;
                }
                let hi = (lo + CHUNK_MULTIPLIERS).min(max_m + 1);
                for m in lo..hi {
                    if stop.load(Ordering::Relaxed) {
                        break;
                    }
                    let a = FORCED_STEP * m;
                    tested.fetch_add(1, Ordering::Relaxed);
                    if !passes_filters(a, &filters) {
                        continue;
                    }
                    filter_survivors.fetch_add(1, Ordering::Relaxed);
                    let values = tuple_values(a).expect("audited u64 range");
                    // Test the smaller/cheaper forms first.
                    let mut all_prime = true;
                    for &q in values.iter().rev() {
                        mr_tests.fetch_add(1, Ordering::Relaxed);
                        if !is_prime_u64(q) {
                            all_prime = false;
                            break;
                        }
                    }
                    if all_prime {
                        *answer.lock().unwrap() = Some((a, values));
                        stop.store(true, Ordering::Relaxed);
                        break;
                    }
                }
            }
        }));
    }
    for h in handles {
        h.join().unwrap();
    }

    let elapsed = started.elapsed().as_secs_f64();
    let tested = tested.load(Ordering::Relaxed);
    let survivors = filter_survivors.load(Ordering::Relaxed);
    let mr = mr_tests.load(Ordering::Relaxed);
    println!("tested forced candidates: {tested}");
    println!(
        "small-sieve survivors: {survivors} ({:.9}%)",
        100.0 * survivors as f64 / tested as f64
    );
    println!("Miller--Rabin tests: {mr}");
    println!(
        "elapsed: {:.3}s; forced candidates/s: {:.0}; MR tests/s: {:.0}",
        elapsed,
        tested as f64 / elapsed,
        mr as f64 / elapsed
    );
    let result = *answer.lock().unwrap();
    match result {
        Some((a, values)) => {
            println!("WITNESS A={a}; n={}", L * a);
            for (k, q) in (1usize..=16).zip(values) {
                println!("  k={k:2} coeff={} q={q}", COEFFS[k - 1]);
            }
        }
        None => println!("NO WITNESS in the audited range 34 <= A <= {max_a}, A=0 mod 34"),
    }
}
