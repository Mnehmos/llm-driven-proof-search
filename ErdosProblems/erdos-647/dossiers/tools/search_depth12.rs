//! Computational steering search for fixed-depth Erdős #647 survivors.
//!
//! This is reproducible empirical evidence, not part of the Lean proof chain.

use std::env;
use std::time::Instant;

const FORMS: [u64; 7] = [210, 315, 420, 630, 840, 1260, 2520];
// Any shortlisted candidate also needs 504N-1, 280N-1, and 252N-1 to
// have one of a few prime-like shapes.  A divisor p >= 11 rules every such
// shape out, so these three forms can safely participate in the small-prime
// sieve (the exceptional multipliers are only 3 and 5).
const SIEVE_FORMS: [u64; 10] = [210, 315, 420, 630, 840, 1260, 2520, 504, 280, 252];

fn mod_mul(a: u64, b: u64, m: u64) -> u64 {
    ((a as u128 * b as u128) % m as u128) as u64
}

fn mod_pow(mut a: u64, mut e: u64, m: u64) -> u64 {
    let mut r = 1u64;
    while e > 0 {
        if e & 1 == 1 { r = mod_mul(r, a, m); }
        a = mod_mul(a, a, m);
        e >>= 1;
    }
    r
}

// Deterministic Miller--Rabin on the full u64 range.
fn prime(n: u64) -> bool {
    if n < 2 { return false; }
    for p in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37] {
        if n == p { return true; }
        if n % p == 0 { return false; }
    }
    let s = (n - 1).trailing_zeros();
    let d = (n - 1) >> s;
    'bases: for a in [2u64, 325, 9375, 28178, 450775, 9_780_504, 1_795_265_022] {
        if a % n == 0 { continue; }
        let mut x = mod_pow(a % n, d, n);
        if x == 1 || x == n - 1 { continue; }
        for _ in 1..s {
            x = mod_mul(x, x, n);
            if x == n - 1 { continue 'bases; }
        }
        return false;
    }
    true
}

fn square_prime(n: u64) -> bool {
    let r = (n as f64).sqrt() as u64;
    [r.saturating_sub(1), r, r + 1]
        .iter().copied().any(|q| q.checked_mul(q) == Some(n) && prime(q))
}

fn inv_mod(a: u64, p: u64) -> u64 {
    // Every use has prime p and a nonzero residue.
    mod_pow(a % p, p - 2, p)
}

fn small_primes(limit: usize) -> Vec<u64> {
    let mut sieve = vec![true; limit + 1];
    sieve[0] = false;
    if limit >= 1 { sieve[1] = false; }
    let mut p = 2usize;
    while p * p <= limit {
        if sieve[p] {
            let mut j = p * p;
            while j <= limit { sieve[j] = false; j += p; }
        }
        p += 1;
    }
    (2..=limit).filter(|&q| sieve[q]).map(|q| q as u64).collect()
}

fn passes_nonprime_shifts(n_param: u64) -> bool {
    // Exact low-divisor classifications for shifts 5, 9, and 10.  Shift 8
    // is required to be prime by FORMS, and shifts 1,2,3,4,6,8,12 are then
    // automatic.  Shifts 7 and 11 are intentionally left for exact factorization.
    let a5 = 504 * n_param - 1;
    if !(prime(a5) || square_prime(a5) || (a5 % 5 == 0 && prime(a5 / 5))) {
        return false;
    }
    let a9 = 280 * n_param - 1;
    if !(prime(a9) || square_prime(a9)
        || (a9 % 3 == 0 && prime(a9 / 3))
        || (a9 % 9 == 0 && prime(a9 / 9))) {
        return false;
    }
    let a10 = 252 * n_param - 1;
    prime(a10) || square_prime(a10) || (a10 % 5 == 0 && prime(a10 / 5))
}

fn main() {
    let start: u64 = env::args().nth(1).unwrap_or_else(|| "1".into()).parse().unwrap();
    let end: u64 = env::args().nth(2).unwrap_or_else(|| "100000000".into()).parse().unwrap();
    let block_len: u64 = env::args().nth(3).unwrap_or_else(|| "5000000".into()).parse().unwrap();
    let sieve_bound: usize = env::args().nth(4).unwrap_or_else(|| "10000".into()).parse().unwrap();
    assert!(1 <= start && start <= end);

    let primes: Vec<u64> = small_primes(sieve_bound).into_iter()
        .filter(|p| SIEVE_FORMS.iter().all(|c| c % p != 0))
        .collect();
    let roots: Vec<(u64, [u64; 10])> = primes.iter().map(|&p| {
        let mut rs = [0u64; 10];
        for (i, &c) in SIEVE_FORMS.iter().enumerate() { rs[i] = inv_mod(c, p); }
        (p, rs)
    }).collect();
    // A 11*13*17*19 wheel avoids touching almost every integer in a block.
    // Subsequent prime filters repeatedly compact only the wheel survivors.
    const WHEEL: u64 = 11 * 13 * 17 * 19;
    let wheel_residues: Vec<u64> = (0..WHEEL).filter(|&n| {
        [11u64, 13, 17, 19].iter().all(|&p|
            SIEVE_FORMS.iter().all(|&c| c * n % p != 1))
    }).collect();
    let tail_roots: Vec<_> = roots.into_iter().filter(|(p, _)| *p > 19).collect();

    let clock = Instant::now();
    let mut lo = start;
    let mut sieve_survivors = 0u64;
    let mut tuples = 0u64;
    let mut shortlisted = 0u64;
    while lo <= end {
        let hi = end.min(lo.saturating_add(block_len - 1));
        let mut candidates = Vec::with_capacity(((hi - lo + 1) / 100) as usize);
        let lo_mod = lo % WHEEL;
        for &r in &wheel_residues {
            let delta = if r >= lo_mod { r - lo_mod } else { r + WHEEL - lo_mod };
            let mut n_param = lo + delta;
            while n_param <= hi {
                candidates.push(n_param);
                n_param += WHEEL;
            }
        }
        for &(p, ref rs) in &tail_roots {
            candidates.retain(|n_param| {
                let r = *n_param % p;
                !rs.contains(&r)
            });
        }
        sieve_survivors += candidates.len() as u64;
        for n_param in candidates {
            if !FORMS.iter().all(|&c| prime(c * n_param - 1)) { continue; }
            tuples += 1;
            if !passes_nonprime_shifts(n_param) { continue; }
            shortlisted += 1;
            println!("SHORTLIST N={n_param} n={} a7={} a11={}",
                2520 * n_param, 360 * n_param - 1, 2520 * n_param - 11);
        }
        eprintln!("progress hi={hi} sieve={sieve_survivors} tuples={tuples} shortlist={shortlisted} elapsed={:.1}s",
            clock.elapsed().as_secs_f64());
        if hi == u64::MAX { break; }
        lo = hi + 1;
    }
    eprintln!("DONE start={start} end={end} sieve={sieve_survivors} tuples={tuples} shortlist={shortlisted} elapsed={:.3}s",
        clock.elapsed().as_secs_f64());
}
