//! Full square-root-prefix candidate search for Erdős #647.
//!
//! The kernel-verified reduction (Erdos647_DivisorSqrtDepthReduction.lean)
//! proves that verifying every shift budget for n = 2520*N reduces to the
//! prefix k < 2*sqrt(n): every later shift is automatically safe. So a
//! genuine candidate is EXACTLY an N whose value survives its entire
//! square-root prefix — and one computationally discovered survivor becomes
//! a short formal proof via the prefix theorem plus native_decide.
//!
//! Search structure (all filters are kernel-verified necessary conditions):
//!   - n = 2520*N, N in one of the 45 open residue classes mod 46189
//!     (the kernel-verified mod-46189 frontier; a superset of Hughes's 41);
//!   - the seven density forms (2520/k)*N - 1 for k in {1,2,3,4,6,8,12}
//!     must all be prime (checked by deterministic Miller-Rabin);
//!   - survivors get the full incremental prefix check: for k = 1 .. 2*sqrt(n),
//!     tau(n-k) <= k+2, rejecting at the first failure (tau via Pollard rho).
//!
//! This program is computational steering, not proof. Primality uses the
//! deterministic Miller-Rabin basis valid for all u64. A found survivor
//! must still be replayed in Lean before it is theorem-grade. Depth records
//! (first failing shift) are logged as empirical evidence for the
//! bounded-reuse investigation.
//!
//! Build:  rustc -O search_sqrt_prefix_survivor.rs -o search_sqrt_prefix.exe
//! Run:    search_sqrt_prefix.exe <t_start> <t_end> [depth_report_threshold]
//!         (N = 46189*t + r over the 45 residues r; default threshold 13)
//! Check:  search_sqrt_prefix.exe --check <N>   (validate one N directly)

use std::env;

const RESIDUES: [u64; 45] = [
    0, 858, 1287, 1716, 2431, 2574, 4862, 5291, 6149, 8151, 9009, 9867, 10582,
    12155, 12584, 13013, 13442, 16302, 17017, 17160, 18733, 19877, 20306,
    20735, 21164, 24310, 24453, 25168, 26884, 27170, 28028, 28457, 29315,
    29601, 31603, 32032, 32461, 35321, 36608, 37752, 38896, 39325, 40612,
    41470, 44187,
];

const FORM_COEFFS: [u64; 7] = [2520, 1260, 840, 630, 420, 315, 210];

fn mulmod(a: u64, b: u64, m: u64) -> u64 {
    ((a as u128 * b as u128) % m as u128) as u64
}

fn powmod(mut a: u64, mut e: u64, m: u64) -> u64 {
    let mut r: u64 = 1;
    a %= m;
    while e > 0 {
        if e & 1 == 1 {
            r = mulmod(r, a, m);
        }
        a = mulmod(a, a, m);
        e >>= 1;
    }
    r
}

/// Deterministic Miller-Rabin for all u64.
fn is_prime(n: u64) -> bool {
    if n < 2 {
        return false;
    }
    for p in [2u64, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37] {
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
    'witness: for a in [2u64, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37] {
        let mut x = powmod(a, d, n);
        if x == 1 || x == n - 1 {
            continue;
        }
        for _ in 0..s - 1 {
            x = mulmod(x, x, n);
            if x == n - 1 {
                continue 'witness;
            }
        }
        return false;
    }
    true
}

fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

/// Pollard rho: one nontrivial factor of composite odd n.
fn rho(n: u64) -> u64 {
    if n % 2 == 0 {
        return 2;
    }
    let mut c: u64 = 1;
    loop {
        let f = |x: u64| (mulmod(x, x, n) + c) % n;
        let (mut x, mut y, mut d) = (2u64, 2u64, 1u64);
        while d == 1 {
            x = f(x);
            y = f(f(y));
            d = gcd(x.abs_diff(y), n);
        }
        if d != n {
            return d;
        }
        c += 1;
    }
}

/// Divisor count via recursive factorization.
fn tau(n: u64) -> u64 {
    if n == 1 {
        return 1;
    }
    // Collect prime factors with multiplicity.
    let mut stack = vec![n];
    let mut primes: Vec<(u64, u32)> = Vec::new();
    while let Some(m) = stack.pop() {
        if m == 1 {
            continue;
        }
        if is_prime(m) {
            match primes.iter_mut().find(|(p, _)| *p == m) {
                Some((_, e)) => *e += 1,
                None => primes.push((m, 1)),
            }
            continue;
        }
        let d = rho(m);
        stack.push(d);
        stack.push(m / d);
    }
    primes.iter().map(|(_, e)| (*e as u64) + 1).product()
}

fn isqrt(n: u64) -> u64 {
    let mut r = (n as f64).sqrt() as u64;
    while r * r > n {
        r -= 1;
    }
    while (r + 1) * (r + 1) <= n {
        r += 1;
    }
    r
}

/// Full prefix check: returns first failing shift, or None if N is a
/// genuine square-root-prefix survivor (i.e. a candidate!).
fn prefix_check(n_val: u64) -> Option<u64> {
    let limit = 2 * isqrt(n_val);
    for k in 1..limit {
        if k >= n_val {
            break;
        }
        if tau(n_val - k) > k + 2 {
            return Some(k);
        }
    }
    None
}

fn seven_form_filter(n_param: u64) -> bool {
    // Cheapest-rejection order: densest form first.
    for c in FORM_COEFFS {
        if !is_prime(c * n_param - 1) {
            return false;
        }
    }
    true
}

fn check_one(n_param: u64) {
    let n_val = 2520 * n_param;
    println!(
        "N = {} (n = {}), residue {} mod 46189, seven-form: {}",
        n_param,
        n_val,
        n_param % 46189,
        seven_form_filter(n_param)
    );
    match prefix_check(n_val) {
        Some(k) => println!("  first failing shift: k = {} (tau = {})", k, tau(n_val - k)),
        None => println!("  *** FULL SQRT-PREFIX SURVIVOR — CANDIDATE ***"),
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() >= 3 && args[1] == "--check" {
        check_one(args[2].parse().expect("bad N"));
        return;
    }
    let t_start: u64 = args.get(1).map(|s| s.parse().unwrap()).unwrap_or(0);
    let t_end: u64 = args.get(2).map(|s| s.parse().unwrap()).unwrap_or(t_start + 1000);
    let threshold: u64 = args.get(3).map(|s| s.parse().unwrap()).unwrap_or(13);
    let mut tested: u64 = 0;
    let mut seven_survivors: u64 = 0;
    let mut best_depth: u64 = 0;
    for t in t_start..t_end {
        for r in RESIDUES {
            let n_param = 46189 * t + r;
            if n_param == 0 {
                continue;
            }
            tested += 1;
            if !seven_form_filter(n_param) {
                continue;
            }
            seven_survivors += 1;
            let n_val = 2520 * n_param;
            match prefix_check(n_val) {
                Some(k) => {
                    if k > best_depth {
                        best_depth = k;
                    }
                    if k >= threshold {
                        println!("DEPTH {} at N = {} (n = {})", k, n_param, n_val);
                    }
                }
                None => {
                    println!("*** CANDIDATE: N = {} (n = {}) ***", n_param, n_val);
                }
            }
        }
        if t % 100_000 == 0 && t > t_start {
            eprintln!(
                "t = {} | tested {} | seven-form survivors {} | best depth {}",
                t, tested, seven_survivors, best_depth
            );
        }
    }
    println!(
        "DONE t=[{},{}) tested {} seven-form-survivors {} best-depth {}",
        t_start, t_end, tested, seven_survivors, best_depth
    );
}
