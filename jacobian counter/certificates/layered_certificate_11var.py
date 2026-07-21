#!/usr/bin/env python3
"""Layered verification certificate for the 11-variable cubic reduction
(gist Spacerat/08b4a43f6b6ca57178efabc220170ce8) of the Alpoge Jacobian
counterexample, replacing a stalled direct 11x11 symbolic Berkowitz determinant.

Layers:
  1. Random-point redundancy: det J(Phi) = -2 at 40 exact integer points
     (Schwartz-Zippel: deg det <= 22, points from [-1e4, 1e4]^11 -- detects any
     transcription error with overwhelming probability; NOT a symbolic proof).
  2. Structural factors: det of the linear part L = JPhi(0) is -2; the gist's
     own assertions (run separately) certify the construction chain
     (stabilizations + triangular automorphisms + two det -1 linear changes).
  3. Monic normalization closing the fidelity gap in the "F0 = X + Q + C"
     formulation: F0 := JPhi(p1)^{-1} . (Phi(X + p1) - Phi(p1)).
     NOTE: the linear factor must be JPhi(p1), NOT JPhi(0) -- the translation
     regenerates linear terms through the nonzero coordinates z=-1/4, c=1/2.
     Verified: F0 linear part == I exactly; F0 - X splits into homogeneous
     degrees {2,3} only; F0(0) = F0(p2-p1) = F0(p3-p1) = 0 with the three
     points pairwise distinct; det JF0 = 1 structurally
     (det JPhi(p1)^{-1} * det JPhi = (-1/2)*(-2)) and at 40 random points.

Run: python3 layered_certificate_11var.py   (requires sympy)
"""
import random
import sympy as sp

random.seed(20260722)
xs = sp.symbols("x y z a b c d q s h k")
x, y, z, a, b, c, d, q, s, h, k = xs
Phi = [
    -a*c - a*d*z - 3*a*y**2 - 2*a*z - c*d**2 + d**2*z - d*s + 7*d*y**2 + s*x*y + 3*x*y*z + 4*y**2 + z,
    -b*c - b*d*z - 3*b*y**2 - 2*b*z - 3*c*d*x - d*q + q*x*y + 12*x*y**2 + 3*x*z + y,
    -h*k - h*x*z + k*x**2 - 3*x**2*y + 2*x,
    a - d**2 + 2*d*x*y,
    b + 3*x**2*y,
    c + x*y*z + 3*y**2 + 2*z,
    d - x*y,
    b*z + 3*c*x + q,
    s + a*z + c*x*y - x*y*z - 7*y**2 + c*d - d*z,
    h - x**2,
    k + x*z,
]
J = sp.Matrix(Phi).jacobian(xs)

# Layer 1
assert all(J.subs({v: sp.Integer(random.randint(-10000, 10000)) for v in xs}).det() == -2
           for _ in range(40))
# Layer 2
L = sp.Matrix([[sp.expand(cmp).coeff(v, 1).subs({vv: 0 for vv in xs}) for v in xs] for cmp in Phi])
assert L.det() == -2
# Layer 3
p1 = sp.Matrix([0, 0, sp.Rational(-1, 4), 0, 0, sp.Rational(1, 2), 0, 0, 0, 0, 0])
L1 = J.subs(dict(zip(xs, p1)))
assert L1.det() == -2
Xv = sp.Matrix(xs)
shifted = sp.Matrix([sp.expand(cmp.subs(dict(zip(xs, Xv + p1)))) for cmp in Phi])
img = sp.Matrix([sp.simplify(cmp.subs(dict(zip(xs, p1)))) for cmp in Phi])
F0 = sp.expand(L1.inv() * (shifted - img))
comps = [F0[i, 0] for i in range(11)]
Lf = sp.Matrix([[sp.expand(cmp).coeff(v, 1).subs({vv: 0 for vv in xs}) for v in xs] for cmp in comps])
assert Lf == sp.eye(11)
for cmp, v0 in zip(comps, xs):
    higher = sp.expand(cmp - v0)
    if higher != 0:
        assert set(sum(m) for m in sp.Poly(higher, *xs).monoms()) <= {2, 3}
p2 = sp.Matrix([1, sp.Rational(-3,2), sp.Rational(13,2), sp.Rational(-9,4), sp.Rational(9,2), -10,
                sp.Rational(-3,2), sp.Rational(3,4), sp.Rational(-153,8), 1, sp.Rational(-13,2)])
p3 = sp.Matrix([-1, sp.Rational(3,2), sp.Rational(13,2), sp.Rational(-9,4), sp.Rational(-9,2), -10,
                sp.Rational(-3,2), sp.Rational(-3,4), sp.Rational(-153,8), 1, sp.Rational(13,2)])
ev = lambda pt: [sp.simplify(cmp.subs(dict(zip(xs, pt)))) for cmp in comps]
assert ev(sp.zeros(11, 1)) == [0]*11 and ev(p2 - p1) == [0]*11 and ev(p3 - p1) == [0]*11
assert (p2 - p1) != sp.zeros(11, 1) and (p3 - p1) != sp.zeros(11, 1) and (p2 - p1) != (p3 - p1)
Jf = sp.Matrix(comps).jacobian(xs)
assert all(Jf.subs({v: sp.Integer(random.randint(-10000, 10000)) for v in xs}).det() == 1
           for _ in range(40))
print("Layered certificate: ALL CHECKS PASS")
print("  det JPhi = -2 (40 exact random points; structural chain in gist)")
print("  Monic normalization F0 = JPhi(p1)^-1 (Phi(X+p1) - Phi(p1)):")
print("    F0 = X + Q + C, F0(0)=F0(p2-p1)=F0(p3-p1)=0, det JF0 = 1")
