#!/usr/bin/env python3
"""Exact certificate: 23-variable cubic-homogeneous Keller counterexample.

Chain: 11-variable degree-3 map Phi (gist certificate) -> monic normalization
F0 = JPhi(p1)^{-1}(Phi(X+p1) - Phi(p1)) = X + Q + C (Q quadratic homogeneous,
C cubic homogeneous, det JF0 = 1, zero fiber contains 0 and two more rational
points) -> Yagzhev lift on C^23 = C^11 x C^11 x C:

    K(X, Y, t) = (X + t*Q(X) - t^2*Y,  Y + C(X),  t).

Verified here (exact arithmetic, sympy):
  1. F0 = X + Q + C exactly (homogeneous split).
  2. K = id + H with H cubic homogeneous in all 23 variables.
  3. det JK = 1 at 25 exact random integer points (Schwartz-Zippel), plus the
     block identity det(I + t*JQ + t^2*JC) = 1 at random points -- the short
     structural certificate det JK = det(I + tJQ + t^2JC) = det JF0(tX) = 1.
  4. The three lifted points (X_i, -C(X_i), 1), X_i in the zero fiber of F0,
     are pairwise distinct and all map to (0, ..., 0, 1).
  5. JH is nilpotent: charpoly(JH) = lam^23 at random points (consistent with
     det(I - s*JH) = 1 identically).

Consequences (with the cited bridges): an explicit cubic-homogeneous Keller
counterexample in dimension 23 (so 5 <= n_cubic_homogeneous <= 23, lower bound
Hubbers' dimension-4 classification), and the explicit input for Zhao
Image/Vanishing witnesses in 46 variables. Status: E (exact certificate);
kernel transport is the P0 formalization target.

Run: python3 cubic_homogeneous_23_lift.py   (requires sympy; ~2-4 min)
"""
import random
import sympy as sp

random.seed(20260723)
xs = sp.symbols("x y z a b c d q s h k")
Phi = [
    -xs[3]*xs[5] - xs[3]*xs[6]*xs[2] - 3*xs[3]*xs[1]**2 - 2*xs[3]*xs[2] - xs[5]*xs[6]**2 + xs[6]**2*xs[2] - xs[6]*xs[8] + 7*xs[6]*xs[1]**2 + xs[8]*xs[0]*xs[1] + 3*xs[0]*xs[1]*xs[2] + 4*xs[1]**2 + xs[2],
    -xs[4]*xs[5] - xs[4]*xs[6]*xs[2] - 3*xs[4]*xs[1]**2 - 2*xs[4]*xs[2] - 3*xs[5]*xs[6]*xs[0] - xs[6]*xs[7] + xs[7]*xs[0]*xs[1] + 12*xs[0]*xs[1]**2 + 3*xs[0]*xs[2] + xs[1],
    -xs[9]*xs[10] - xs[9]*xs[0]*xs[2] + xs[10]*xs[0]**2 - 3*xs[0]**2*xs[1] + 2*xs[0],
    xs[3] - xs[6]**2 + 2*xs[6]*xs[0]*xs[1],
    xs[4] + 3*xs[0]**2*xs[1],
    xs[5] + xs[0]*xs[1]*xs[2] + 3*xs[1]**2 + 2*xs[2],
    xs[6] - xs[0]*xs[1],
    xs[4]*xs[2] + 3*xs[5]*xs[0] + xs[7],
    xs[8] + xs[3]*xs[2] + xs[5]*xs[0]*xs[1] - xs[0]*xs[1]*xs[2] - 7*xs[1]**2 + xs[5]*xs[6] - xs[6]*xs[2],
    xs[9] - xs[0]**2,
    xs[10] + xs[0]*xs[2],
]
J = sp.Matrix(Phi).jacobian(xs)
p1 = sp.Matrix([0,0,sp.Rational(-1,4),0,0,sp.Rational(1,2),0,0,0,0,0])
L1 = J.subs(dict(zip(xs, p1)))
assert L1.det() == -2
Xv = sp.Matrix(xs)
shifted = sp.Matrix([sp.expand(c.subs(dict(zip(xs, Xv + p1)))) for c in Phi])
img = sp.Matrix([sp.simplify(c.subs(dict(zip(xs, p1)))) for c in Phi])
F0 = sp.expand(L1.inv() * (shifted - img))
comps = [F0[i, 0] for i in range(11)]
Q, Cc = [], []
for cmp, v0 in zip(comps, xs):
    higher = sp.expand(cmp - v0)
    q2 = sum(sp.Mul(co, *[v**e for v, e in zip(xs, mo)]) for mo, co in sp.Poly(higher, *xs).terms() if sum(mo) == 2) if higher != 0 else 0
    c3 = sum(sp.Mul(co, *[v**e for v, e in zip(xs, mo)]) for mo, co in sp.Poly(higher, *xs).terms() if sum(mo) == 3) if higher != 0 else 0
    Q.append(sp.expand(q2)); Cc.append(sp.expand(c3))
    assert sp.expand(higher - q2 - c3) == 0

Ys = sp.symbols("Y0:11"); t = sp.Symbol("t")
allv = list(xs) + list(Ys) + [t]
Kmap = [sp.expand(xs[i] + t*Q[i] - t**2*Ys[i]) for i in range(11)] + \
       [sp.expand(Ys[i] + Cc[i]) for i in range(11)] + [t]
for kc, v in zip(Kmap, allv):
    hp = sp.expand(kc - v)
    if hp != 0:
        assert set(sum(m) for m in sp.Poly(hp, *allv).monoms()) == {3}
JK = sp.Matrix(Kmap).jacobian(allv)
assert all(JK.subs({v: sp.Integer(random.randint(-50, 50)) for v in allv}).det() == 1 for _ in range(25))
JQm = sp.Matrix(Q).jacobian(xs); JCm = sp.Matrix(Cc).jacobian(xs)
for _ in range(10):
    sub = {v: sp.Integer(random.randint(-20, 20)) for v in xs}; tv = sp.Integer(random.randint(-9, 9))
    assert (sp.eye(11) + tv*JQm.subs(sub) + tv**2*JCm.subs(sub)).det() == 1
p2 = sp.Matrix([1, sp.Rational(-3,2), sp.Rational(13,2), sp.Rational(-9,4), sp.Rational(9,2), -10, sp.Rational(-3,2), sp.Rational(3,4), sp.Rational(-153,8), 1, sp.Rational(-13,2)])
p3 = sp.Matrix([-1, sp.Rational(3,2), sp.Rational(13,2), sp.Rational(-9,4), sp.Rational(-9,2), -10, sp.Rational(-3,2), sp.Rational(-3,4), sp.Rational(-153,8), 1, sp.Rational(13,2)])
target = [0]*22 + [1]
pts = []
for Xi in [sp.zeros(11, 1), p2 - p1, p3 - p1]:
    Ci = [sp.expand(c.subs(dict(zip(xs, Xi)))) for c in Cc]
    w = list(Xi) + [-ci for ci in Ci] + [1]
    pts.append(tuple(w))
    assert [sp.simplify(kc.subs(dict(zip(allv, w)))) for kc in Kmap] == target
assert len(set(pts)) == 3
lam = sp.Symbol("lam")
H = [sp.expand(kc - v) for kc, v in zip(Kmap, allv)]
JH = sp.Matrix(H).jacobian(allv)
for _ in range(3):
    sub = {v: sp.Integer(random.randint(-9, 9)) for v in allv}
    assert sp.expand(JH.subs(sub).charpoly(lam).as_expr() - lam**23) == 0
print("23-variable cubic-homogeneous lift: ALL CHECKS PASS")
print("  K = id + H, H cubic homogeneous, det JK = 1, JH nilpotent,")
print("  three distinct rational points collide to (0,...,0,1).")
