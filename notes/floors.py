"""Exponent bookkeeping for the 2/3 question (log base x, polylog factors dropped).

Scales from grh-compact 72fead1: m = x^th lifts, f ~ x^(22 th) tops, b = x^beta with beta huge,
a ~ x b, t ~ k ~ x^5, budget B = f a (log b)^3, log N >= m log b. The pair terms of the triangle
(about m^2 of them) are placed on one floor at a time; the script reports the largest th for
which both the lever and the pair terms fit in the budget. Run: python3 -I floors.py
"""
import fractions
beta = 1e12
def budget(th): return 22*th + 1 + beta
def level(th): return th + 22*th + beta + th
def squares(th, floor):
    pairs = 2*th
    if floor == 'x': return pairs + 5 + 999
    if floor == 'b': return pairs + 22*th + beta
    if floor == 'N': return pairs + 22*th + beta + th
def edge(floor):
    lo, hi = 0.0, 1.0
    for _ in range(60):
        th = (lo + hi) / 2
        ok = level(th) <= budget(th) and squares(th, floor) <= budget(th)
        lo, hi = (th, hi) if ok else (lo, th)
    return lo
for fl in ['x', 'b', 'N']:
    th = edge(fl)
    print(f"pair terms on floor {fl}: max theta = {th:.4f}, edge = {fractions.Fraction(1 - th).limit_denominator(12)}")
