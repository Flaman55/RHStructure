"""Change the number of lifts from m ~ x^(1/2) to m ~ x^theta in a copy of grh-compact (v3).

Usage: python3 -I patch_theta_v3.py <grh-compact dir> <num> <den>
v1 changed only m and the tower (2^s = m^22); the build then stopped at an exponent derived from
1/2 elsewhere: n(m) = k + m(t+1) ~ x^(5 + 1/2), written as 5.5. v2 rewrites every exponent that
is derived from theta through m or through the tower 2^s = m^22 (number of tops and of infinite
places ~ x^(22 theta), root discriminant ~ x^(22 theta +- 1), the period Omega ~ x^-(22 theta + 2),
log N ~ x^theta, the order of the chosen group ~ x^(21 + 22 theta), and the choice of m in
exists_data). Exponents that do not depend on m (r ~ x^5, h ~ x^40, ...) are left unchanged.
"""
import sys, os
root, num, den = sys.argv[1], sys.argv[2], sys.argv[3]
th = f"({num} / {den} : ℝ)"
edits = {
 "src/New/Data/AdmissibleData.lean": [("exp (logX / 2)", f"exp ({th} * logX)")],
 "src/New/Data/Magnitudes.lean": [
   ("HasLogBound D u D.m (D.logX / 2 + ite u 2 0)", f"HasLogBound D u D.m ({th} * D.logX + ite u 2 0)"),
   ("(towerDeg D.s) (11 * D.logX +", f"(towerDeg D.s) (22 * {th} * D.logX +"),
   ("HasLogBound D u D.f (11 * D.logX +", f"HasLogBound D u D.f (22 * {th} * D.logX +"),
   ("(D.n D.m) (5.5 * D.logX + ite u 12 0)", f"(D.n D.m) ((5 + {th}) * D.logX + ite u 12 0)")],
 "src/New/Data/ChosenPlaceLevels.lean": [("(.log D.chosenGroupOrder) (32 * D.logX)", f"(.log D.chosenGroupOrder) ((21 + 22 * {th}) * D.logX)")],
 "src/New/Data/DataExist.lean": [("N (x / 2).exp 2", f"N ({th} * x).exp 2")],
 "src/New/Trace/GoodIdempotent.lean": [("D.ϱ (D.logX / 2 + ite u 2 (-4))", f"D.ϱ ({th} * D.logX + ite u 2 (-4))")],
 "src/New/Seesaw/IndexTypes.lean": [
   ("(.log D.N) (D.logX / 2 + D.logB.log", f"(.log D.N) ({th} * D.logX + D.logB.log"),
   ("(v (P.ϖ D.s)) (ite u 12 10 * D.logX)", f"(v (P.ϖ D.s)) (ite u (22 * {th} + 1) (22 * {th} - 1) * D.logX)"),
   ("D.rootDisc (ite u 12 10 * D.logX)", f"D.rootDisc (ite u (22 * {th} + 1) (22 * {th} - 1) * D.logX)"),
   ("(P.bigOmega D.s) (ite u 0 (-13 * D.logX))", f"(P.bigOmega D.s) (ite u 0 (-(22 * {th} + 2) * D.logX))")],
}
for f, reps in edits.items():
    p = os.path.join(root, f); s = open(p, encoding="utf-8").read()
    for a, b in reps:
        n = s.count(a)
        if n == 0: sys.exit(f"pattern not found in {f}: {a}")
        s = s.replace(a, b)
        print(f"{f}: {n} x  {a}  ->  {b}")
    open(p, "w", encoding="utf-8").write(s)
