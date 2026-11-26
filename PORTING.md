# PNTPort: files of PrimeNumberTheoremAnd used here

Source: PrimeNumberTheoremAnd, https://github.com/AlexKontorovich/PrimeNumberTheoremAnd,
commit e9906138410f8f76ca66b9bc252d0993f3ee348c (2026-11-24), Apache-2.0, built there on Lean
v4.36.0 and Mathlib fc4f59e. Copyright headers of the original files are kept.

The files are ported to Lean v4.35.0 and Mathlib 56a005855ea1 (the versions pinned by
grh-compact), so that both developments can be imported in one build.

Mechanical changes (script `scripts/port_pnt.py`): the LeanArchitect layer is removed (`import
Architect`, `@[blueprint ...]` attributes, `blueprint_comment` blocks); module paths
`PrimeNumberTheoremAnd.*` become `PNTPort.*`; a header line marking the file as changed.

Files: Auxiliary, EulerMaclaurin, Fourier, Mathlib/Algebra/Notation/Support,
Mathlib/Analysis/SpecialFunctions/Log/Basic, MediumPNT, MellinCalculus, Rectangle,
ResidueCalcOnRectangles, SmoothExistence, Sobolev, StrongPNT, ZetaBounds, ZetaConj (the import
closure of MediumPNT, plus StrongPNT for its Borel-Caratheodory and logarithm lemmas).

API adaptations to the older Mathlib (by file and line):
- all files: identifiers with `nnNorm` / `eNorm` are renamed back to the older Mathlib spelling
  `nnnorm` / `enorm` (ContinuousOn.nnnorm, enorm_eq_nnnorm, enorm_mul, nnnorm_div, nnnorm_real,
  hasFiniteIntegral_iff_enorm); done by `scripts/port_pnt.py`.
- StrongPNT.lean, `LogDerivZetaFinalBound` (line 1100 of the port): `div_left_inj₀` is
  `div_left_inj'` in the older Mathlib.
