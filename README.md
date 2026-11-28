# RHStructure

Primes in short intervals from the Lean proof of the Riemann Hypothesis, and a structural reading
of that proof.

Paper: *Why the Lean proof of the Riemann Hypothesis works: Stepanov's balance in rings and arcs,
and where the exponent 1/2 is set*, Zenodo, https://doi.org/10.5281/zenodo.24572321 (source in
`paper/`).

Versions of the paper:

- Zenodo v1 (26 November 2026) is the PDF of commit `4abbeff` (md5 `2d1eceb828797411d511cf8489022a24`).
- The current `paper/` on GitHub (28 November 2026) adds Section 2, the analysis of the original
  Lean archive (leanprover-community/riemann-hypothesis, commit `6b1e1b8e`): the dependency walk
  from the five headline theorems and the split into the argument and the literature layer, with
  scripts and measurements in `scripts/original/`, and two lemmas in `Structural/RingsPadic.lean`
  (shared markers on the rings of ℓ measure ℓ-adic closeness; a twist's offsets are frozen on all
  rings of ℓ). The results of the note are unchanged; this revision is not yet on Zenodo.

The RH-conditional versions of the short-interval theorems are registered on Palomar as
`PALOMAR-2026-11-26-000056` (version 1), from https://github.com/Flaman55/RHShortIntervals at
commit `f9269d3`.

The Riemann Hypothesis has a Lean 4 proof by Levent Alpöge, with Claude
(<https://alpo.ge/remark.pdf>), rewritten as grh-compact by Luke Sernau and colleagues at
Anthropic, with Claude (<https://github.com/lsernau/grh-lean>, folder `grh-compact`, commit
`72fead1`, Apache-2.0). **Neither the Riemann Hypothesis nor its proof is a result of this
repository.** grh-compact is a Lake dependency, pinned and unchanged.

## Advertised statements

`Challenge.lean` imports only Mathlib and states two theorems; `Solution.lean` proves them.

- `Submission.chebyshev_psi_error`: for every `δ > 0` there are `C`, `x₀` with
  `|ψ(x) - x| ≤ C x^(1/2 + δ)` for `x ≥ x₀` (Mathlib's `Chebyshev.psi`).
- `Submission.exists_prime_in_short_interval`: for every `ε > 0` there is `x₀` such that for
  every real `x ≥ x₀` there is a prime `p` with `x < p ≤ x + x^(1/2 + ε)`.

Both are classical consequences of RH (H. von Koch, Acta Math. 24 (1901), §7; sharper forms with
logarithms by von Koch and by H. Cramér are not formalized here). The contribution is their
deduction in Lean from Mathlib's `RiemannHypothesis`; with RH supplied by grh-compact they hold
in Lean without hypotheses. Both depend only on `propext`, `Classical.choice`, `Quot.sound`.

## Proof (`Applications/`)

The smoothed Chebyshev function of PrimeNumberTheoremAnd is moved to the line
`Re s = 1/2 + δ` (`SmoothedChebyshevPull1`).

1. `RHLogDeriv.lean`: under RH, `ζ'/ζ(σ + it) ≪ log |t|` for `σ ≥ 1/2 + δ` (a holomorphic
   logarithm of `ζ` on a disk and the Borel–Carathéodory bound for its derivative).
2. `RHMellin.lean`: `|𝓜(s)| ≤ K ε^(-η) |s|^(-(1+η))` for the Mellin transform of the smoothing,
   interpolating `A/|s|` and `B/(ε|s|²)`; the second bound alone would give exponent `3/4`.
3. `RHPsi.lean`: the contour estimate, `ψ(x) = x + O(x^(1/2+δ))`.
4. `ShortInterval.lean`: with `ψ - θ = O(√x)`, `θ(x + x^(1/2+ε)) > θ(x)` for large `x`.

`PNTPort/` holds files of PrimeNumberTheoremAnd
(<https://github.com/AlexKontorovich/PrimeNumberTheoremAnd>, commit `e990613`, Apache-2.0)
ported to grh-compact's Mathlib with mechanical changes, listed in `PORTING.md`.

## Structural Window (`Applications/StructuralWindow.lean`, not advertised)

The window definitions of A. Flamandzki's Structural Window
(<https://github.com/Flaman55/Structural-Window>) are restated verbatim. There the
certificates of the width laws `⌈A^θ⌉` enter as citations, the sharpest at `θ = 0.52`. Here,
from the Lean RH and for every `θ > 1/2`: the certificate (`gapCertificate_eventually_of_RH`),
the general law on `⌈A^θ⌉ ≤ W ≤ A` (`generalLaw_partial`), the next prime after a large prime
`p` within `⌈p^θ⌉` (`nextPrime_gap_of_RH`), and a prime in every window of the march
`A_(k+1) = A_k + ⌈A_k^θ⌉` from some step on (`march`).

## Structural reading (`Structural/`, not advertised)

The note `paper/why_one_half.tex` explains, with Lean theorems built on the unchanged grh-compact,
why that proof succeeds and where it sets the exponent `1/2`: the prime-sum remainder as excess
turns of rings, the certificate of size against divisibility, and the lever
`m² · 4b ≤ a (log b)²` (one prime, the level, is charged twice by the number `m` of lifts). It
uses tools from the author's earlier work, among them ArcOrder
(<https://github.com/Flaman55/ArcOrder>).

## Build

Lean v4.35.0 (`lean-toolchain`); Mathlib 56a005855ea1 comes from grh-compact's manifest.
`lake build` builds grh-compact (one to two hours on 12 cores; see its README), the ported files
and this repository. The axioms of the main theorems are printed by `#print axioms`.

## License and attribution

Apache-2.0 (`LICENSE`). See `NOTICE` for grh-compact and PrimeNumberTheoremAnd. The Lean files and
texts were written with Claude (Anthropic) under the author's direction; the author ran every
build.
