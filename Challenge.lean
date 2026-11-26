import Mathlib

/-!
# Advertised statements

This file is the small, trusted surface a reader should audit. It imports only Mathlib.

The two statements are classical consequences of the Riemann Hypothesis: the first is the
theorem of section 7 of H. von Koch, Sur la distribution des nombres premiers, Acta Math. 24
(1901), and the second follows from it (sharper forms with logarithms in place of `x^δ` and
`x^ε` are due to von Koch and to H. Cramér and are not formalized here). Here
they are stated without any hypothesis: in the accompanying development the Riemann Hypothesis
is the theorem `New.zeta_zeros_on_line New.grh` of grh-compact (Luke Sernau and colleagues at
Anthropic, with Claude), a rewriting of the Lean proof of RH and GRH by Levent Alpoge, with
Claude. Neither the Riemann Hypothesis nor its proof is a result of this submission.

The contribution of the submission is the deduction of the two statements in Lean from Mathlib's
`RiemannHypothesis`, by a contour shift of the smoothed Chebyshev function of
PrimeNumberTheoremAnd to the line `Re s = 1/2 + δ`, with a bound `ζ'/ζ ≪ log |t|` there obtained
from Borel–Carathéodory, and an interpolated bound on the Mellin transform of the smoothing that
keeps the exponent `1/2` (the bound used in PrimeNumberTheoremAnd alone would give `3/4`).

1. `Submission.chebyshev_psi_error`: for every `δ > 0`, `|ψ(x) - x| ≤ C x^(1/2 + δ)` for all
   large `x`, with `ψ` Mathlib's `Chebyshev.psi`.
2. `Submission.exists_prime_in_short_interval`: for every `ε > 0` and all large `x` there is a
   prime `p` with `x < p ≤ x + x^(1/2 + ε)`.
-/

theorem Submission.chebyshev_psi_error (δ : ℝ) (hδ : 0 < δ) :
    ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → |Chebyshev.psi x - x| ≤ C * x ^ (1 / 2 + δ) := by
  sorry

theorem Submission.exists_prime_in_short_interval (ε : ℝ) (hε : 0 < ε) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ x + x ^ (1 / 2 + ε) := by
  sorry
