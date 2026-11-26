import Applications.ShortInterval
import Structural.Spine

/-!
# Proved solutions

The statements of `Challenge.lean`, proved from Mathlib's `RiemannHypothesis` through
`Applications/` (steps 1-4), with the Riemann Hypothesis supplied by grh-compact
(`Structural.zeta_zeros_on_line`, which is `New.zeta_zeros_on_line New.grh`).
-/

theorem Submission.chebyshev_psi_error (δ : ℝ) (hδ : 0 < δ) :
    ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → |Chebyshev.psi x - x| ≤ C * x ^ (1 / 2 + δ) :=
  RHStructure.chebyshev_psi_of_RH Structural.zeta_zeros_on_line hδ

theorem Submission.exists_prime_in_short_interval (ε : ℝ) (hε : 0 < ε) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ x + x ^ (1 / 2 + ε) :=
  RHStructure.exists_prime_short_interval_of_RH Structural.zeta_zeros_on_line hε
