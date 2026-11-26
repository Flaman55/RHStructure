import Structural.Certificate

/-!
# The spine: from the one-sided bound to the critical line (steps S4-S7)

Ring reading of the last steps of grh-compact:

* S4. The certificate, with `m ≈ √x` lifts (`Structural.lifts_sq_le` is the edge), gives a
  one-sided bound for the excess turns: `primeError d N₀ x ≤ x^(8ε − 1/2)` for large `x`
  (`one_sided_bound`, grh-compact's `eventually_primeError_le_rpow`).
* S5. The second scale `x₁` is taken in a long window where the other remainder is small
  (`second_scale_window`, grh-compact's `IsPolar.exists_window_sub_mul_le`).
* S6. Landau: a one-sided bound on a sum with non-negative weights (`Structural.weight_nonneg`)
  leaves no zero right of `β` (`landau_criterion`, grh-compact's
  `entireL_ne_zero_of_primeError_le`); hence no Dirichlet L-function vanishes in `Re s > 1/2`
  (`no_zero_right_of_half`, grh-compact's `New.grh`).
* S7. The functional equation folds `Re s > 1/2` onto `Re s < 1/2`, and the zeros are left on
  the line (`zeros_on_line`, `zeta_zeros_on_line`).

The zeros of the L-functions do not enter the argument; they appear only in its last statement.

All theorems here are grh-compact's (Luke Sernau and colleagues at Anthropic, with Claude; a
rewriting of Levent Alpöge's proof), commit 72fead1, Apache-2.0, restated under these names.
-/

open Filter

namespace Structural

/-- S4. One-sided bound for the excess turns: for `0 < ε < 1/100`, eventually
`primeError d N₀ x ≤ x^(8ε − 1/2)`. -/
theorem one_sided_bound (P : Parameters) {ε : ℝ} (h : 0 < ε / 6 ∧ ε < 1 / 100) :
    ∀ᶠ x in atTop, primeError P.d P.N₀ x ≤ x ^ (8 * ε + 2⁻¹ - 1) :=
  eventually_primeError_le_rpow P h

/-- S5. A good second scale in every long window (grh-compact's statement). -/
alias second_scale_window := IsPolar.exists_window_sub_mul_le

/-- S6. Landau's criterion: a one-sided bound for the excess turns gives a zero-free half-plane
(grh-compact's statement). -/
alias landau_criterion := entireL_ne_zero_of_primeError_le

/-- S6. No Dirichlet L-function vanishes in `Re s > 1/2`, the pole at `s = 1` excepted. -/
theorem no_zero_right_of_half : DirichletLNonvanishingRightOfHalf :=
  New.grh

/-- S7. Every zero of a Dirichlet L-function with `0 < Re s < 1` lies on `Re s = 1/2`. -/
theorem zeros_on_line : DirichletLZerosOnLine :=
  New.zeros_on_line New.grh

/-- S7. The Riemann hypothesis, in Mathlib's statement. -/
theorem zeta_zeros_on_line : RiemannHypothesis :=
  New.zeta_zeros_on_line New.grh

end Structural
