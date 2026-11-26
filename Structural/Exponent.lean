import Mathlib

/-!
# The exponent of the lever as a function of the cost per lift

An abstract form of `Structural.lifts_sq_le`. The level `N` carries the `m` lifts,
`m · L ≤ log N` with `L = log b`, and its allowed loss, times `log N`, must fit in a budget
proportional to the length `a` of the prime sum. In grh-compact the allowed loss at `N` is
`4 m f b`: one unit of loss per lift, and the budget is `f a L³`; this gives `m² b ≲ a L²`, so
with `a ≈ x b` at most about `√x` lifts and a saving `x^(−1/2)` (the critical line `1/2`).

If the loss at the level grew like `m^α` instead of `m`, the same two charges would give
`m^(α+1) b ≲ a L²`, at most about `x^(1/(α+1))` lifts, and a saving `x^(−1/(α+1))`, that is a
zero-free half-plane `Re s > 1 − 1/(α+1)`. For `α = 2` this is `2/3`.

L. Alpöge's remark (<https://alpo.ge/remark.pdf>, item 14) records that a precise computation of
the cost of each lift shows that the method would stop at `2/3` a priori, and that twisting and a
"division" were needed. This file proves only the algebra: `α = 1` gives `1/2`, `α = 2` gives
`2/3`. That the cost without the twists grows quadratically in `m` is a hypothesis of this
note (see notes/two_thirds.md), not a theorem of grh-compact.
-/

namespace Structural

/-- The lever with loss exponent `α`: if `m · L ≤ log N` and `c · m^α · b · log N ≤ c · a · L³`,
then `m^(α+1) · b ≤ a · L²`. -/
theorem lever_power {m a b L logN c : ℝ} (α : ℕ) (hc : 0 < c) (hb : 0 < b) (hL : 0 < L)
    (hm : 0 ≤ m) (hN : m * L ≤ logN) (hcharge : c * m ^ α * b * logN ≤ c * a * L ^ 3) :
    m ^ (α + 1) * b ≤ a * L ^ 2 := by
  have h0 : 0 ≤ c * m ^ α * b := mul_nonneg (mul_nonneg hc.le (pow_nonneg hm α)) hb.le
  have h1 : c * m ^ α * b * (m * L) ≤ c * a * L ^ 3 :=
    (mul_le_mul_of_nonneg_left hN h0).trans hcharge
  have h2 : (c * L) * (m ^ (α + 1) * b) ≤ (c * L) * (a * L ^ 2) := by
    calc (c * L) * (m ^ (α + 1) * b) = c * m ^ α * b * (m * L) := by ring
      _ ≤ c * a * L ^ 3 := h1
      _ = (c * L) * (a * L ^ 2) := by ring
  exact le_of_mul_le_mul_left h2 (mul_pos hc hL)

/-- With one unit of loss per lift (`α = 1`, grh-compact): `m² b ≤ a L²`. -/
theorem lever_one_half {m a b L logN c : ℝ} (hc : 0 < c) (hb : 0 < b) (hL : 0 < L) (hm : 0 ≤ m)
    (hN : m * L ≤ logN) (hcharge : c * m * b * logN ≤ c * a * L ^ 3) : m ^ 2 * b ≤ a * L ^ 2 :=
  lever_power 1 hc hb hL hm hN (by simpa using hcharge)

/-- With a loss quadratic in the number of lifts (`α = 2`): `m³ b ≤ a L²`, the exponent `2/3`. -/
theorem lever_two_thirds {m a b L logN c : ℝ} (hc : 0 < c) (hb : 0 < b) (hL : 0 < L) (hm : 0 ≤ m)
    (hN : m * L ≤ logN) (hcharge : c * m ^ 2 * b * logN ≤ c * a * L ^ 3) : m ^ 3 * b ≤ a * L ^ 2 :=
  lever_power 2 hc hb hL hm hN hcharge

end Structural
