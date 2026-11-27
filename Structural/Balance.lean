import Mathlib

/-!
# The balance of the proof under the two conditions kept by the twists

A model of the bookkeeping of grh-compact (Levent Alpöge's proof, compact rewriting by Luke
Sernau and colleagues at Anthropic, both with Claude), written for the open question of the paper
"why the method would stop at 2/3 without the twists". Notation as in the paper: `m` lifts,
`m = X^θ`, saving `1/m`.

The twists of `exists_isFitFamily` keep two conditions:

* D (floor b): the denominators of each lift stay within `B₀` (`IsFitFamily.denominator_le`);
* H (floor x): each square of the triangle of lifts and descents has height `≤ x^999`
  (`IsFitFamily.height_le`), so the about `m²` pair terms are negligible.

The equations of the proof combine to `m · rem ≤ K + E_D` (Theorems A, B, C) and, at the level,
`m^(α+1) ≤ X` (the lever, `Structural.lever_power`). In grh-compact `E_D = 0` and `α = 1`.

Model assumptions (not theorems of grh-compact): if D fails, `E_D ≤ e · m`; if H fails, the pair
terms are charged at the level and `α = 2`. Under these assumptions the four cases are:

| D | H | lever          | edge |
|---|---|----------------|------|
| ✓ | ✓ | `θ ≤ 1/2`      | 1/2  |
| ✓ | ✗ | `θ ≤ 1/3`      | 2/3  |
| ✗ | · | bound `≤ K/m + e`, no decay | none |

This file proves only the algebra of the table.
-/

namespace Structural

/-- With condition D (`E_D = 0`): the remainder is at most `K / m`; the saving is `1/m`. -/
theorem saving_with_D {m rem K : ℝ} (hm : 0 < m) (h : m * rem ≤ K) : rem ≤ K / m := by
  rw [le_div_iff₀ hm]; linarith

/-- Without condition D (`E_D ≤ e · m`): the bound is `K / m + e`, which does not decay in `m`. -/
theorem saving_without_D {m rem K e : ℝ} (hm : 0 < m) (h : m * rem ≤ K + e * m) :
    rem ≤ K / m + e := by
  have h' : rem ≤ (K + e * m) / m := by rw [le_div_iff₀ hm]; linarith
  rwa [add_div, mul_div_assoc, div_self hm.ne', mul_one] at h'

/-- The lever in exponents: if `m = X^θ` and `m^(α+1) ≤ X` with `X > 1`, then `θ ≤ 1/(α+1)`. -/
theorem exponent_of_lever {X θ : ℝ} (α : ℕ) (hX : 1 < X) (h : (X ^ θ) ^ (α + 1) ≤ X) :
    θ ≤ 1 / ((α : ℝ) + 1) := by
  have h1 : (X ^ θ) ^ (α + 1) = X ^ (θ * ((α : ℝ) + 1)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : (0 : ℝ) ≤ X)]
    push_cast
    ring_nf
  have h' : X ^ (θ * ((α : ℝ) + 1)) ≤ X ^ (1 : ℝ) := by rw [Real.rpow_one, ← h1]; exact h
  have h2 := (Real.rpow_le_rpow_left_iff hX).mp h'
  rw [le_div_iff₀ (by positivity)]
  exact h2

/-- Both conditions (`α = 1`, grh-compact): `θ ≤ 1/2`, the edge `1/2`. -/
theorem edge_both {X θ : ℝ} (hX : 1 < X) (h : (X ^ θ) ^ 2 ≤ X) : θ ≤ 1 / 2 := by
  have := exponent_of_lever 1 hX (by simpa using h)
  norm_num at this ⊢; linarith

/-- Condition D only (`α = 2` in the model): `θ ≤ 1/3`, the edge `2/3`. -/
theorem edge_D_only {X θ : ℝ} (hX : 1 < X) (h : (X ^ θ) ^ 3 ≤ X) : θ ≤ 1 / 3 := by
  have := exponent_of_lever 2 hX (by simpa using h)
  norm_num at this ⊢; linarith

end Structural
