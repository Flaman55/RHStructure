import New.Columns.SizeEstimates
import New.Seesaw.IndexTypes
import Structural.Arcs

/-!
# The lever: where the exponent 1/2 is set in grh-compact

Ring reading. The argument of grh-compact uses a chain of `m` theta lifts; its final saving is
`1/m`. One prime, the level `N`, carries the bill of all `m` lifts:

* its size grows with `m`: `m · log b ≤ log N` (`Data.log_N_mem_Icc`), because the level pays the
  excesses of the `m` lifts (`Data.heightPerRow_le`);
* its allowed loss grows with `m`: `allowedLoss N = 4 · m · f · b` (`Data.allowedLoss`).

So the level is charged twice by `m`, and the charge must fit in the budget `f · a · (log b)³`
of the whole window (`Data.sum_allowedLoss_mul_log_le`). The result is a square law for the
lever, `m² · 4b ≤ a · (log b)²`; with `a ≈ x·b` this is `m² ≲ x (log b)²`, so `m ≲ √x` and the
saving `1/m` cannot beat `x^(−1/2)`.

All objects and lemmas used here are those of grh-compact (Luke Sernau and colleagues at
Anthropic, with Claude; a rewriting of Levent Alpöge's proof), commit 72fead1, Apache-2.0.
This file only reads them.
-/

open Real Finset

namespace Structural

variable {P : Parameters} (D : Data P)

/-- The level ring `N` lies far above the second scale `x₁`, so it is not one of the non-split
primes below `x₁` that carry the prime-sum losses. -/
lemma level_not_mem_nonsplitPrimes : D.N ∉ D.nonsplitPrimes := by
  intro h
  simp only [Data.nonsplitPrimes, Finset.mem_filter, Finset.mem_range] at h
  have hlt : (D.N : ℝ) < D.x₁ := Nat.lt_ceil.1 h.1
  have hN0 : (0 : ℝ) < D.N := by exact_mod_cast h.2.1.pos
  have hlog : Real.log D.N < D.logX₁ := by
    simpa [Data.x₁] using Real.log_lt_log hN0 hlt
  have hlow := D.log_N_mem_Icc.1
  have hB : (0 : ℝ) < D.logB := Data.HasLogBound.pos D
  have hX₁ : (0 : ℝ) < D.logX₁ := Data.HasLogBound.pos D
  have hm : (1 : ℝ) ≤ D.m := by exact_mod_cast (le_trans (by norm_num) D.le_m)
  have hs := D.scale
  -- log x₁ ≤ 10⁶ log x₁ ≤ log b ≤ m log b ≤ log N < log x₁
  nlinarith [hs.2.2.2.1, mul_le_mul_of_nonneg_right hm hB.le]

/-- The double charge of the level ring: its allowed loss `4·m·f·b`, times its size
`log N ≥ m · log b`, fits in the budget `f·a·(log b)³`. -/
theorem level_double_charge :
    4 * (D.m : ℝ) * D.f * D.b * (D.m * D.logB) ≤ D.budget := by
  have h := D.sum_allowedLoss_mul_log_le {D.N}
  rw [Finset.sum_singleton] at h
  have hA : D.allowedLoss D.N = 4 * D.m * D.f * D.b := by
    simp [Data.allowedLoss, level_not_mem_nonsplitPrimes D]
  rw [hA] at h
  have hf : (0 : ℝ) < D.f := Data.HasLogBound.pos D
  have hb : (0 : ℝ) < D.b := Real.exp_pos _
  have hpos : (0 : ℝ) ≤ 4 * (D.m : ℝ) * D.f * D.b := by positivity
  exact (mul_le_mul_of_nonneg_left D.log_N_mem_Icc.1 hpos).trans h

/-- The square law of the lever: `m² · 4b ≤ a · (log b)²`. With `a ≈ x·b` it reads
`m² ≲ x (log b)²`: at most about `√x` lifts, hence a saving of at most `x^(−1/2)`. -/
theorem lifts_sq_le : (D.m : ℝ) ^ 2 * (4 * D.b) ≤ D.a * D.logB ^ 2 := by
  have h := level_double_charge D
  have hf : (0 : ℝ) < D.f := Data.HasLogBound.pos D
  have hB : (0 : ℝ) < D.logB := Data.HasLogBound.pos D
  have key : (D.f * D.logB) * ((D.m : ℝ) ^ 2 * (4 * D.b)) ≤ (D.f * D.logB) * (D.a * D.logB ^ 2) := by
    simp only [Data.budget] at h
    nlinarith [h]
  exact le_of_mul_le_mul_left key (by positivity)

/-- The level in arcs: on the ring `B = ⌊b⌋₊`, the level `N` has a nonzero arc at every ring
`B ^ i` with `1 ≤ i ≤ m`. So `N` carries `m` levels of the ring `B`, the arc form of
`m · log b ≤ log N`. -/
theorem level_arcs {i : ℕ} (hi : i ≤ D.m) : 0 < arc D.N (⌊D.b⌋₊ ^ i) := by
  have hB : (0 : ℝ) < D.logB := Data.HasLogBound.pos D
  have hm : (1 : ℝ) ≤ D.m := by exact_mod_cast (le_trans (by norm_num) D.le_m)
  have hlow := D.log_N_mem_Icc.1
  have hb1 : (1 : ℝ) ≤ D.b := Real.one_le_exp hB.le
  have hN : (0 : ℝ) < D.N := by
    rcases (Nat.cast_nonneg D.N : (0 : ℝ) ≤ D.N).lt_or_eq with h | h
    · exact h
    · rw [← h, Real.log_zero] at hlow
      nlinarith [mul_le_mul_of_nonneg_right hm hB.le]
  have hfl : (1 : ℕ) ≤ ⌊D.b⌋₊ := Nat.le_floor (by simpa using hb1)
  have key : ((⌊D.b⌋₊ ^ i : ℕ) : ℝ) ≤ D.N := by
    push_cast
    calc (⌊D.b⌋₊ : ℝ) ^ i ≤ D.b ^ i :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le (by linarith)) i
      _ ≤ D.b ^ D.m := pow_le_pow_right₀ hb1 hi
      _ = Real.exp (D.m * D.logB) := by rw [Real.exp_nat_mul]
      _ ≤ Real.exp (Real.log D.N) := Real.exp_le_exp.2 hlow
      _ = D.N := Real.exp_log hN
  have key' : ⌊D.b⌋₊ ^ i ≤ D.N := by exact_mod_cast key
  exact Nat.div_pos key' (Nat.pow_pos hfl)

/-- The double charge per arc: the level pays `4·m·f·b · log b` for each of its `m` arcs on the
ring `⌊b⌋₊` (`level_arcs`), and the total fits in the budget. The count `m` enters twice: once
as the number of arcs, once in the price of each. This is the square of `lifts_sq_le`. -/
theorem level_charge_per_arc :
    ∑ _i ∈ Icc 1 D.m, 4 * (D.m : ℝ) * D.f * D.b * D.logB ≤ D.budget := by
  have h := level_double_charge D
  simp only [sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul]
  nlinarith [h]

end Structural
