import PNTPort.MediumPNT

/-!
# Step 2 of the short-interval application: Mellin bounds for the smoothed indicator

`Smooth1 ν ε` is the smoothed indicator of `(0, 1]` of PrimeNumberTheoremAnd (`MellinCalculus`),
with Mellin transform `𝓜(Smooth1 ν ε)(s) = s⁻¹ · 𝓜ν(εs)` (`MellinOfSmooth1a`). Two bounds hold
for `σ₁ ≤ Re s ≤ 2`, uniformly in `ε ∈ (0, 1)`:

* `‖𝓜(Smooth1 ν ε)(s)‖ ≤ A / ‖s‖` (`mellin_smooth1_le_inv_norm`, from `MellinOfSmooth1a` and the
  boundedness of `𝓜ν` on `0 ≤ Re w ≤ 2`, `mellin_bounded`);
* `‖𝓜(Smooth1 ν ε)(s)‖ ≤ B / (ε ‖s‖²)` (`MellinOfSmooth1b`).

Interpolating, `‖𝓜(Smooth1 ν ε)(s)‖ ≤ K ε^(-η) ‖s‖^(-(1+η))` for every `η ∈ (0, 1)`
(`mellin_smooth1_interp`): integrable along a vertical line, at the price of a factor `ε^(-η)`.
PrimeNumberTheoremAnd uses the second bound alone, which costs a factor `1/ε`; with `ε = x^(-1/2)`
that would give only `x^(3/4)`.
-/

open Complex MeasureTheory Set Filter

namespace RHStructure

lemma rpow_sub_one_le_two {x a : ℝ} (hx : x ∈ Icc (1 / 2 : ℝ) 2) (ha0 : 0 ≤ a) (ha2 : a ≤ 2) :
    x ^ (a - 1) ≤ 2 := by
  obtain ⟨hx1, hx2⟩ := hx
  have xpos : 0 < x := by linarith
  rcases le_or_gt 1 x with h | h
  · calc x ^ (a - 1) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h (by linarith)
      _ = x := Real.rpow_one x
      _ ≤ 2 := hx2
  · calc x ^ (a - 1) ≤ x ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_ge xpos h.le (by linarith)
      _ = x⁻¹ := Real.rpow_neg_one x
      _ ≤ 2 := by rw [inv_le_comm₀ xpos (by norm_num)]; linarith

/-- The Mellin transform of a continuous `ν` supported in `[1/2, 2]` is bounded on the strip
`0 ≤ Re w ≤ 2`. -/
lemma mellin_bounded {ν : ℝ → ℝ} (contν : Continuous ν) (suppν : ν.support ⊆ Icc (1 / 2) 2) :
    ∃ C, 0 ≤ C ∧ ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 2 → ‖mellin (fun x ↦ (ν x : ℂ)) w‖ ≤ C := by
  have hcs : HasCompactSupport ν :=
    HasCompactSupport.intro isCompact_Icc (fun x hx ↦ by
      by_contra h
      exact hx (suppν h))
  have hint : Integrable (fun x ↦ 2 * |ν x|) :=
    ((contν.integrable_of_hasCompactSupport hcs).abs).const_mul 2
  refine ⟨∫ x in Ioi (0 : ℝ), 2 * |ν x|,
    setIntegral_nonneg measurableSet_Ioi (fun x _ ↦ by positivity), fun w h0 h2 ↦ ?_⟩
  unfold mellin
  refine norm_integral_le_of_norm_le hint.integrableOn ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun x hx ↦ ?_)
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.norm_real, Real.norm_eq_abs]
  have hre : (w - 1).re = w.re - 1 := by simp
  rw [hre]
  by_cases hν : ν x = 0
  · simp [hν]
  · exact mul_le_mul_of_nonneg_right (rpow_sub_one_le_two (suppν hν) h0 h2) (abs_nonneg _)

/-- `‖𝓜(Smooth1 ν ε)(s)‖ ≤ A / ‖s‖` for `0 < Re s ≤ 2`, uniformly in `ε ∈ (0, 1)`. -/
lemma mellin_smooth1_le_inv_norm {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Icc (1 / 2) 2) :
    ∃ A, 0 ≤ A ∧ ∀ (ε : ℝ), 0 < ε → ε < 1 → ∀ s : ℂ, 0 < s.re → s.re ≤ 2 →
      ‖mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) s‖ ≤ A * ‖s‖⁻¹ := by
  obtain ⟨C, C0, hC⟩ := mellin_bounded diffν.continuous suppν
  refine ⟨C, C0, fun ε ε0 ε1 s hs0 hs2 ↦ ?_⟩
  rw [MellinOfSmooth1a diffν suppν ε0 hs0, norm_mul, norm_inv, mul_comm (‖s‖⁻¹)]
  have hre : ((ε : ℂ) * s).re = ε * s.re := by simp
  refine mul_le_mul_of_nonneg_right (hC _ ?_ ?_) (inv_nonneg.mpr (norm_nonneg _))
  · rw [hre]; exact (mul_pos ε0 hs0).le
  · rw [hre]; nlinarith

/-- Interpolated Mellin bound: `‖𝓜(Smooth1 ν ε)(s)‖ ≤ K ε^(-η) ‖s‖^(-(1+η))` for
`σ₁ ≤ Re s ≤ 2`, `ε ∈ (0, 1)`. -/
lemma mellin_smooth1_interp {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Icc (1 / 2) 2) {σ₁ : ℝ} (hσ₁ : 0 < σ₁) {η : ℝ} (hη0 : 0 < η)
    (hη1 : η < 1) :
    ∃ K, 0 ≤ K ∧ ∀ (ε : ℝ), 0 < ε → ε < 1 → ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ 2 →
      ‖mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) s‖ ≤ K * ε ^ (-η) * ‖s‖ ^ (-(1 + η)) := by
  obtain ⟨A, A0, hA⟩ := mellin_smooth1_le_inv_norm diffν suppν
  obtain ⟨B, B0, hB⟩ := MellinOfSmooth1b diffν suppν
  refine ⟨A ^ (1 - η) * B ^ η, mul_nonneg (Real.rpow_nonneg A0 _) (Real.rpow_nonneg B0.le _),
    fun ε ε0 ε1 s hs1 hs2 ↦ ?_⟩
  set m := ‖mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) s‖ with hm
  set a := ‖s‖ with ha_def
  have ha : 0 < a := by
    rw [ha_def, norm_pos_iff]
    intro h
    rw [h] at hs1
    simp at hs1
    linarith
  have hm0 : 0 ≤ m := norm_nonneg _
  have h1 : m ≤ A * a⁻¹ := hA ε ε0 ε1 s (by linarith) hs2
  have h2 : m ≤ B * (ε * a ^ 2)⁻¹ := hB σ₁ hσ₁ s hs1 hs2 ε ε0 ε1
  have hinv1 : 0 ≤ A * a⁻¹ := mul_nonneg A0 (inv_nonneg.2 ha.le)
  have hprod : 0 ≤ ε * a ^ 2 := mul_nonneg ε0.le (sq_nonneg a)
  have e1 : (A * a⁻¹) ^ (1 - η) = A ^ (1 - η) * a ^ (-(1 - η)) := by
    rw [Real.mul_rpow A0 (inv_nonneg.2 ha.le), Real.inv_rpow ha.le, ← Real.rpow_neg ha.le]
  have e3 : ((a ^ 2) ^ η)⁻¹ = a ^ (-(2 * η)) := by
    rw [Real.rpow_neg ha.le, ← Real.rpow_natCast, ← Real.rpow_mul ha.le]
    norm_num
  have e2 : (B * (ε * a ^ 2)⁻¹) ^ η = B ^ η * (ε ^ (-η) * a ^ (-(2 * η))) := by
    rw [Real.mul_rpow B0.le (inv_nonneg.2 hprod), Real.inv_rpow hprod,
      Real.mul_rpow ε0.le (sq_nonneg a), mul_inv, ← Real.rpow_neg ε0.le, e3]
  have e4 : a ^ (-(1 - η)) * a ^ (-(2 * η)) = a ^ (-(1 + η)) := by
    rw [← Real.rpow_add ha]
    ring_nf
  calc m = m ^ (1 - η) * m ^ η := by
        rw [← Real.rpow_add' hm0 (by simp), sub_add_cancel, Real.rpow_one]
    _ ≤ (A * a⁻¹) ^ (1 - η) * (B * (ε * a ^ 2)⁻¹) ^ η :=
        mul_le_mul (Real.rpow_le_rpow hm0 h1 (by linarith))
          (Real.rpow_le_rpow hm0 h2 hη0.le) (Real.rpow_nonneg hm0 _)
          (Real.rpow_nonneg hinv1 _)
    _ = A ^ (1 - η) * B ^ η * ε ^ (-η) * a ^ (-(1 + η)) := by
        rw [e1, e2, ← e4]
        ring

end RHStructure
