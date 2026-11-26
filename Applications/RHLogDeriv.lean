import PNTPort.StrongPNT

/-!
# Step 1 of the short-interval application: `ζ'/ζ ≪ log |t|` to the right of `1/2` under RH

Under the Riemann Hypothesis (Mathlib's `RiemannHypothesis`), for every `δ ∈ (0, 1)` there is a
constant `C` with `‖ζ'(s)/ζ(s)‖ ≤ C log |t|` for `s = σ + it`, `σ ≥ 1/2 + δ`, `|t| ≥ 3`.

Proof: on the disk of radius `1 - δ/2` around `3/2 + it` the function `ζ` has no zeros (RH, and the
pole `s = 1` is at distance `≥ |t| > 1`), so it has a holomorphic logarithm `J` with `J(0) = 0`
(`LogOfAnalyticFunction'`); its real part is `log |ζ(s)| - log |ζ(3/2 + it)| ≤ log(7 + 2|t|) + c`
(`GlobalBound`, `ZetaFixedLowerBound`); the Borel–Carathéodory bound for the derivative
(`BorelCaratheodoryDeriv`) gives `|J'| = |ζ'/ζ| ≪ log |t|` on the disk of radius `1 - δ`. For
`σ ≥ 3/2` the Dirichlet series bounds `ζ'/ζ` by a constant
(`LogDerivZetaBdd_of_Re_ge_three_halves`). The cited lemmas are those of PrimeNumberTheoremAnd
(Apache-2.0), ported in `PNTPort/`.
-/

open Complex

namespace RHStructure

/-- Under RH, `ζ` does not vanish to the right of the critical line (away from `s = 1`). -/
theorem riemannZeta_ne_zero_of_RH (RH : RiemannHypothesis) {s : ℂ} (hs : 1 / 2 < s.re)
    (hs1 : s ≠ 1) : riemannZeta s ≠ 0 := by
  intro h
  have htriv : ¬∃ n : ℕ, s = -2 * (n + 1) := by
    rintro ⟨n, rfl⟩
    have hn : (0 : ℝ) ≤ n := n.cast_nonneg
    norm_num at hs <;> linarith
  have := RH s h htriv hs1
  linarith

/-- Step 1: under RH, `ζ'/ζ(σ + it) ≪_δ log |t|` for `σ ≥ 1/2 + δ`, `|t| ≥ 3`. -/
theorem logDerivZeta_bound_of_RH (RH : RiemannHypothesis) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ C > 0, ∀ (σ t : ℝ), 3 ≤ |t| → 1 / 2 + δ ≤ σ →
      ‖deriv riemannZeta (σ + t * I) / riemannZeta (σ + t * I)‖ ≤ C * Real.log |t| := by
  obtain ⟨C₁, hC₁⟩ := LogDerivZetaBdd_of_Re_ge_three_halves
  set r' : ℝ := 1 - δ with hr'
  set r : ℝ := 1 - δ / 2 with hr
  set R : ℝ := 1 - δ / 4 with hR
  have r'_pos : 0 < r' := by linarith
  have r'_lt_r : r' < r := by linarith
  have r_lt_R : r < R := by linarith
  have R_lt_one : R < 1 := by linarith
  set c₀ : ℝ := ‖riemannZeta 3 / riemannZeta (3 / 2)‖ with hc₀
  have hz3 : riemannZeta 3 ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  have hz32 : riemannZeta (3 / 2) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  have c₀_pos : 0 < c₀ := norm_pos_iff.mpr (div_ne_zero hz3 hz32)
  set L : ℝ := |Real.log c₀| with hL
  have L_nonneg : 0 ≤ L := abs_nonneg _
  set K : ℝ := 16 * r ^ 2 / (r - r') ^ 3 with hK
  have K_pos : 0 < K := by
    have h1 : 0 < r - r' := by linarith
    have h2 : 0 < r := by linarith
    exact div_pos (mul_pos (by norm_num) (pow_pos h2 2)) (pow_pos h1 3)
  have log3_pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have one_lt_log3 : 1 < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have := Real.exp_one_lt_d9
    linarith
  refine ⟨max C₁ 0 / Real.log 3 + K * (L + 4),
    add_pos_of_nonneg_of_pos (div_nonneg (le_max_right _ _) log3_pos.le)
      (mul_pos K_pos (by linarith)), ?_⟩
  intro σ t ht hσ
  have logt_ge : Real.log 3 ≤ Real.log |t| := Real.log_le_log (by norm_num) ht
  have logt_pos : 0 < Real.log |t| := lt_of_lt_of_le log3_pos logt_ge
  -- the constant part of the bound is dominated by its multiple of `log |t|`
  have part₁ : max C₁ 0 ≤ max C₁ 0 / Real.log 3 * Real.log |t| := by
    rw [div_mul_eq_mul_div, le_div_iff₀ log3_pos]
    exact mul_le_mul_of_nonneg_left logt_ge (le_max_right _ _)
  have part₂ : 0 ≤ K * (L + 4) * Real.log |t| :=
    mul_nonneg (mul_nonneg K_pos.le (by linarith)) logt_pos.le
  have one_le_logt : 1 ≤ Real.log |t| := one_lt_log3.le.trans logt_ge
  rcases le_or_gt (3 / 2) σ with hσ' | hσ'
  · -- far right: a constant bound
    have h := hC₁ (σ + t * I) (by simpa using hσ')
    calc ‖deriv riemannZeta (σ + t * I) / riemannZeta (σ + t * I)‖ ≤ C₁ := h
      _ ≤ max C₁ 0 := le_max_left _ _
      _ ≤ max C₁ 0 / Real.log 3 * Real.log |t| := part₁
      _ ≤ (max C₁ 0 / Real.log 3 + K * (L + 4)) * Real.log |t| := by
          rw [add_mul]; linarith
  -- the strip `1/2 + δ ≤ σ < 3/2`: Borel–Carathéodory on the disk around `3/2 + it`
  set B : ℂ → ℂ := fun w ↦ riemannZeta (w + 3 / 2 + I * t) with hB
  have notOne : ∀ w : ℂ, ‖w‖ ≤ 1 → w + 3 / 2 + I * t ≠ 1 := by
    intro w hw h1
    have him := congrArg Complex.im h1
    simp at him
    have hwim : |w.im| ≤ 1 := (Complex.abs_im_le_norm w).trans hw
    have : |t| ≤ 1 := by
      have : t = -w.im := by linarith
      rw [this, abs_neg]; exact hwim
    linarith
  have Banalytic : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R) := by
    intro w hw
    rw [Metric.mem_closedBall, dist_zero_right] at hw
    exact AnalyticAt.comp (analyticAt_riemannZeta (notOne w (hw.trans R_lt_one.le)))
      ((analyticAt_id.add analyticAt_const).add analyticAt_const)
  have Bnonzero : ∀ w ∈ Metric.closedBall (0 : ℂ) r, B w ≠ 0 := by
    intro w hw
    rw [Metric.mem_closedBall, dist_zero_right] at hw
    have hw1 : ‖w‖ ≤ 1 := hw.trans (by linarith)
    refine riemannZeta_ne_zero_of_RH RH ?_ (notOne w hw1)
    have hre : (w + 3 / 2 + I * t).re = w.re + 3 / 2 := by simp
    rw [hre]
    have := neg_abs_le w.re
    have := Complex.abs_re_le_norm w
    linarith
  obtain ⟨J, hJan, hJ0, hJderiv, hJre⟩ :=
    LogOfAnalyticFunction' r'_pos r'_lt_r r_lt_R Banalytic Bnonzero
  set M : ℝ := Real.log (7 + 2 * |t|) + L + 1 with hM
  have M_pos : 0 < M := by
    have : 0 < Real.log (7 + 2 * |t|) := Real.log_pos (by linarith [abs_nonneg t])
    linarith
  have B0 : B 0 = riemannZeta (3 / 2 + I * t) := by simp [hB]
  have lowB0 : Real.log c₀ ≤ Real.log ‖B 0‖ := by
    have hlow : c₀ ≤ ‖B 0‖ := by
      rw [B0, hc₀]
      exact_mod_cast ZetaFixedLowerBound t
    exact Real.log_le_log c₀_pos hlow
  have Jre_le : ∀ w ∈ Metric.ball (0 : ℂ) r, (J w).re ≤ M := by
    intro w hw
    rw [← hJre w hw]
    have hw' : ‖w‖ ≤ 1 := by
      rw [Metric.mem_ball, dist_zero_right] at hw; linarith
    have hBw : B w ≠ 0 := Bnonzero w (Metric.ball_subset_closedBall hw)
    have upper : Real.log ‖B w‖ ≤ Real.log (7 + 2 * |t|) :=
      Real.log_le_log (norm_pos_iff.mpr hBw) (GlobalBound hw' (by linarith))
    have : -Real.log c₀ ≤ L := neg_le_abs _
    linarith
  -- the point `σ + it` is `z + (3/2 + it)` with `z = σ - 3/2` real, `‖z‖ ≤ 1 - δ`
  set z : ℂ := ((σ - 3 / 2 : ℝ) : ℂ) with hz
  have hz_norm : ‖z‖ ≤ r' := by
    rw [hz, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
    linarith
  have hz_mem : z ∈ Metric.closedBall (0 : ℂ) r' := by
    rwa [Metric.mem_closedBall, dist_zero_right]
  have hpt : z + 3 / 2 + I * t = (σ : ℂ) + t * I := by
    rw [hz]; push_cast; ring
  have hBderiv : deriv B z = deriv riemannZeta ((σ : ℂ) + t * I) := by
    have hB' : B = fun w ↦ riemannZeta (w + (3 / 2 + I * t)) := by
      funext w; simp [hB, add_assoc]
    rw [hB', deriv_comp_add_const, ← add_assoc, hpt]
  have hBz : B z = riemannZeta ((σ : ℂ) + t * I) := by
    simp only [hB]; rw [hpt]
  have bc := BorelCaratheodoryDeriv M_pos r'_pos r'_lt_r (hJan.analyticOn) hJ0 Jre_le hz_mem
  rw [hJderiv z hz_mem, hBderiv, hBz] at bc
  have hMle : M ≤ (L + 4) * Real.log |t| := by
    have h7 : 7 + 2 * |t| ≤ 9 * |t| := by linarith
    have hlog7 : Real.log (7 + 2 * |t|) ≤ Real.log 9 + Real.log |t| := by
      rw [← Real.log_mul (by norm_num) (ne_of_gt (by linarith))]
      exact Real.log_le_log (by linarith [abs_nonneg t]) h7
    have hlog9 : Real.log 9 = 2 * Real.log 3 := by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]; norm_num
    have hLl : L ≤ L * Real.log |t| := le_mul_of_one_le_right L_nonneg one_le_logt
    rw [add_mul]
    linarith
  calc ‖deriv riemannZeta (σ + t * I) / riemannZeta (σ + t * I)‖
      ≤ 16 * M * r ^ 2 / (r - r') ^ 3 := bc
    _ = K * M := by rw [hK]; ring
    _ ≤ K * ((L + 4) * Real.log |t|) := mul_le_mul_of_nonneg_left hMle K_pos.le
    _ ≤ (max C₁ 0 / Real.log 3 + K * (L + 4)) * Real.log |t| := by
        have : 0 ≤ max C₁ 0 / Real.log 3 * Real.log |t| :=
          le_trans (le_max_right _ _) part₁
        have e : (max C₁ 0 / Real.log 3 + K * (L + 4)) * Real.log |t| =
            max C₁ 0 / Real.log 3 * Real.log |t| + K * ((L + 4) * Real.log |t|) := by ring
        rw [e]
        linarith

/-- `ζ'/ζ` along a vertical line `Re s = σ₁ ∈ (1/2, 1)` under RH: at most `D (1 + |t|)^η`, for
every `η > 0`. For `|t| ≥ 3` this is `logDerivZeta_bound_of_RH` with `log |t| ≤ |t|^η / η`; on
`|t| ≤ 3` the function is continuous (no zero by RH, no pole since `σ₁ < 1`), hence bounded. -/
theorem logDerivZeta_line_bound_of_RH (RH : RiemannHypothesis) {σ₁ : ℝ} (h1 : 1 / 2 < σ₁)
    (h2 : σ₁ < 1) {η : ℝ} (hη : 0 < η) :
    ∃ D, 0 ≤ D ∧ ∀ t : ℝ,
      ‖deriv riemannZeta (σ₁ + t * I) / riemannZeta (σ₁ + t * I)‖ ≤ D * (1 + |t|) ^ η := by
  obtain ⟨C, C_pos, hC⟩ := logDerivZeta_bound_of_RH RH (δ := σ₁ - 1 / 2) (by linarith)
    (by linarith)
  have hne : ∀ t : ℝ, (σ₁ : ℂ) + t * I ≠ 1 := by
    intro t h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hz : ∀ t : ℝ, riemannZeta ((σ₁ : ℂ) + t * I) ≠ 0 := fun t ↦
    riemannZeta_ne_zero_of_RH RH (by simp; linarith) (hne t)
  have hcont : ∀ t : ℝ, ContinuousAt
      (fun t : ℝ ↦ deriv riemannZeta ((σ₁ : ℂ) + t * I) / riemannZeta ((σ₁ : ℂ) + t * I)) t := by
    intro t
    have hg : ContinuousAt (fun s ↦ deriv riemannZeta s / riemannZeta s) ((σ₁ : ℂ) + t * I) :=
      ((analyticAt_riemannZeta (hne t)).deriv.continuousAt).div
        (differentiableAt_riemannZeta (hne t)).continuousAt (hz t)
    have hf : ContinuousAt (fun t : ℝ ↦ (σ₁ : ℂ) + t * I) t := by fun_prop
    exact ContinuousAt.comp (g := fun s ↦ deriv riemannZeta s / riemannZeta s)
      (f := fun t : ℝ ↦ (σ₁ : ℂ) + t * I) hg hf
  obtain ⟨C₀, hC₀⟩ := (isCompact_Icc (a := (-3 : ℝ)) (b := 3)).exists_bound_of_continuousOn
    (fun t _ ↦ (hcont t).continuousWithinAt)
  refine ⟨max C₀ 0 + C / η, add_nonneg (le_max_right _ _) (div_nonneg C_pos.le hη.le),
    fun t ↦ ?_⟩
  have hpow1 : 1 ≤ (1 + |t|) ^ η := Real.one_le_rpow (by linarith [abs_nonneg t]) hη.le
  have hsplit : (max C₀ 0 + C / η) * (1 + |t|) ^ η =
      max C₀ 0 * (1 + |t|) ^ η + C / η * (1 + |t|) ^ η := by ring
  have hA : 0 ≤ max C₀ 0 * (1 + |t|) ^ η :=
    mul_nonneg (le_max_right _ _) (by positivity)
  have hB : 0 ≤ C / η * (1 + |t|) ^ η :=
    mul_nonneg (div_nonneg C_pos.le hη.le) (by positivity)
  rw [hsplit]
  rcases le_or_gt 3 |t| with ht | ht
  · have hlog : Real.log |t| ≤ |t| ^ η / η := Real.log_le_rpow_div (abs_nonneg t) hη
    have hmono : |t| ^ η ≤ (1 + |t|) ^ η :=
      Real.rpow_le_rpow (abs_nonneg t) (by linarith) hη.le
    have := hC σ₁ t ht (by linarith)
    calc ‖deriv riemannZeta (σ₁ + t * I) / riemannZeta (σ₁ + t * I)‖ ≤ C * Real.log |t| := this
      _ ≤ C * (|t| ^ η / η) := mul_le_mul_of_nonneg_left hlog C_pos.le
      _ = C / η * |t| ^ η := by ring
      _ ≤ C / η * (1 + |t|) ^ η :=
          mul_le_mul_of_nonneg_left hmono (div_nonneg C_pos.le hη.le)
      _ ≤ _ := by linarith
  · have hmem : t ∈ Set.Icc (-3 : ℝ) 3 := by
      rw [abs_lt] at ht
      exact ⟨ht.1.le, ht.2.le⟩
    have := hC₀ t hmem
    calc ‖deriv riemannZeta (σ₁ + t * I) / riemannZeta (σ₁ + t * I)‖ ≤ C₀ := this
      _ ≤ max C₀ 0 := le_max_left _ _
      _ ≤ max C₀ 0 * (1 + |t|) ^ η := le_mul_of_one_le_right (le_max_right _ _) hpow1
      _ ≤ _ := by linarith

end RHStructure
