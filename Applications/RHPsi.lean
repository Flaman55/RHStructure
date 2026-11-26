import Applications.RHLogDeriv
import Applications.RHMellin
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# Step 3 of the short-interval application: `ψ(x) = x + O(x^(1/2+δ))` under RH

The smoothed Chebyshev function of PrimeNumberTheoremAnd, `SmoothedChebyshev ν ε X`, is the
integral of `-ζ'/ζ(s) 𝓜(Smooth1 ν ε)(s) X^s` on the line `Re s = 1 + 1/log X`. Under RH the
integrand is holomorphic on `Re s > 1/2` except at `s = 1`, and `SmoothedChebyshevPull1` moves the
line to `Re s = σ₁ = 1/2 + δ'/2` at height `T`:

  `SmoothedChebyshev = I₁ - I₂ + I₃₇ + I₈ + I₉ + 𝓜(Smooth1 ν ε)(1) X`.

With `ε = X^(-1/2)` and `T = X`:
* `I₃₇` (the new line) is at most `M ε^(-η) X^σ₁ = M X^(1/2+δ')` (`I37_bound`, from
  `logDerivZeta_line_bound_of_RH` and `mellin_smooth1_interp`);
* `I₂`, `I₈` (horizontal segments) are at most `M log T (εT²)⁻¹ X² = M X^(1/2) log X`
  (`I28_bound`, from `logDerivZeta_bound_of_RH` and `MellinOfSmooth1b`);
* `I₁`, `I₉` (tails of the old line) are at most `C X log X/(εT) = C X^(1/2) log X` (`I1Bound`,
  `I9Bound`);
* `𝓜(1) - 1 = O(ε)` (`MellinOfSmooth1cExplicit`) and `SmoothedChebyshev - ψ = O(εX log X)`
  (`SmoothedChebyshevClose`) cost `O(X^(1/2) log X)`.
-/

open Complex MeasureTheory Set Filter
open scoped Interval

namespace RHStructure

lemma integrand_norm (ν : ℝ → ℝ) (ε X : ℝ) (s : ℂ) (hX : 0 < X) :
    ‖SmoothedChebyshevIntegrand ν ε X s‖ =
      ‖deriv riemannZeta s / riemannZeta s‖ * ‖mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) s‖ *
        X ^ s.re := by
  simp only [SmoothedChebyshevIntegrand]
  rw [norm_mul, norm_mul, neg_div, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hX]

/-- The integral on the new line `Re s = σ₁`. -/
lemma I37_bound (RH : RiemannHypothesis) {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Icc (1 / 2) 2) {σ₁ : ℝ} (h1 : 1 / 2 < σ₁) (h2 : σ₁ < 1) {η : ℝ}
    (hη0 : 0 < η) (hη1 : η < 1) :
    ∃ M, 0 ≤ M ∧ ∀ (ε : ℝ), 0 < ε → ε < 1 → ∀ (X : ℝ), 1 < X → ∀ (T : ℝ), 0 ≤ T →
      ‖I₃₇ ν ε T X σ₁‖ ≤ M * ε ^ (-η) * X ^ σ₁ := by
  obtain ⟨D, D0, hD⟩ := logDerivZeta_line_bound_of_RH RH h1 h2 (η := η / 2) (by linarith)
  obtain ⟨K, K0, hK⟩ := mellin_smooth1_interp diffν suppν (σ₁ := σ₁) (by linarith) hη0 hη1
  have hint : Integrable (fun t : ℝ ↦ (1 + ‖t‖) ^ (-(1 + η / 2))) :=
    integrable_one_add_norm (by simp only [Module.finrank_self, Nat.cast_one]; linarith)
  set J := ∫ t : ℝ, (1 + ‖t‖) ^ (-(1 + η / 2)) with hJ
  have J0 : 0 ≤ J := integral_nonneg (fun t ↦ by positivity)
  set cs := (σ₁ / 2) ^ (-(1 + η)) with hcs
  have cs0 : 0 ≤ cs := Real.rpow_nonneg (by linarith) _
  set c := ‖(1 / (2 * Real.pi * I) : ℂ)‖ with hc
  have c0 : 0 ≤ c := norm_nonneg _
  refine ⟨c * (D * K * cs * J), mul_nonneg c0 (mul_nonneg (mul_nonneg (mul_nonneg D0 K0) cs0) J0),
    fun ε ε0 ε1 X hX T hT ↦ ?_⟩
  set G := D * K * cs * ε ^ (-η) * X ^ σ₁ with hG
  have G0 : 0 ≤ G := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg D0 K0) cs0)
    (Real.rpow_nonneg ε0.le _)) (Real.rpow_nonneg (by linarith) _)
  have hpt : ∀ t : ℝ, ‖SmoothedChebyshevIntegrand ν ε X (σ₁ + t * I)‖ ≤
      G * (1 + ‖t‖) ^ (-(1 + η / 2)) := by
    intro t
    set s : ℂ := σ₁ + t * I with hs
    have hre : s.re = σ₁ := by simp [hs]
    have him : s.im = t := by simp [hs]
    rw [integrand_norm ν ε X s (by linarith), hre]
    have hζ := hD t
    have hM := hK ε ε0 ε1 s (by rw [hre]) (by rw [hre]; linarith)
    have ht0 : 0 ≤ |t| := abs_nonneg t
    have hs_lb : σ₁ * (1 + |t|) / 2 ≤ ‖s‖ := by
      have a1 : |s.re| ≤ ‖s‖ := Complex.abs_re_le_norm s
      have a2 : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
      rw [hre, abs_of_pos (by linarith)] at a1
      rw [him] at a2
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - σ₁) ht0]
    have hpos : 0 < σ₁ * (1 + |t|) / 2 :=
      div_pos (mul_pos (by linarith) (by linarith)) two_pos
    have hpow : ‖s‖ ^ (-(1 + η)) ≤ cs * (1 + |t|) ^ (-(1 + η)) := by
      calc ‖s‖ ^ (-(1 + η)) ≤ (σ₁ * (1 + |t|) / 2) ^ (-(1 + η)) :=
            Real.rpow_le_rpow_of_nonpos hpos hs_lb (by linarith)
        _ = cs * (1 + |t|) ^ (-(1 + η)) := by
            rw [hcs, show σ₁ * (1 + |t|) / 2 = (σ₁ / 2) * (1 + |t|) by ring,
              Real.mul_rpow (show (0 : ℝ) ≤ σ₁ / 2 by linarith) (show (0 : ℝ) ≤ 1 + |t| by linarith)]
    have hcomb : (1 + |t|) ^ (η / 2) * (1 + |t|) ^ (-(1 + η)) = (1 + ‖t‖) ^ (-(1 + η / 2)) := by
      rw [← Real.rpow_add (show (0 : ℝ) < 1 + |t| by linarith), Real.norm_eq_abs]
      congr 1
      ring
    have hKε : 0 ≤ K * ε ^ (-η) := mul_nonneg K0 (Real.rpow_nonneg ε0.le _)
    have hDt : 0 ≤ D * (1 + |t|) ^ (η / 2) := mul_nonneg D0 (by positivity)
    have hXσ : 0 ≤ X ^ σ₁ := Real.rpow_nonneg (by linarith) _
    calc ‖deriv riemannZeta s / riemannZeta s‖ * ‖mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) s‖ *
          X ^ σ₁
        ≤ (D * (1 + |t|) ^ (η / 2)) * (K * ε ^ (-η) * (cs * (1 + |t|) ^ (-(1 + η)))) *
          X ^ σ₁ := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul hζ ?_ (norm_nonneg _) hDt) hXσ
          exact hM.trans (mul_le_mul_of_nonneg_left hpow hKε)
      _ = G * ((1 + |t|) ^ (η / 2) * (1 + |t|) ^ (-(1 + η))) := by rw [hG]; ring
      _ = G * (1 + ‖t‖) ^ (-(1 + η / 2)) := by rw [hcomb]
  unfold I₃₇
  rw [norm_mul, norm_mul, Complex.norm_I, one_mul, ← hc]
  have hle : ‖∫ t in (-T)..T, SmoothedChebyshevIntegrand ν ε X (σ₁ + t * I)‖ ≤
      ∫ t in (-T)..T, G * (1 + ‖t‖) ^ (-(1 + η / 2)) :=
    intervalIntegral.norm_integral_le_of_norm_le (by linarith)
      (Filter.Eventually.of_forall fun t _ ↦ hpt t) ((hint.const_mul G).intervalIntegrable)
  have hle2 : ∫ t in (-T)..T, G * (1 + ‖t‖) ^ (-(1 + η / 2)) ≤ G * J := by
    rw [intervalIntegral.integral_of_le (by linarith), hJ, ← integral_const_mul]
    exact setIntegral_le_integral (hint.const_mul G)
      (Filter.Eventually.of_forall fun t ↦ mul_nonneg G0 (by positivity))
  calc c * ‖∫ t in (-T)..T, SmoothedChebyshevIntegrand ν ε X (σ₁ + t * I)‖
      ≤ c * (G * J) := mul_le_mul_of_nonneg_left (hle.trans hle2) c0
    _ = c * (D * K * cs * J) * ε ^ (-η) * X ^ σ₁ := by rw [hG]; ring

/-- The two horizontal segments at height `±T`. -/
lemma I28_bound (RH : RiemannHypothesis) {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Icc (1 / 2) 2) {σ₁ : ℝ} (h1 : 1 / 2 < σ₁) (h2 : σ₁ < 1) :
    ∃ M, 0 ≤ M ∧ ∀ (ε : ℝ), 0 < ε → ε < 1 → ∀ (X : ℝ), 3 ≤ X → ∀ (T : ℝ), 3 ≤ T →
      ‖I₂ ν ε T X σ₁‖ ≤ M * Real.log T * (ε * T ^ 2)⁻¹ * X ^ 2 ∧
      ‖I₈ ν ε T X σ₁‖ ≤ M * Real.log T * (ε * T ^ 2)⁻¹ * X ^ 2 := by
  obtain ⟨CL, CL0, hCL⟩ := logDerivZeta_bound_of_RH RH (δ := σ₁ - 1 / 2) (by linarith)
    (by linarith)
  obtain ⟨B, B0, hB⟩ := MellinOfSmooth1b diffν suppν
  set c := ‖(1 / (2 * Real.pi * I) : ℂ)‖ with hc
  have c0 : 0 ≤ c := norm_nonneg _
  refine ⟨c * 2 * CL * B, mul_nonneg (mul_nonneg (mul_nonneg c0 two_pos.le) CL0.le) B0.le,
    fun ε ε0 ε1 X hX T hT ↦ ?_⟩
  have one_lt_log3 : 1 < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have := Real.exp_one_lt_d9
    linarith
  have hlogX : 1 ≤ Real.log X := (one_lt_log3.trans_le (Real.log_le_log (by norm_num) hX)).le
  set σ₀ := 1 + (Real.log X)⁻¹ with hσ₀
  have hσ₀2 : σ₀ ≤ 2 := by
    have : (Real.log X)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hlogX
    linarith
  have hσ₁σ₀ : σ₁ ≤ σ₀ := by
    have : 0 < (Real.log X)⁻¹ := inv_pos.mpr (by linarith)
    linarith
  set P := CL * Real.log T * (B * (ε * T ^ 2)⁻¹) * X ^ 2 with hP
  have hT0 : 0 < T := by linarith
  have hεT : 0 < ε * T ^ 2 := by positivity
  have P0 : 0 ≤ P := by
    have h1 : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
    have h2 : 0 ≤ (ε * T ^ 2)⁻¹ := inv_nonneg.mpr hεT.le
    exact mul_nonneg (mul_nonneg (mul_nonneg CL0.le h1) (mul_nonneg B0.le h2)) (sq_nonneg X)
  -- pointwise bound on a horizontal segment at height `τ`, `|τ| = T`
  have hpt : ∀ (σ τ : ℝ), |τ| = T → σ ∈ Ι σ₁ σ₀ →
      ‖SmoothedChebyshevIntegrand ν ε X (σ + τ * I)‖ ≤ P := by
    intro σ τ hτ hσ
    rw [Set.uIoc_of_le hσ₁σ₀] at hσ
    obtain ⟨hσa, hσb⟩ := hσ
    set s : ℂ := σ + τ * I with hs
    have hre : s.re = σ := by simp [hs]
    have him : s.im = τ := by simp [hs]
    rw [integrand_norm ν ε X s (by linarith), hre]
    have hζ : ‖deriv riemannZeta s / riemannZeta s‖ ≤ CL * Real.log T := by
      have := hCL σ τ (by rw [hτ]; exact hT) (by linarith)
      rwa [hτ] at this
    have hM : ‖mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) s‖ ≤ B * (ε * T ^ 2)⁻¹ := by
      have h := hB σ₁ (by linarith) s (by rw [hre]; linarith) (by rw [hre]; linarith) ε ε0 ε1
      refine h.trans (mul_le_mul_of_nonneg_left ?_ B0.le)
      have hTs : T ≤ ‖s‖ := by
        have := Complex.abs_im_le_norm s
        rwa [him, hτ] at this
      exact inv_anti₀ hεT (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hT0.le hTs 2) ε0.le)
    have hXs : X ^ σ ≤ X ^ 2 := by
      rw [← Real.rpow_two]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
    calc ‖deriv riemannZeta s / riemannZeta s‖ * ‖mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) s‖ * X ^ σ
        ≤ (CL * Real.log T) * (B * (ε * T ^ 2)⁻¹) * X ^ 2 := by
          refine mul_le_mul (mul_le_mul hζ hM (norm_nonneg _) (mul_nonneg CL0.le hlogT)) hXs
            (Real.rpow_nonneg (by linarith) _) (mul_nonneg (mul_nonneg CL0.le hlogT)
              (mul_nonneg B0.le (inv_nonneg.mpr hεT.le)))
      _ = P := by rw [hP]
  have hlen : |σ₀ - σ₁| ≤ 2 := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hbound : ∀ τ : ℝ, |τ| = T →
      ‖∫ σ in σ₁..σ₀, SmoothedChebyshevIntegrand ν ε X (σ + τ * I)‖ ≤ P * 2 := by
    intro τ hτ
    calc ‖∫ σ in σ₁..σ₀, SmoothedChebyshevIntegrand ν ε X (σ + τ * I)‖ ≤ P * |σ₀ - σ₁| :=
          intervalIntegral.norm_integral_le_of_norm_le_const (fun σ hσ ↦ hpt σ τ hτ hσ)
      _ ≤ P * 2 := mul_le_mul_of_nonneg_left hlen P0
  have hfinal : c * (P * 2) = c * 2 * CL * B * Real.log T * (ε * T ^ 2)⁻¹ * X ^ 2 := by
    rw [hP]; ring
  constructor
  · unfold I₂
    rw [norm_mul, ← hc]
    have e : (fun σ : ℝ ↦ SmoothedChebyshevIntegrand ν ε X (σ - T * I)) =
        fun σ : ℝ ↦ SmoothedChebyshevIntegrand ν ε X (σ + ((-T : ℝ) : ℂ) * I) := by
      funext σ; congr 1; simp only [ofReal_neg]; ring
    rw [e, ← hfinal]
    exact mul_le_mul_of_nonneg_left (hbound (-T) (by rw [abs_neg, abs_of_pos hT0])) c0
  · unfold I₈
    rw [norm_mul, ← hc, ← hfinal]
    exact mul_le_mul_of_nonneg_left (hbound T (abs_of_pos hT0)) c0

/-- Step 3: under RH, `ψ(x) = x + O(x^(1/2 + δ))` for every `δ > 0`. -/
theorem chebyshev_psi_of_RH (RH : RiemannHypothesis) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → |Chebyshev.psi X - X| ≤ C * X ^ (1 / 2 + δ) := by
  set δ' := min δ (1 / 2) with hδ'
  have hδ'0 : 0 < δ' := lt_min hδ (by norm_num)
  have hδ'1 : δ' ≤ 1 / 2 := min_le_right _ _
  have hδ'δ : δ' ≤ δ := min_le_left _ _
  set σ₁ := 1 / 2 + δ' / 2 with hσ₁
  have h1 : 1 / 2 < σ₁ := by linarith
  have h2 : σ₁ < 1 := by linarith
  obtain ⟨ν, νdiff', νnonneg', νsupp, νmass'⟩ := SmoothExistence
  have νdiff : ContDiff ℝ 1 ν := νdiff'.of_le (by simp)
  have νnonneg : ∀ x > 0, 0 ≤ ν x := fun x _ ↦ νnonneg' x
  have νmass : ∫ x in Ioi 0, ν x / x = 1 := by rwa [← integral_Ici_eq_integral_Ioi]
  obtain ⟨Cc, Cc0, hCc⟩ := SmoothedChebyshevClose νdiff νsupp νnonneg νmass
  obtain ⟨C1, C10, hC1⟩ := I1Bound νsupp νdiff νnonneg νmass
  obtain ⟨C9, C90, hC9⟩ := I9Bound νsupp νdiff νnonneg νmass
  obtain ⟨ε₀, cM, ε₀0, cM0, hcM⟩ := MellinOfSmooth1cExplicit νdiff νsupp νmass
  obtain ⟨M37, M370, hM37⟩ := I37_bound RH νdiff νsupp h1 h2 hδ'0 (by linarith)
  obtain ⟨M2, M20, hM2⟩ := I28_bound RH νdiff νsupp h1 h2
  set A := Cc + C1 + C9 + 2 * M2 with hA
  have A0 : 0 ≤ A := by rw [hA]; linarith
  refine ⟨A / δ' + cM + M37, 16 + (ε₀⁻¹) ^ 2, fun X hX ↦ ?_⟩
  have hX16 : 16 ≤ X := by nlinarith [sq_nonneg ε₀⁻¹]
  have hX0 : 0 < X := by linarith
  have hX1 : 1 ≤ X := by linarith
  set u := Real.sqrt X with hu
  have huX : u ^ 2 = X := Real.sq_sqrt hX0.le
  have hu0 : 0 < u := Real.sqrt_pos.mpr hX0
  have hu4 : 4 ≤ u := by nlinarith
  have huε : ε₀⁻¹ < u := by
    refine lt_of_pow_lt_pow_left₀ 2 hu0.le ?_
    rw [huX]
    have : 0 < ε₀⁻¹ := inv_pos.mpr ε₀0
    nlinarith
  set ε := u⁻¹ with hε
  have ε0 : 0 < ε := inv_pos.mpr hu0
  have ε1 : ε < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have εε₀ : ε < ε₀ := (inv_lt_comm₀ hu0 ε₀0).mpr huε
  have hεX : ε * X = u := by
    rw [hε, ← huX, pow_two, ← mul_assoc, inv_mul_cancel₀ hu0.ne', one_mul]
  have hu0' : u ≠ 0 := hu0.ne'
  -- the contour shift
  have holo : HolomorphicOn (deriv riemannZeta / riemannZeta)
      ((Icc σ₁ 2) ×ℂ (Icc (-X) X) \ {1}) := by
    intro s hs
    have hs1 : s ≠ 1 := hs.2
    have hre : σ₁ ≤ s.re := (Complex.mem_reProdIm.1 hs.1).1.1
    exact (((analyticAt_riemannZeta hs1).deriv.differentiableAt).div
      (differentiableAt_riemannZeta hs1)
      (riemannZeta_ne_zero_of_RH RH (by linarith) hs1)).differentiableWithinAt
  have hPull := SmoothedChebyshevPull1 ε0 ε1 X (by linarith) (T := X) hX0 (σ₁ := σ₁)
    (by linarith) h2 holo νsupp νnonneg νmass νdiff
  set SC := SmoothedChebyshev ν ε X
  set m1 := mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) 1
  set a₁ := I₁ ν ε X X
  set a₂ := I₂ ν ε X X σ₁
  set a₃ := I₃₇ ν ε X X σ₁
  set a₈ := I₈ ν ε X X σ₁
  set a₉ := I₉ ν ε X X
  have hsplit : ((Chebyshev.psi X : ℝ) : ℂ) - (X : ℂ) =
      -(SC - (Chebyshev.psi X : ℂ)) + (a₁ - a₂ + a₃ + a₈ + a₉) + (m1 - 1) * X := by
    rw [hPull]; ring
  have hnorm : |Chebyshev.psi X - X| ≤ ‖SC - (Chebyshev.psi X : ℂ)‖ + (‖a₁‖ + ‖a₂‖ + ‖a₃‖ +
      ‖a₈‖ + ‖a₉‖) + ‖m1 - 1‖ * X := by
    have e : |Chebyshev.psi X - X| = ‖((Chebyshev.psi X : ℝ) : ℂ) - (X : ℂ)‖ := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [e, hsplit]
    have n1 := norm_add_le (-(SC - (Chebyshev.psi X : ℂ)) + (a₁ - a₂ + a₃ + a₈ + a₉))
      ((m1 - 1) * (X : ℂ))
    have n1' := norm_add_le (-(SC - (Chebyshev.psi X : ℂ))) (a₁ - a₂ + a₃ + a₈ + a₉)
    have n2 : ‖a₁ - a₂ + a₃ + a₈ + a₉‖ ≤ ‖a₁‖ + ‖a₂‖ + ‖a₃‖ + ‖a₈‖ + ‖a₉‖ := by
      have := norm_add_le (a₁ - a₂ + a₃ + a₈) a₉
      have := norm_add_le (a₁ - a₂ + a₃) a₈
      have := norm_add_le (a₁ - a₂) a₃
      have := norm_sub_le a₁ a₂
      linarith
    have n3 : ‖(m1 - 1) * (X : ℂ)‖ = ‖m1 - 1‖ * X := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hX0.le]
    rw [norm_neg] at n1'
    linarith
  -- the six bounds, in terms of `u = √X` and `L = log X`
  set L := Real.log X with hL
  have hClose : ‖SC - (Chebyshev.psi X : ℂ)‖ ≤ Cc * u * L := by
    have h := hCc X (by linarith) ε ε0 ε1 (by rw [mul_comm, hεX]; linarith)
    calc ‖SC - (Chebyshev.psi X : ℂ)‖ ≤ Cc * ε * X * L := h
      _ = Cc * u * L := by rw [mul_assoc Cc ε X, hεX]
  have hI1 : ‖a₁‖ ≤ C1 * u * L := by
    have h := hC1 ε ε0 ε1 X (by linarith) (T := X) (by linarith)
    calc ‖a₁‖ ≤ C1 * X * L / (ε * X) := h
      _ = C1 * u * L := by rw [hεX, div_eq_iff hu0', ← huX]; ring
  have hI9 : ‖a₉‖ ≤ C9 * u * L := by
    have h := hC9 ε0 ε1 X (by linarith) (T := X) (by linarith)
    calc ‖a₉‖ ≤ C9 * X * L / (ε * X) := h
      _ = C9 * u * L := by rw [hεX, div_eq_iff hu0', ← huX]; ring
  obtain ⟨h28a, h28b⟩ := hM2 ε ε0 ε1 X (by linarith) X (by linarith)
  have hk : (ε * X ^ 2)⁻¹ * X ^ 2 = u := by
    rw [mul_inv, mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 hX0.ne'), mul_one, hε, inv_inv]
  have h28 : M2 * L * (ε * X ^ 2)⁻¹ * X ^ 2 = M2 * u * L := by
    rw [mul_assoc (M2 * L), hk]; ring
  have hm1 : ‖m1 - 1‖ * X ≤ cM * u := by
    have h := hcM ε ⟨ε0, εε₀⟩
    calc ‖m1 - 1‖ * X ≤ cM * ε * X := mul_le_mul_of_nonneg_right h hX0.le
      _ = cM * u := by rw [mul_assoc, hεX]
  have hI3 : ‖a₃‖ ≤ M37 * X ^ (1 / 2 + δ') := by
    have h := hM37 ε ε0 ε1 X (by linarith) X hX0.le
    have hpow : ε ^ (-δ') * X ^ σ₁ = X ^ (1 / 2 + δ') := by
      rw [hε, Real.inv_rpow hu0.le, Real.rpow_neg hu0.le, inv_inv, hu, Real.sqrt_eq_rpow,
        ← Real.rpow_mul hX0.le, ← Real.rpow_add hX0, hσ₁]
      ring_nf
    calc ‖a₃‖ ≤ M37 * ε ^ (-δ') * X ^ σ₁ := h
      _ = M37 * X ^ (1 / 2 + δ') := by rw [mul_assoc, hpow]
  -- powers of X
  have hP : u * X ^ δ' = X ^ (1 / 2 + δ') := by
    rw [hu, Real.sqrt_eq_rpow, ← Real.rpow_add hX0]
  have huL : u * L ≤ X ^ (1 / 2 + δ') / δ' := by
    have hlog : L ≤ X ^ δ' / δ' := Real.log_le_rpow_div hX0.le hδ'0
    calc u * L ≤ u * (X ^ δ' / δ') := mul_le_mul_of_nonneg_left hlog hu0.le
      _ = X ^ (1 / 2 + δ') / δ' := by rw [← hP]; ring
  have hu_le : u ≤ X ^ (1 / 2 + δ') := by
    rw [hu, Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  have hmono : X ^ (1 / 2 + δ') ≤ X ^ (1 / 2 + δ) :=
    Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  have hXp0 : 0 ≤ X ^ (1 / 2 + δ') := Real.rpow_nonneg hX0.le _
  have hsum : |Chebyshev.psi X - X| ≤ A * (u * L) + cM * u + M37 * X ^ (1 / 2 + δ') := by
    have e2 : ‖a₂‖ ≤ M2 * u * L := by rw [← h28]; exact h28a
    have e8 : ‖a₈‖ ≤ M2 * u * L := by rw [← h28]; exact h28b
    have : A * (u * L) = Cc * u * L + C1 * u * L + C9 * u * L + 2 * (M2 * u * L) := by
      rw [hA]; ring
    linarith
  have huL' : A * (u * L) ≤ A / δ' * X ^ (1 / 2 + δ') := by
    calc A * (u * L) ≤ A * (X ^ (1 / 2 + δ') / δ') := mul_le_mul_of_nonneg_left huL A0
      _ = A / δ' * X ^ (1 / 2 + δ') := by ring
  have hcu : cM * u ≤ cM * X ^ (1 / 2 + δ') := mul_le_mul_of_nonneg_left hu_le cM0.le
  have hexp : (A / δ' + cM + M37) * X ^ (1 / 2 + δ') =
      A / δ' * X ^ (1 / 2 + δ') + cM * X ^ (1 / 2 + δ') + M37 * X ^ (1 / 2 + δ') := by ring
  calc |Chebyshev.psi X - X| ≤ (A / δ' + cM + M37) * X ^ (1 / 2 + δ') := by
        rw [hexp]; linarith
    _ ≤ (A / δ' + cM + M37) * X ^ (1 / 2 + δ) :=
        mul_le_mul_of_nonneg_left hmono
          (add_nonneg (add_nonneg (div_nonneg A0 hδ'0.le) cM0.le) M370)

end RHStructure
