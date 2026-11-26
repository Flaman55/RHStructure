import Applications.RHPsi

/-!
# Step 4 of the short-interval application: a prime in `(x, x + x^(1/2+ε)]`

From `ψ(x) = x + O(x^(1/2+δ))` (`chebyshev_psi_of_RH`) and `ψ - θ = O(√x)` (Mathlib's
`Chebyshev.psi_sub_theta_le_mul_sqrt`): with `h = x^(1/2+ε)` and `δ = ε/2`,
`θ(x + h) - θ(x) ≥ h - K x^(1/2+δ) > 0` for large `x`, so a prime lies in `(x, x + h]`
(`exists_prime_of_theta_lt`). This is the classical consequence of RH (von Koch 1901,
Cramér 1920); here RH is the theorem `Structural.zeta_zeros_on_line` of grh-compact.
-/

open Real

namespace RHStructure

/-- If `θ(x) < θ(y)`, a prime lies in `(x, y]`. -/
lemma exists_prime_of_theta_lt {x y : ℝ} (hx : 0 ≤ x) (h : Chebyshev.theta x < Chebyshev.theta y) :
    ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ y := by
  by_contra hne
  push_neg at hne
  apply lt_irrefl (Chebyshev.theta y)
  refine lt_of_le_of_lt ?_ h
  unfold Chebyshev.theta
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hp ⊢
    obtain ⟨⟨hp0, hpy⟩, hpp⟩ := hp
    refine ⟨⟨hp0, ?_⟩, hpp⟩
    by_contra hpx
    push_neg at hpx
    have hxp : x < p := (Nat.floor_lt hx).1 hpx
    have hyp := hne p hpp hxp
    have hy : 0 ≤ y := by
      by_contra hy
      push_neg at hy
      rw [Nat.floor_of_nonpos hy.le] at hpy
      omega
    have : (p : ℝ) ≤ y := (Nat.le_floor_iff hy).1 hpy
    linarith
  · intro p _ _
    exact Real.log_natCast_nonneg p

/-- The core estimate, for `ε ≤ 1/4`. -/
lemma exists_prime_short_interval_core (RH : RiemannHypothesis) {ε : ℝ} (hε : 0 < ε)
    (hε4 : ε ≤ 1 / 4) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ x + x ^ (1 / 2 + ε) := by
  set δ := ε / 2 with hδ
  have hδ0 : 0 < δ := by linarith
  obtain ⟨C, X₀, hC⟩ := chebyshev_psi_of_RH RH hδ0
  obtain ⟨C', hC'⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  set Cm := max C 0 with hCm
  set Cpm := max C' 0 with hCpm
  set K := 3 * Cm + 2 * Cpm + 1 with hK
  have K0 : 0 < K := by
    have := le_max_right C 0
    have := le_max_right C' 0
    linarith
  refine ⟨max X₀ (max 1 (K ^ δ⁻¹) + 1), fun x hx ↦ ?_⟩
  have hxX₀ : X₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx1 : 1 ≤ x := by
    have := le_max_left 1 (K ^ δ⁻¹)
    have := le_max_right X₀ (max 1 (K ^ δ⁻¹) + 1)
    linarith
  have hxK : K ^ δ⁻¹ < x := by
    have := le_max_right 1 (K ^ δ⁻¹)
    have := le_max_right X₀ (max 1 (K ^ δ⁻¹) + 1)
    linarith
  have hx0 : 0 < x := by linarith
  set a := 1 / 2 + δ with ha
  set h := x ^ (1 / 2 + ε) with hh
  set y := x + h with hy
  have hh0 : 0 ≤ h := Real.rpow_nonneg hx0.le _
  have hhx : h ≤ x := by
    calc h = x ^ (1 / 2 + ε) := hh
      _ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      _ = x := Real.rpow_one x
  have hy1 : 1 ≤ y := by linarith
  have hy2 : y ≤ 2 * x := by linarith
  have hxa : 0 < x ^ a := Real.rpow_pos_of_pos hx0 _
  -- `y^a ≤ 2 x^a` and `√y ≤ 2 x^a`
  have hya : y ^ a ≤ 2 * x ^ a := by
    calc y ^ a ≤ (2 * x) ^ a := Real.rpow_le_rpow (by linarith) hy2 (by linarith)
      _ = 2 ^ a * x ^ a := Real.mul_rpow (by norm_num) hx0.le
      _ ≤ 2 * x ^ a := by
          refine mul_le_mul_of_nonneg_right ?_ hxa.le
          calc (2 : ℝ) ^ a ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num)
                (by linarith)
            _ = 2 := Real.rpow_one 2
  have hsqrt : Real.sqrt y ≤ 2 * x ^ a := by
    rw [Real.sqrt_eq_rpow]
    calc y ^ (1 / 2 : ℝ) ≤ y ^ a := Real.rpow_le_rpow_of_exponent_le hy1 (by linarith)
      _ ≤ 2 * x ^ a := hya
  -- bounds on θ
  have hθx : Chebyshev.theta x ≤ x + Cm * x ^ a := by
    have h1 := (abs_le.1 (hC x hxX₀)).2
    have h2 : C * x ^ a ≤ Cm * x ^ a := mul_le_mul_of_nonneg_right (le_max_left _ _) hxa.le
    have h3 := Chebyshev.theta_le_psi x
    linarith
  have hθy : y - Cm * (2 * x ^ a) - Cpm * (2 * x ^ a) ≤ Chebyshev.theta y := by
    have h1 := (abs_le.1 (hC y (by linarith))).1
    have h2 : C * y ^ a ≤ Cm * (2 * x ^ a) :=
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by linarith) _)).trans
        (mul_le_mul_of_nonneg_left hya (le_max_right _ _))
    have h3 := hC' y
    have h4 : C' * Real.sqrt y ≤ Cpm * (2 * x ^ a) :=
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)).trans
        (mul_le_mul_of_nonneg_left hsqrt (le_max_right _ _))
    linarith
  -- `h = x^δ · x^a > K x^a`
  have hsplit : h = x ^ δ * x ^ a := by
    rw [hh, ← Real.rpow_add hx0, ha, hδ]
    ring_nf
  have hxδ : K < x ^ δ := by
    have := Real.rpow_lt_rpow (Real.rpow_nonneg K0.le _) hxK hδ0
    rwa [Real.rpow_inv_rpow K0.le hδ0.ne'] at this
  have hbig : K * x ^ a < h := by
    rw [hsplit]
    exact mul_lt_mul_of_pos_right hxδ hxa
  have hlt : Chebyshev.theta x < Chebyshev.theta y := by
    have : (3 * Cm + 2 * Cpm) * x ^ a < h := by
      have : (3 * Cm + 2 * Cpm) * x ^ a < K * x ^ a :=
        mul_lt_mul_of_pos_right (by rw [hK]; linarith) hxa
      linarith
    have e : y - Cm * (2 * x ^ a) - Cpm * (2 * x ^ a) - (x + Cm * x ^ a) =
        h - (3 * Cm + 2 * Cpm) * x ^ a := by rw [hy]; ring
    linarith
  exact exists_prime_of_theta_lt hx0.le hlt

/-- Step 4: under RH, for every `ε > 0` and all large `x`, there is a prime in
`(x, x + x^(1/2+ε)]`. -/
theorem exists_prime_short_interval_of_RH (RH : RiemannHypothesis) {ε : ℝ} (hε : 0 < ε) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ x + x ^ (1 / 2 + ε) := by
  obtain ⟨x₀, hx₀⟩ := exists_prime_short_interval_core RH (ε := min ε (1 / 4))
    (lt_min hε (by norm_num)) (min_le_right _ _)
  refine ⟨max x₀ 1, fun x hx ↦ ?_⟩
  obtain ⟨p, hp, hxp, hpx⟩ := hx₀ x (le_trans (le_max_left _ _) hx)
  refine ⟨p, hp, hxp, hpx.trans ?_⟩
  have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
  have : x ^ (1 / 2 + min ε (1 / 4)) ≤ x ^ (1 / 2 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith [min_le_left ε (1 / 4)])
  linarith

end RHStructure
