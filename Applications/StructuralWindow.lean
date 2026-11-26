import Applications.ShortInterval
import Structural.Spine

/-!
# The general law of the Structural Window, from the Lean RH

A. Flamandzki's Structural Window (<https://github.com/Flaman55/Structural-Window>, folder
`lean`, Lean v4.14.0) reads "a prime in `(A, A + W]`" as a *void* of the window: a position that no
prime of the active base `{p prime : p² ≤ A + W}` divides. Its width laws `law θ A = ⌈A^θ⌉`
form one scale on which Hoheisel, Ingham, Huxley, Baker–Harman–Pintz and Li are points; their
certificates `GapCertificate_eventually θ` enter there as citations, the sharpest at `θ = 0.52`.
The span between the Legendre width `2⌊√A⌋ + 1` and `A^0.52` is open there.

This file restates the window definitions verbatim (they use only Mathlib) and proves the
certificate for **every** `θ ∈ (1/2, 1]` from `exists_prime_short_interval_of_RH`, with RH the
theorem of grh-compact; and the general law on the sub-range `⌈A^θ⌉ ≤ W ≤ A`. The endpoint
`θ = 1/2`, Legendre's width, is not reached: a prime in `(A, A + A^θ]` does not give one in the
narrower `(A, A + 2√A + 1]`.
-/

namespace StructuralWindow

/-- The window `(A, A + W]` (Structural Window, `Core.coupledWindow`). -/
def coupledWindow (A W : ℕ) : Finset ℕ := Finset.Ioc A (A + W)

/-- Active base for top `T`: the primes `p` with `p² ≤ T` (`Core.activeBase`). -/
def activeBase (T : ℕ) : Finset ℕ :=
  (Finset.range (T + 1)).filter (fun p => Nat.Prime p ∧ p ^ 2 ≤ T)

/-- `n` is a void of the window: no prime of the active base divides it (`Core.isVoid`). -/
def isVoid (A W n : ℕ) : Prop := ∀ p ∈ activeBase (A + W), ¬ p ∣ n

/-- The window contains a void (`Core.windowHasVoid`). -/
def windowHasVoid (A W : ℕ) : Prop := ∃ n ∈ coupledWindow A W, isVoid A W n

namespace ShortInterval

/-- The exponent-`θ` width law `⌈A^θ⌉` (`ShortInterval.law`). -/
noncomputable def law (θ : ℝ) : ℕ → ℕ := fun A => Nat.ceil ((A : ℝ) ^ θ)

/-- The certificate at exponent `θ` (`ShortInterval.GapCertificate_eventually`). -/
def GapCertificate_eventually (θ : ℝ) : Prop :=
  ∃ A₀ : ℕ, ∀ A : ℕ, A₀ ≤ A → windowHasVoid A (law θ A)

lemma law_le_self {θ : ℝ} (hθ : θ ≤ 1) {A : ℕ} (hA : 1 ≤ A) : law θ A ≤ A := by
  unfold law
  rw [Nat.ceil_le]
  have hA1 : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  calc (A : ℝ) ^ θ ≤ (A : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hA1 hθ
    _ = (A : ℝ) := Real.rpow_one _

end ShortInterval

open ShortInterval

/-- A prime `p > A` in `(A, A + W]` with `W ≤ A` is a void of the window. -/
lemma windowHasVoid_of_prime {A W p : ℕ} (hp : p.Prime) (hAp : A < p) (hpW : p ≤ A + W)
    (hWA : W ≤ A) : windowHasVoid A W := by
  refine ⟨p, ?_, ?_⟩
  · rw [coupledWindow, Finset.mem_Ioc]; exact ⟨hAp, hpW⟩
  · intro q hq hqp
    rw [activeBase, Finset.mem_filter] at hq
    obtain ⟨_, hqprime, hqsq⟩ := hq
    have hqeq : q = p := (Nat.prime_dvd_prime_iff_eq hqprime hp).mp hqp
    rw [hqeq] at hqsq
    have hsq : (A + 1) * (A + 1) ≤ p * p := Nat.mul_le_mul hAp hAp
    nlinarith

/-- From the Lean RH: the short-interval prime for `x = A` and exponent `θ`. -/
lemma exists_prime_law_of_RH (RH : RiemannHypothesis) {θ : ℝ} (hθ : 1 / 2 < θ) :
    ∃ A₀ : ℕ, 1 ≤ A₀ ∧ ∀ A : ℕ, A₀ ≤ A → ∃ p : ℕ, p.Prime ∧ A < p ∧ p ≤ A + law θ A := by
  obtain ⟨x₀, hx₀⟩ := RHStructure.exists_prime_short_interval_of_RH RH (ε := θ - 1 / 2)
    (by linarith)
  refine ⟨max (Nat.ceil x₀) 1, le_max_right _ _, fun A hA ↦ ?_⟩
  have hAx : x₀ ≤ (A : ℝ) :=
    (Nat.le_ceil x₀).trans (by exact_mod_cast (le_max_left _ _).trans hA)
  obtain ⟨p, hp, hAp, hpA⟩ := hx₀ A hAx
  refine ⟨p, hp, by exact_mod_cast hAp, ?_⟩
  have h1 : (A : ℝ) ^ (1 / 2 + (θ - 1 / 2)) = (A : ℝ) ^ θ := by ring_nf
  rw [h1] at hpA
  have h2 : (p : ℝ) ≤ (A : ℝ) + (law θ A : ℝ) := hpA.trans (by
    unfold law
    linarith [Nat.le_ceil ((A : ℝ) ^ θ)])
  exact_mod_cast h2

/-- **The certificate at every exponent `θ ∈ (1/2, 1]`**, proved: from the Lean RH every
sufficiently large window of width `⌈A^θ⌉` has a void. -/
theorem gapCertificate_eventually_of_RH (RH : RiemannHypothesis) {θ : ℝ} (hθ : 1 / 2 < θ)
    (hθ1 : θ ≤ 1) : GapCertificate_eventually θ := by
  obtain ⟨A₀, hA₀1, h⟩ := exists_prime_law_of_RH RH hθ
  refine ⟨A₀, fun A hA ↦ ?_⟩
  obtain ⟨p, hp, hAp, hpA⟩ := h A hA
  exact windowHasVoid_of_prime hp hAp hpA (law_le_self hθ1 (hA₀1.trans hA))

/-- **The general law on `⌈A^θ⌉ ≤ W ≤ A`**, for every `θ ∈ (1/2, 1]`: eventually every window
whose width lies between the exponent-`θ` law and Bertrand's width has a void. -/
theorem generalLaw_partial_of_RH (RH : RiemannHypothesis) {θ : ℝ} (hθ : 1 / 2 < θ) :
    ∃ A₀ : ℕ, ∀ A W : ℕ, A₀ ≤ A → law θ A ≤ W → W ≤ A → windowHasVoid A W := by
  obtain ⟨A₀, _, h⟩ := exists_prime_law_of_RH RH hθ
  refine ⟨A₀, fun A W hA hWlo hWhi ↦ ?_⟩
  obtain ⟨p, hp, hAp, hpA⟩ := h A hA
  exact windowHasVoid_of_prime hp hAp (by omega) hWhi

/-- The same, unconditionally in Lean: RH is grh-compact's theorem. -/
theorem generalLaw_partial {θ : ℝ} (hθ : 1 / 2 < θ) :
    ∃ A₀ : ℕ, ∀ A W : ℕ, A₀ ≤ A → law θ A ≤ W → W ≤ A → windowHasVoid A W :=
  generalLaw_partial_of_RH Structural.zeta_zeros_on_line hθ

/-! ## How far the window must move

The question of the general law is not how narrow a window can be, but how far the window must
move so that the active base cannot cover all of it. Two forms of the answer follow. -/

/-- From a prime `p`, the next prime is at most `⌈p^θ⌉` further, for every `θ > 1/2` and all
large `p`: moving the window by `⌈A^θ⌉` from the last prime found always leaves a void. -/
theorem nextPrime_gap_of_RH (RH : RiemannHypothesis) {θ : ℝ} (hθ : 1 / 2 < θ) :
    ∃ p₀ : ℕ, ∀ p : ℕ, p.Prime → p₀ ≤ p → ∃ q : ℕ, q.Prime ∧ p < q ∧ q ≤ p + law θ p := by
  obtain ⟨A₀, _, h⟩ := exists_prime_law_of_RH RH hθ
  exact ⟨A₀, fun p _ hp ↦ h p hp⟩

namespace ShortInterval

/-- Next anchor at exponent `θ`: advance by the width law itself (`ShortInterval.nextAnchor`). -/
noncomputable def nextAnchor (θ : ℝ) (A : ℕ) : ℕ := A + law θ A

/-- The marching anchor sequence at exponent `θ`, seeded at `2` (`ShortInterval.anchor`). -/
noncomputable def anchor (θ : ℝ) : ℕ → ℕ
  | 0 => 2
  | (k + 1) => nextAnchor θ (anchor θ k)

lemma law_pos {θ : ℝ} (hθ0 : 0 ≤ θ) {A : ℕ} (hA : 1 ≤ A) : 1 ≤ law θ A := by
  unfold law
  have hA1 : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have h1 : (1 : ℝ) ≤ (A : ℝ) ^ θ := Real.one_le_rpow hA1 hθ0
  have h2 : (1 : ℝ) ≤ (Nat.ceil ((A : ℝ) ^ θ) : ℝ) := h1.trans (Nat.le_ceil _)
  exact_mod_cast h2

lemma le_anchor {θ : ℝ} (hθ0 : 0 ≤ θ) (k : ℕ) : k + 2 ≤ anchor θ k := by
  induction k with
  | zero => simp [anchor]
  | succ n ih =>
    have heq : anchor θ (n + 1) = anchor θ n + law θ (anchor θ n) := rfl
    have := law_pos hθ0 (show 1 ≤ anchor θ n by omega)
    omega

end ShortInterval

/-- **The march.** Moving the window forward by its own width `⌈A^θ⌉`, for any `θ > 1/2`, from
some step on every window `(A_k, A_(k+1)]` of the march has a void, that is a prime. -/
theorem march_of_RH (RH : RiemannHypothesis) {θ : ℝ} (hθ : 1 / 2 < θ) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      ∃ p : ℕ, p.Prime ∧ anchor θ k < p ∧ p ≤ anchor θ (k + 1) := by
  obtain ⟨A₀, _, h⟩ := exists_prime_law_of_RH RH hθ
  refine ⟨A₀, fun k hk ↦ ?_⟩
  have hA : A₀ ≤ anchor θ k := by
    have := le_anchor (θ := θ) (by linarith) k
    omega
  obtain ⟨p, hp, h1, h2⟩ := h _ hA
  have heq : anchor θ (k + 1) = anchor θ k + law θ (anchor θ k) := rfl
  exact ⟨p, hp, h1, by omega⟩

/-- The march, unconditionally in Lean. -/
theorem march {θ : ℝ} (hθ : 1 / 2 < θ) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      ∃ p : ℕ, p.Prime ∧ anchor θ k < p ∧ p ≤ anchor θ (k + 1) :=
  march_of_RH Structural.zeta_zeros_on_line hθ

end StructuralWindow
