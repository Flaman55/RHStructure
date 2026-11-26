import Mathlib.NumberTheory.Padics.PadicVal.Basic
import New.Endgame.PrimeError

/-!
# Rings and arcs: the prime-sum side of grh-compact in ring language (steps S0-S2)

Ring reading (after A. Flamandzki, ArcOrder). Every `p ≥ 1` is a ring that turns one step per
unit of `ℕ`. At position `N` its marker is `N % p` and its arc is `N / p`, the number of full
turns. Unrounded, the number of turns over a length `A` is `A / p`.

This file states, in that language:

* `arc_mul_add_marker`: position = arc · ring + marker;
* `arc_le_turns`, `turns_lt_arc_add_one`: the arc is the rounded-down number of turns;
* `padicValNat_factorial_eq_sum_arcs`: the divisibility of `N!` by `p` is the sum of the arcs of
  the rings `p, p², p³, …` at `N` (Legendre's formula, Mathlib's `padicValNat_factorial`);
* `primeError_eq_sum_excess_turns`: the remainder `primeError` of grh-compact, whose one-sided
  bound gives the zero-free half-plane, is the weighted sum over rings `ν ≤ A` of the turns of
  `ν` over the length `A` in excess of the turns of the cutoff ring `z`
  (grh-compact's `primeError_eq_sum`, restated);
* `weight_nonneg`: the weights are non-negative (Landau's lemma needs this).

The weight `lambdaClass d M ν = Λ(ν)·(1 − (ν/d))` on `ν ≡ 1 mod M` keeps the rings whose marker
modulo `M` is `1` and weighs them by the quadratic-residue mask modulo `d`.

The objects `primeError`, `lambdaClass`, `logDerivMean` and the lemmas `primeError_eq_sum`,
`lambdaClass_nonneg_and_abs_le` are those of grh-compact (Luke Sernau and colleagues at
Anthropic, with Claude; a rewriting of Levent Alpöge's proof), commit 72fead1, Apache-2.0.
-/

open Finset

namespace Structural

/-- The marker of the ring `p` at position `N`. -/
def marker (N p : ℕ) : ℕ := N % p

/-- The arc of the ring `p` at position `N`: the number of full turns. -/
def arc (N p : ℕ) : ℕ := N / p

/-- The number of turns of the ring `ν` over the length `A`, not rounded. -/
noncomputable def turns (A ν : ℝ) : ℝ := A / ν

/-- Position = arc · ring + marker. -/
theorem arc_mul_add_marker (N p : ℕ) : p * arc N p + marker N p = N :=
  Nat.div_add_mod N p

/-- The arc does not exceed the number of turns. -/
theorem arc_le_turns (N p : ℕ) : (arc N p : ℝ) ≤ turns N p := by
  unfold arc turns
  exact Nat.cast_div_le

/-- The number of turns is less than the arc plus one. -/
theorem turns_lt_arc_add_one (N p : ℕ) (hp : 0 < p) : turns N p < arc N p + 1 := by
  unfold arc turns
  rw [div_lt_iff₀ (by exact_mod_cast hp)]
  have h : N < (N / p + 1) * p := by
    rw [Nat.add_mul, one_mul]
    exact Nat.lt_div_mul_add hp
  exact_mod_cast h

/-- Divisibility counted by turns: the exponent of the prime `p` in `N!` is the sum of the arcs of
the rings `p^i`, `1 ≤ i < b`, at `N`, for any `b` beyond `log_p N`. -/
theorem padicValNat_factorial_eq_sum_arcs (p N b : ℕ) [Fact p.Prime] (hb : Nat.log p N < b) :
    padicValNat p N.factorial = ∑ i ∈ Ico 1 b, arc N (p ^ i) := by
  simpa [arc] using padicValNat_factorial (p := p) (n := N) (b := b) hb

/-- The remainder of grh-compact as excess turns: for `0 < z ≤ A`,
`primeError d M z = (1/A) Σ_{ν ≤ A} λ(ν) · (turns of ν over A − turns of z over A)⁺
  − log z / φ(M) − Re logDerivMean(1)`. -/
theorem primeError_eq_sum_excess_turns {d M : ℕ} [Fact d.Prime] [NeZero M] (A : ℕ) {z : ℝ}
    (u : 0 < z) (h : z ≤ A) :
    primeError d M z = ∑ ν ∈ Icc 1 A, lambdaClass d M ν * (turns A ν - turns A z)⁺ / A
      - Real.log z / Nat.totient M - (logDerivMean d M 1).re := by
  simpa [turns] using primeError_eq_sum (d := d) (M := M) A u h

/-- The weights are non-negative: each ring `ν` enters with `λ(ν) ≥ 0`. -/
theorem weight_nonneg (d M ν : ℕ) [Fact d.Prime] : 0 ≤ lambdaClass d M ν :=
  (lambdaClass_nonneg_and_abs_le d M ν).1

end Structural
