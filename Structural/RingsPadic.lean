import Mathlib

/-!
# Rings as the ℓ-adic metric, and frozen offsets

Two statements that turn rows of the dictionary of the paper into theorems.

* `marker_eq_iff_le_padicValInt`: two numbers have the same marker `N % ℓ^i` on the ring `ℓ^i`
  exactly when `i ≤ v_ℓ(a − b)`. So the ℓ-adic valuation of a difference is the number of rings
  `ℓ, ℓ², …` on which the two markers agree, independently of where the numbers lie on the axis:
  ℓ-adic closeness is closeness of markers.
* `frozen_offsets`: in `ZMod (ℓ^K)`, a root of unity of order prime to `ℓ` whose marker on the
  first ring is that of `1` equals `1`. Applied to `ζ/ζ'`: two such roots of unity that agree on the
  ring `ℓ` agree on every ring `ℓ^i`, `i ≤ K`. The values of a twist by a character of finite order
  prime to `ℓ` are such roots of unity: a twist rotates each prime by an angle fixed by its residue,
  and the offset it sets on the first ring of `ℓ` is frozen on all higher rings (the finite form of
  the uniqueness of Teichmüller lifts).

Markers are `N % p`, as `Structural.marker` in `Structural/Arcs.lean`; this file imports Mathlib only.
-/

namespace Structural

/-- Same marker on the ring `ℓ^i` ⟺ `ℓ^i` divides the difference. -/
theorem marker_eq_iff_dvd (a b n : ℕ) : a % n = b % n ↔ (n : ℤ) ∣ (a : ℤ) - b := by
  rw [show a % n = b % n ↔ a ≡ b [MOD n] from Iff.rfl, Nat.modEq_iff_dvd, dvd_sub_comm]

/-- The rings on which two different numbers share their marker are exactly `ℓ^i` with
`i ≤ v_ℓ(a − b)`. -/
theorem marker_eq_iff_le_padicValInt (ℓ : ℕ) [Fact ℓ.Prime] {a b : ℕ} (h : a ≠ b) (i : ℕ) :
    a % ℓ ^ i = b % ℓ ^ i ↔ i ≤ padicValInt ℓ ((a : ℤ) - b) := by
  rw [marker_eq_iff_dvd]
  push_cast
  rw [padicValInt_dvd_iff]
  have hne : (a : ℤ) - b ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast h)
  simp [hne]

/-- Frozen offsets: in `ZMod (ℓ^K)`, if `x^d = 1` with `d` prime to `ℓ` and `x ≡ 1` on the first
ring (`ℓ ∣ x − 1`), then `x = 1`. -/
theorem frozen_offsets {ℓ K d : ℕ} (hK : 1 ≤ K) (hd : Nat.Coprime d ℓ) {x : ZMod (ℓ ^ K)}
    (hx : x ^ d = 1) (h1 : (ℓ : ZMod (ℓ ^ K)) ∣ x - 1) : x = 1 := by
  have hpow : x ^ ℓ ^ (K - 1) = 1 := by
    have h := dvd_sub_pow_of_dvd_sub (p := ℓ) (b := (1 : ZMod (ℓ ^ K))) h1 (K - 1)
    rw [one_pow, Nat.sub_add_cancel hK] at h
    have h0 : (ℓ : ZMod (ℓ ^ K)) ^ K = 0 := by
      rw [← Nat.cast_pow, ZMod.natCast_self]
    rw [h0, zero_dvd_iff, sub_eq_zero] at h
    exact h
  have hc : Nat.Coprime d (ℓ ^ (K - 1)) := Nat.Coprime.pow_right _ hd
  have hdvd : orderOf x ∣ Nat.gcd d (ℓ ^ (K - 1)) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hx) (orderOf_dvd_of_pow_eq_one hpow)
  rw [hc.gcd_eq_one, Nat.dvd_one] at hdvd
  exact orderOf_eq_one_iff.mp hdvd

end Structural
