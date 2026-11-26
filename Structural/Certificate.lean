import Mathlib.Data.Nat.Choose.Central
import Structural.Arcs
import New.Main

/-!
# The certificate: size against divisibility (step S3)

Ring reading. A certificate is a non-zero quantity with two bounds:

* from above, by its size;
* from below, by its divisibility, counted ring by ring through arcs, and turned into a size by
  the product formula: a non-zero algebraic number cannot be small at every place.

Over `ℚ`, with one central binomial coefficient, this is the certificate of Chebyshev and Erdős,
used in A. Flamandzki's StructuralBertrand (`binomial_contradiction`): `centralBinom_size` is its
size side, `centralBinom_arcs` its divisibility side in arcs. Over `ℚ` it gives bounds of
Chebyshev order only.

grh-compact runs the same certificate on a covolume of `m` theta lifts over a CM field: the size
side is Theorems A and B, the divisibility side Theorem C, and the product formula
(`HeightLe.nonneg`, here `product_formula`) closes it. What is left is the inequality (⋆),
`m · remainder ≤ (log b)² · budget` (`star_inequality`, here `certificate`), whose remainder is
the excess-turns sum of `Structural.primeError_eq_sum_excess_turns`.

`star_inequality`, `HeightLe`, `HeightLe.nonneg` and `Data` are those of grh-compact (Luke Sernau
and colleagues at Anthropic, with Claude; a rewriting of Levent Alpöge's proof), commit 72fead1,
Apache-2.0.
-/

open Finset

namespace Structural

/-- Size side over `ℚ`: `4ⁿ < n · C(2n, n)` for `n ≥ 4` (Mathlib). -/
theorem centralBinom_size (n : ℕ) (hn : 4 ≤ n) : 4 ^ n < n * Nat.centralBinom n :=
  Nat.four_pow_lt_mul_centralBinom n hn

/-- Divisibility side over `ℚ`, in arcs: the exponent of `p` in `C(2n, n)` is the excess of the
arcs of the rings `p^i` at `2n` over twice their arcs at `n`. -/
theorem centralBinom_arcs (p n b : ℕ) [Fact p.Prime] (hb : Nat.log p (2 * n) < b) :
    padicValNat p (Nat.centralBinom n) + 2 * ∑ i ∈ Ico 1 b, arc n (p ^ i) =
      ∑ i ∈ Ico 1 b, arc (2 * n) (p ^ i) := by
  have hb' : Nat.log p n < b := lt_of_le_of_lt (Nat.log_mono_right (by omega)) hb
  rw [← padicValNat_factorial_eq_sum_arcs p n b hb',
    ← padicValNat_factorial_eq_sum_arcs p (2 * n) b hb]
  have h := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
  rw [show 2 * n - n = n by omega] at h
  have hc : (2 * n).choose n ≠ 0 := (Nat.choose_pos (by omega)).ne'
  rw [Nat.centralBinom_eq_two_mul_choose, ← h,
    padicValNat.mul (mul_ne_zero hc (Nat.factorial_ne_zero n)) (Nat.factorial_ne_zero n),
    padicValNat.mul hc (Nat.factorial_ne_zero n)]
  ring

/-- The square-root threshold in arcs: if `N < p ^ 2`, only the first ring `p` carries an arc at
`N`; every ring `p ^ i` with `i ≥ 2` has arc zero. -/
theorem arc_eq_zero_of_lt_sq {N p i : ℕ} (hN : N < p ^ 2) (hi : 2 ≤ i) : arc N (p ^ i) = 0 := by
  have hp : 0 < p := by
    rcases Nat.eq_zero_or_pos p with h | h
    · subst h; simp at hN
    · exact h
  exact Nat.div_eq_of_lt (lt_of_lt_of_le hN (Nat.pow_le_pow_right hp hi))

/-- Above the square-root threshold a prime enters the central binomial coefficient at most once:
if `2n < p ^ 2`, the exponent of `p` in `C(2n, n)` is at most `1` (Mathlib's
`Nat.factorization_choose_le_one`). This is where the exponent `1/2` enters the Chebyshev–Erdős
certificate: the primes below `√(2n)` are the only ones that can be counted twice. -/
theorem centralBinom_factorization_le_one {n p : ℕ} (h : 2 * n < p ^ 2) :
    (Nat.centralBinom n).factorization p ≤ 1 := by
  rw [Nat.centralBinom_eq_two_mul_choose]
  exact Nat.factorization_choose_le_one h

/-- The product formula, in heights (grh-compact's `HeightLe.nonneg`): if the constant `1` has
height at most `c`, then `c ≥ 0`. A non-zero algebraic number cannot be small at every place. -/
theorem product_formula {c : ℝ} (h : HeightLe c 1) : 0 ≤ c :=
  HeightLe.nonneg h

/-- The certificate of grh-compact closed: `m · remainder ≤ (log b)² · budget` (the inequality
(⋆), grh-compact's `star_inequality`). The remainder is the excess-turns sum of
`primeError_eq_sum_excess_turns`, weighted by `m`, the number of lifts. -/
theorem certificate {P : Parameters} (D : Data P) : D.m * D.remainder ≤ D.logB ^ 2 * D.budget :=
  star_inequality

end Structural
