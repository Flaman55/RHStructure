import New.TwistedHecke.RootLemma
import Structural.Lever
import Structural.Certificate

/-!
# The lever as Stepanov's inequality

L. Alpöge describes the proof as a descendant of Stepanov's method for the Riemann Hypothesis over
finite fields (remark, <https://alpo.ge/remark.pdf>): over `𝔽_q` an auxiliary function vanishing
with multiplicity `E` at all `q` points has degree at least `E q`, and the balance `E ≈ √q` gives
the error `√q`. Over the integers multiplicity is missing; in the proof each theta lift of a chain
supplies one unit of it, and the chain has length `m ≈ √x`.

Three inequalities of the same shape, side by side:

* `stepanov` (grh-compact's `stepanov_count`, used there for the Hecke divisors): zeros counted
  with multiplicity are bounded by the degree, `E · q ≤ deg Φ`.
* `level_stepanov`: in the data of the proof, the level `N` carries the `m` lifts on the scale
  `b`, `m · log b ≤ log N`; in arcs, `N` has a nonzero arc on every ring `⌊b⌋^i`, `i ≤ m`
  (`level_arcs`). Multiplicity `m` times the size `log b` of a point against the "degree" `log N`.
* `erdos_multiplicity_one`: in the Chebyshev–Erdős certificate over `ℚ` the multiplicity is at
  most `1` above `√(2n)`; this is why that certificate gives Chebyshev bounds and not `1/2`.

The lever (`level_double_charge`, `lifts_sq_le`) charges `N` a second time, by its allowed loss
`4 m f b`; the two charges together give `m² ≲ x`, the balance `E ≈ √q` of Stepanov's method in
the form `m ≈ √x`.

`stepanov_count`, `Data` and `Data.log_N_mem_Icc` are those of grh-compact (Luke Sernau and
colleagues at Anthropic, with Claude; a rewriting of Levent Alpöge's proof), commit 72fead1,
Apache-2.0.
-/

namespace Structural

/-- Stepanov's count (grh-compact's `stepanov_count`): if a nonzero polynomial over `R` is divisible
by `(X - ι x)^E` at every point `x` of a local ring `W` with `q` residue classes, its degree is at
least `E q`. -/
alias stepanov := stepanov_count

/-- Stepanov's inequality for the level: the `m` lifts on the scale `b` fit in the level,
`m · log b ≤ log N`. -/
theorem level_stepanov {P : Parameters} (D : Data P) : (D.m : ℝ) * D.logB ≤ Real.log D.N :=
  D.log_N_mem_Icc.1

/-- Multiplicity one above the square root in the Chebyshev–Erdős certificate. -/
alias erdos_multiplicity_one := centralBinom_factorization_le_one

end Structural
