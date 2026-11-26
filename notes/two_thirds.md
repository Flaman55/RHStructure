# Reconstructing the 2/3 (research note, not part of the paper's claims)

Status: hypothesis with a proved algebraic core (`Structural/Exponent.lean`). Candidate for a
separate Palomar entry if the cost model can be stated and proved from grh-compact.

## What the sources say

- Alpöge, remark, item 14: a precise computation of the cost of each lift shows that one would
  stop at 2/3 a priori; then the attempt to kill via twisting, and the need for "division".
  Item 17: for the H^1 classes that twisting could not kill, a weakening of Vandiver.
- The remark does not give the 2/3 computation. grh-compact proves only the final bound.

## What grh-compact shows about the cost (commit 72fead1)

- `Data.allowedLoss` (Columns/SizeEstimates): 3·loss(p) at a non-split p < x₁, `4 m f b` at the
  level N, 0 elsewhere; `loss p = f (log b)² a/p`, times m if p is short (p ≡ ±1 mod m).
- `sum_allowedLoss_mul_log_le`: all allowed losses times log p fit in `budget = f a (log b)³`.
- The lever (`Structural.level_double_charge`, `lifts_sq_le`): `4 m f b · log N ≤ f a (log b)³`
  with `log N ≥ m log b` gives `m² b ≲ a (log b)²`, so m ≲ √x and the saving x^(−1/2).
- Columns/LocalStatement: "each lift may lose divisibility at an inert prime p pairing two tops,
  but outside a sparse set of p the chain regains the predicted power of p, up to about one
  lift's loss". The sparse set is the short primes, where the loss carries the factor m.
- `Data.IsFitFamily` / `exists_isFitFamily` (Selmer/FitTwists, FitTwistsExist): one twist ϑ per
  ℓ-adic embedding such that its first m powers have few congruences; the denominators of the
  projections to the lifts sum to at most `B₀ = budget/(m k)` per rank and dimension.
- Selmer/TwistForRows: one twist makes, for each of its first m powers, all Selmer groups short.

## The algebra (proved, `Structural/Exponent.lean`)

If the loss charged to the level grows like m^α (instead of m), the two charges give
m^(α+1) b ≲ a (log b)², so m ≲ x^(1/(α+1)), the saving is x^(−1/(α+1)), and the zero-free
half-plane is Re s > 1 − 1/(α+1). α = 1 gives 1/2 (grh-compact); α = 2 gives 2/3.

## Hypothesis

Without the fit twists, the cost of the m-fold chain is quadratic in m (α = 2). Two candidate
sources, not yet separated:

1. Pairwise congruences among the powers ϑ, ϑ², …, ϑ^m: about m²/2 pairs, each able to cost
   about one lift's loss.
2. Selmer length growing with the power j: if the untwisted Selmer group of ϑ^j costs about j
   units, the total over j ≤ m is about m²/2.

Either gives α = 2, hence 2/3; the fit twists bring the cost back to one unit per lift (α = 1),
hence 1/2. This would match item 14 ("cost of each lift … 2/3 a priori … kill via twisting").

## What would turn this into a theorem

- State the cost of the untwisted chain at the level in grh-compact's terms (which lemma would
  replace `IsFitFamily` with a trivial twist, and what it can prove), and show it is Θ(m²)·f b.
- Then `lever_two_thirds` gives the 2/3 exactly, and `lever_one_half` the 1/2.
- An experiment in the style of `patch_theta_v3.py` (on the PC, overnight): replace the
  `B₀` budget of `IsFitFamily` by `m · B₀` and record which inequality breaks first.
