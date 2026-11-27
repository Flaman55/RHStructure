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

## Step 1 (paper analysis, 2026-11-27): where the budgets enter

Sources: grh-compact 72fead1, Endgame/LongForms, Rows/LiftVolumeHeight, Selmer/FitTwists,
Columns/SizeEstimates, Columns/TwistedHeckeType, Seesaw/IndexTypes, Seesaw/LiftCharacters.

### How the saving is produced

- Lower bound (Theorem C, `Data.integral_forms_long`): `D (h_main − 3 fa log⁴ b) ≤ V + 2δ`.
  Each of the m lifts has height `D k (B₀ log b − 𝖴)` (`heightLe_liftVolume_ratio`); with
  `m k B₀ = budget` and `m k 𝖴 = h_main` the m lifts together lose `D · log b · budget`.
- Upper bound (Theorems A, B): `V + 2δ ≲ D (h_main − m · rem + O(log b · budget))`.
- Together: `m · rem ≲ log b · budget`. With rem ≈ #tops · a · ε and budget = f a (log b)³ this
  is `ε ≲ (log b)⁴ / m`: the saving is 1/m, and the lever (m ≲ √x) gives x^(−1/2).

### Consequence 1: the Selmer budget cannot be the source of 2/3 by a simple scaling

If the denominators of the untwisted chain were bounded only by `m^β` times the fit budget,
the lower bound would lose `m^β · log b · budget`, so `ε ≲ m^(β−1)`, and with m ≲ √x the edge
would be `(1 + β)/2`. A quadratic total (β = 1, "Selmer length growing with j") gives no saving
at all, not 2/3; 2/3 would need β = 1/3, which has no natural source. Candidate 2 of the
hypothesis is therefore refuted as stated. The experiment "replace B₀ by m·B₀" is predictable
(Theorem C collapses) and not worth running.

### Consequence 2: the level is the natural place for 2/3

`lever_power`: if the loss charged to N grows like m^α, the edge is 1 − 1/(α+1); 2/3 needs α = 2.
The loss at N (`allowedLoss N = 4 m f b`) comes from one step: "trading denominators at the
level prime for a column operator" (Columns/TwistedHeckeType, `chain₂_pairTranslates_eq_smul_chain`):
the chain of ϱ+1 pairs of lifts (ϱ = m/2 − 1, Seesaw/IndexTypes) equals a scalar t with
‖t‖ ≤ N^(4fb(ϱ+1)) times a chain with data given mod N, after a power F^(ϱ+1) of a Gauss-sum
Hecke operator; the index cost is ≤ 4mfb·dim(columns) (`exists_indexDvd_fourierOp_pow`).
Extracting the scalar t is a division. Hypothesis (refined): Alpöge's "need for division" is
this step, and without it the denominator at N of the m-fold chain grows quadratically in m,
which by `lever_two_thirds` gives exactly 2/3.

To check next (paper, no PC): the valuation at N of the untraded chain — whether the j-th datum
(`diagPointN j`, weights w_j = b₁ + j h + h₂ ≤ 2b, `norm_detCharAt_diagN_le`) carries a
denominator growing with j, or whether pairs of lifts interact at N.

### Consequence 3: experiments below θ = 5/11 are blocked before the lever

The two rejections at θ = 2/5 are both on the divisibility side and both come from the tower
2^s = m^22 against r² ~ x^10: Selmer/ThickSpacing (crystalline losses above ℓ, part of
Selmer/RibetElement) and Curve/DepthPairs (some jet no more divisible than predicted, part of
Rows/GluedFormTheta). A build at θ = 1/3 stops there and says nothing about the 2/3.

### Status

No PC experiment is informative yet. Removing the division means removing a proof, not changing
a number, so the test of the refined hypothesis is first a computation on paper of the untraded
chain's valuation at N.

## Step 2 (2026-11-27): the triangle of the chain

Prompted by A. Flamandzki's distinction between walking by n (each step pays for the whole state)
and walking by p (each step pays its increment, with its own reduction).

Found in grh-compact 72fead1:

- `Data.volume_iota_eq_prod_liftVolume` (Rows/RowVolume): the volume of the chain is
  `𝔷(ϑ) = |c(ϑ)|^D · ∏_{j=1}^m λ_j(ϑ^j)`: a product of single-lift volumes (increments) times one
  constant c, and c costs m·m squares (`D.CostsSquares (D.m * D.m) c`).
- The constant comes from `exists_isTriangle` (Exchange/TriangleArrows, TriangleNorms): an abstract
  triangle of maps in which the Gram determinant factors over the first arrows; the pairs (i, j)
  of lifts give exchange constants, each costing one square (Exchange/CostOfSquares, RowLadder).
  `crude_rows` similarly costs 2m² squares.
- One square costs `2 t x^999` (`Data.CostsSquares`): a scale in x alone, independent of b and of
  the level N. In `heightLe_volume_ratio_sq` the whole triangle, `2 m² t x^999`, is absorbed by
  `2 log b · budget` with room to spare.

Reading: the "pay for the state" structure is present (a triangle of about m² pair terms), and the
proof moves it to a scale where it is negligible; the b-scale and N-scale costs fall only on the
increments (the m single lifts, and the ϱ+1 ≈ m/2 pairs traded at N).

Refined hypothesis: if the pair terms of the triangle were charged at the scale of the level, about
f b each with weight log N ≥ m log b, the charge would be m² · f b · m log b ≲ f a (log b)³, i.e.
m³ ≲ x, the edge 2/3 (`lever_two_thirds`). With the pair terms at scale x^999 and only increments at
N, the charge is m · f b · m log b, i.e. m² ≲ x, the edge 1/2.

Still to check: which steps put the pair terms at scale x^999 (the seesaw identity with
denominators away from the conductor, New/Seesaw/SeesawTheorem; the trade at N,
Columns/TwistedHeckeType), and whether without them the pair terms carry N-adic denominators.

## Step 3 (2026-11-27): what keeps the triangle on the low floor

Following A. Flamandzki's suggestion to set the scales (towers) side by side and see what each
one carries.

- The triangle (Exchange/TriangleNorms, `IsTriangle`) is a grid of lifts `a` and descents `d`
  indexed by (i, n); its `square_law` says that going around one grid square costs one exchange
  constant β with `M 1 β` (one square). Its vertices are positions in the chain (groups), not
  scales; the scale enters through the price of a square.
- `Data.CostsSquares` is defined only for fit twists: "for each family θ of fit twists
  (`Data.IsFitFamily`), |c(θ_ι)/c(1)|⁻² has height ≤ 2 n t x^999".
- The exchange constants are rewritten through L-value ratios and conductor norms
  (Exchange/TriangleLevelExponent), and their height is bounded by
  `IsFitFamily.heightLe_of_eq_zpow_mul` from the field `IsFitFamily.height_le`: inverse ratios of
  Hecke values of ramified pairs have height ≤ x^999 at the twists ϑ_ι^j.
- Selmer/TwistForRows: the twist makes "the ratios of twisted to untwisted Hecke values barely
  divisible by ℓ, which limits congruences".

So the same twists do two jobs on two floors: on floor b they keep the denominators of each lift
within B₀ (`denominator_le`); on floor x they keep each square of the triangle at height x^999
(`height_le`). The second job is what keeps the ~m² pair terms negligible.

Refined hypothesis: without the twists, the Hecke-value ratios at the squares of the triangle are
not bounded by x^999 (ℓ-adic divisibility of L-values is uncontrolled), the pair terms leave floor
x, and charged like the increments they give m³ ≲ x, the edge 2/3. This matches the remark's
"kill via twisting". Still a hypothesis: it needs the untwisted height of one square.
