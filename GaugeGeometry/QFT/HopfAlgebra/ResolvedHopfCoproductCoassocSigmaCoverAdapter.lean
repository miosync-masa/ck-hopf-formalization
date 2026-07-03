import GaugeGeometry.QFT.HopfAlgebra.ResolvedActualSigmaCover
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRegroupReindexBody

/-!
# R-6c-body-52 — σ-cover adapter scout: the flat/resolved carrier mismatch, and the one reusable engine

Fifty-second genuine-body step, a WIRING scout of body-50's four σ-cover adapters against the R-4-full reindex
engines — with a decisive carrier finding that re-scopes the adapter list.

## Decisive finding: R-4-full's concrete engines are FLAT, the R-6c reindex is RESOLVED

`ResolvedHopfH = HopfH` is **NOT** definitional (`rfl` fails: type mismatch).  The R-4-full concrete reindex
engines land in the FLAT carrier:

* `ResolvedH58FullGrainOuterSkeleton.outer_sum_reindex` : `∑ A ∈ h58BridgeOuterCarrier g, innerImageSum A =
  ∑ A innerBranchSum A` with `innerImageSum A : HopfH ⊗[ℚ] (HopfH ⊗[ℚ] HopfH)`;
* `ResolvedActualSigmaCoverSupply.concrete_sum_reindex` : sums of `HopfH`-valued `quotientTerm` /
  `splitChoiceTerm`.

Body-38/50's `image_cover_reindex` / `branch_cover_reindex` land in `ResolvedHopfH3 = ResolvedHopfH ⊗ …`.  Since
`ResolvedHopfH ≠ HopfH`, **the flat concrete engines do NOT apply verbatim** — body-50's "re-carriered flat
engines" premise was too optimistic.  (This is expected: R-6c reconstructs coassoc NATIVELY on the resolved
carrier precisely to avoid the flat facades; re-importing the flat reindex would re-introduce the flat carrier.)

## What IS reusable: the ABSTRACT partition reindex

`ResolvedFiniteBranchMapLayer.sum_reindex (FL) (w : FL.layer.Image → M)` is generic over `[AddCommMonoid M]`, so
it applies at `M = ResolvedHopfH3` unchanged.  Instantiated below as `resolved_partition_reindex`, it gives the
image ↔ forest ⊕ mixed cover PARTITION for the RESOLVED carrier — the carrier-agnostic half.  Its `FL` needs a
resolved `ResolvedFiniteBranchMapLayer` built from the GrandFull cover; body-39's
`grandFull_forest_image_ne_mixed_image` is the `cross` (`layer.cross`) ingredient.

## Re-scoped adapter list (the corrected picture)

| body-50 adapter | status after the carrier finding |
|---|---|
| (2) cover ident / PARTITION (imageCarrier ↔ forest+mixed) | **reusable** via abstract `sum_reindex` at `ResolvedHopfH3` + a resolved `FL` (GrandFull carriers + body-39 `cross`) |
| (1) outer carrier ident | resolved-native: `(D.supply G).forestCarrier` is already the resolved outer carrier — NOT `h58BridgeOuterCarrier g` (flat/`HopfGen`) |
| (3) weight ident | resolved-native: `imageWeight` / `resolvedSplitChoiceTerm` are `ResolvedHopfH3`-valued — NOT the flat `quotientTerm`/`splitChoiceTerm` |
| (4) summand ident / OUTER connection | **resolved construction needed**: the outer-forest ↔ cover coverage must be built resolved-natively (the flat `outer_sum_reindex` does not transport); this is a genuine resolved σ-cover, not a flat re-carriering |

So the σ-cover adapter is NOT a flat-engine re-wiring.  The partition half reuses the abstract `sum_reindex`;
the outer↔cover half is a resolved-native σ-cover construction (paralleling R-4-full's `ResolvedActualSigmaCover`
but over `ResolvedHopfH3`).  Per the HALT, no R-4-full proof body is entered, no `Quot.sound`/representative is
touched — the mismatch table is fixed and the reusable engine is surfaced.

Landed:

* `resolved_partition_reindex` — the abstract `ResolvedFiniteBranchMapLayer.sum_reindex` at `M = ResolvedHopfH3`
  (the one carrier-agnostic engine, reusable for the RESOLVED cover partition).

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

set_option linter.unusedSectionVars false in
/-- **R-6c-body-52 — the abstract H5.8 partition reindex at the RESOLVED carrier `ResolvedHopfH3`.**  Just
`ResolvedFiniteBranchMapLayer.sum_reindex` (generic `AddCommMonoid`) at `M = ResolvedHopfH3` — confirming the
one R-4-full engine that survives the flat/resolved carrier boundary. -/
theorem resolved_partition_reindex (FL : ResolvedFiniteBranchMapLayer)
    (w : FL.layer.Image → ResolvedHopfH3) :
    ∑ z ∈ FL.imageCarrier, w z =
      (∑ q ∈ FL.forestCarrier, w (FL.layer.forestImage q)) +
        (∑ q ∈ FL.mixedCarrier, w (FL.layer.mixedImage q)) :=
  FL.sum_reindex w

end GaugeGeometry.QFT.Combinatorial
