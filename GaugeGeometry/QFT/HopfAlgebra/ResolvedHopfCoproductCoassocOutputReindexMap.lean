import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocOuterCoverFiberMaps
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRegroupReindexBody

/-!
# R-6c-body-57 — the OUTPUT reindex final map (capstone + consolidation)

Fifty-seventh genuine-body step, a CONSOLIDATION fixing the OUTPUT (outer-forest ↔ splitPhi-cover) reindex in
its final, fully-factored form after bodies 52–56 reshaped the picture.  No new geometry: a docstring map plus
one thin capstone re-export from body-56's fiber supplies to `coassoc_gen`.

## The final OUTPUT chain

```text
coassoc_gen  (per generator x : ResolvedHopfGen)
  ⇐ ResolvedRegroupReindexSupply.coassoc_gen                                    (body-38)
  ⇐ image_cover_reindex x / branch_cover_reindex x                             (body-38 fields, per x)
  ⇐ ResolvedOuterCoverSigmaSupply.image_cover_reindex / .branch_cover_reindex   (body-54, at F := grand x)
  ⇐ ResolvedOuterCoverSigmaSupply                                              (body-54 skeleton)
  ⇐ toOuterCoverSigmaSupply (imageFiber) (branchFiber)                          (body-56)
  ⇐ ┌ partition bridge            grandFull_partition_reindex / …_imageWeight… (body-53 / body-54)
    ├ shared fibration engine      resolved_outer_cover_fibration               (body-55)
    └ ImageFiberSupply + BranchFiberSupply                                      (body-56, the two fiber maps)
```

## The flat/resolved mismatch (body-52), settled

`ResolvedHopfH ≠ HopfH` (NOT `rfl`).  R-4-full's CONCRETE reindex engines (`outer_sum_reindex`,
`concrete_sum_reindex`) land in the FLAT `HopfH` carrier and do NOT transport to `ResolvedHopfH3`.  What DID
survive is the reindex PATTERNS, re-proved resolved-natively:

* the PARTITION pattern — `grandFull_partition_reindex` (body-53), from the GrandFull cover + body-39 `cross`;
* the FIBRATION pattern — `resolved_outer_cover_fibration` (body-55), the generic `AddCommMonoid` σ-cover
  fibration engine.

So the OUTPUT reindex is entirely resolved-native; no flat carrier, no `forgetHopf`, no facade re-import.

## Remaining primitive OUTPUT leaves (the ONLY unproved OUTPUT obligations)

Everything else in the OUTPUT chain is PROVED.  What remains are the two fiber-map supplies' fields (body-56),
i.e. the resolved-native H5.8 outer × inner coverage geometry, not yet constructed:

* `ResolvedOuterImageFiberSupply` (image = coassoc-RIGHT / quotient decomposition):
  `forestFiber`, `mixedFiber`, `forestFiber_maps_to`, `mixedFiber_maps_to`, `image_fiber_agree`;
* `ResolvedOuterBranchFiberSupply` (branch = coassoc-LEFT decomposition): the same five, `branch_fiber_agree`.

The two fiber CONSTRUCTIONS (`forestFiber` / `mixedFiber` as split-choice ↦ parent outer forest, plus the
per-`A` agreement) are the deepest OUTPUT geometry and stay TWO systems — the image side factoring through the
quotient, the branch side through the left leg.  The cover / disjoint facts are absorbed inside the engine's
`Finset.sum_fiberwise_of_maps_to`, so no separate cover obligation surfaces — only `maps_to` + fiberwise
agreement per side.

## The capstone

`resolved_output_reindex_of_fibers` — given a representative family (`repGraph` / `repCD` / `rep_eq` / `grand`,
the support-9 lift, INPUT-side leaves) and the two per-`x` fiber supplies, produce `coassoc_gen`.  A thin
re-export: `toOuterCoverSigmaSupply` (body-56) feeds `ResolvedRegroupReindexSupply` (body-38) via body-54's two
reindexes, then `.coassoc_gen`.  Reads: **the OUTPUT reindex is fully proved except the two fiber supplies.**

Per the HALT, no fiber construction is entered; only a thin adapter / re-export.

Landed:

* `resolved_regroupReindex_of_fibers` — assemble `ResolvedRegroupReindexSupply` from the fiber families;
* `resolved_output_reindex_of_fibers` — the capstone to `coassoc_gen`.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData}

set_option linter.unusedSectionVars false

/-- **R-6c-body-57 — the OUTPUT reindex supply from the two fiber families.**  A representative family plus, for
each generator, an image and a branch fiber supply assemble body-38's `ResolvedRegroupReindexSupply`: each
per-`x` cover reindex is body-54's reindex on the bundled `toOuterCoverSigmaSupply`. -/
noncomputable def resolved_regroupReindex_of_fibers
    (repGraph : ResolvedHopfGen → ResolvedFeynmanGraph)
    (repCD : ∀ x : ResolvedHopfGen, (repGraph x).forget.toClass.IsConnectedDivergent)
    (rep_eq : ∀ x : ResolvedHopfGen, x = (repGraph x).toResolvedHopfGen (repCD x))
    (grand : ∀ x : ResolvedHopfGen, ResolvedCoassocGrandFullSupply D (repGraph x))
    (imageFib : ∀ x : ResolvedHopfGen, ResolvedOuterImageFiberSupply (grand x))
    (branchFib : ∀ x : ResolvedHopfGen, ResolvedOuterBranchFiberSupply (grand x)) :
    ResolvedRegroupReindexSupply D where
  repGraph := repGraph
  repCD := repCD
  rep_eq := rep_eq
  grand := grand
  image_cover_reindex := fun x =>
    (toOuterCoverSigmaSupply (imageFib x) (branchFib x)).image_cover_reindex
  branch_cover_reindex := fun x =>
    (toOuterCoverSigmaSupply (imageFib x) (branchFib x)).branch_cover_reindex

/-- **R-6c-body-57 — the OUTPUT reindex capstone.**  From the representative family and the two per-`x` fiber
supplies, `Δᵣ`-coassociativity on every generator.  Thin re-export: body-56's `toOuterCoverSigmaSupply` →
body-38's `ResolvedRegroupReindexSupply` → `.coassoc_gen`.  The OUTPUT reindex is fully proved except the two
fiber supplies. -/
theorem resolved_output_reindex_of_fibers
    (repGraph : ResolvedHopfGen → ResolvedFeynmanGraph)
    (repCD : ∀ x : ResolvedHopfGen, (repGraph x).forget.toClass.IsConnectedDivergent)
    (rep_eq : ∀ x : ResolvedHopfGen, x = (repGraph x).toResolvedHopfGen (repCD x))
    (grand : ∀ x : ResolvedHopfGen, ResolvedCoassocGrandFullSupply D (repGraph x))
    (imageFib : ∀ x : ResolvedHopfGen, ResolvedOuterImageFiberSupply (grand x))
    (branchFib : ∀ x : ResolvedHopfGen, ResolvedOuterBranchFiberSupply (grand x))
    (x : ResolvedHopfGen) :
    D.coassocLeft (MvPolynomial.X x) = D.coassocRight (MvPolynomial.X x) :=
  (resolved_regroupReindex_of_fibers repGraph repCD rep_eq grand imageFib branchFib).coassoc_gen x

end GaugeGeometry.QFT.Combinatorial
