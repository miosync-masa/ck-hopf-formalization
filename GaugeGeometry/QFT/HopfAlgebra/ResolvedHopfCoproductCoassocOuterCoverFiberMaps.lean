import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocOuterCoverSigmaUnification

/-!
# R-6c-body-56 — outer↔cover fiber-map skeleton: the two H5.8 coverage supplies

Fifty-sixth genuine-body step.  body-55 closed the σ-cover reindex FORM (`resolved_outer_cover_fibration`, the
shared fibration engine).  Its decision: the image / branch reindexes share that one form but need TWO different
fiber maps.  This step TYPES those two fiber maps as named supplies — the resolved-native face of R-4-full's
outer × inner double sum — and threads them back to body-54's `ResolvedOuterCoverSigmaSupply`.

## The two supplies

Each supply carries exactly the data the fibration engine consumes on ONE side:

* `ResolvedOuterImageFiberSupply F` — the IMAGE fiber map (the coassoc-RIGHT / quotient decomposition):
  `forestFiber` / `mixedFiber` (cover subtype → outer forest), their `maps_to` (into the outer carrier), and
  the per-`A` agreement (the image outer summand `A` = split-term sum of `A`'s fiber, forest ⊕ mixed);
* `ResolvedOuterBranchFiberSupply F` — the BRANCH fiber map (the coassoc-LEFT decomposition): the same shape,
  with the branch outer summand.

Both feed the SAME engine (`resolved_outer_cover_fibration`); the image / branch summands and the two fiber
maps are the only difference — exactly body-55's "one form, two fiber maps".

## The wiring

* `ResolvedOuterImageFiberSupply.outer_image_cover` — the engine at the image summand + image fiber map;
* `ResolvedOuterBranchFiberSupply.outer_branch_cover` — the engine at the branch summand + branch fiber map
  (`.symm`, matching body-54's stated direction);
* `toOuterCoverSigmaSupply` — the two supplies bundle to body-54's `ResolvedOuterCoverSigmaSupply`, hence via
  `.image_cover_reindex` / `.branch_cover_reindex` (body-54) to body-38's reindexes and on to `coassoc_gen`.

So the OUTPUT reindex leaf is now `partition bridge (body-53)` + `shared fibration engine (body-55)` +
`ImageFiberSupply + BranchFiberSupply (body-56)`.

Per the HALT, the actual quotient / left fiber CONSTRUCTIONS are NOT built; only the two fiber maps + their
maps-to + per-`A` agreements are TYPED as supply fields (the cover / disjoint facts live inside the engine's
`Finset.sum_fiberwise_of_maps_to`, so no separate cover-proof obligation surfaces here).  The image and branch
fiber maps stay as TWO systems — not forced onto one carrier.

Landed:

* `ResolvedOuterImageFiberSupply` / `ResolvedOuterBranchFiberSupply` — the two H5.8 coverage supplies;
* `.outer_image_cover` / `.outer_branch_cover` — each side via the shared engine;
* `toOuterCoverSigmaSupply` — the bundle to body-54's skeleton.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

set_option linter.unusedSectionVars false

/-- **R-6c-body-56 — the IMAGE fiber-map supply** (the coassoc-RIGHT / quotient decomposition).  Carries the
split-choice cover → outer forest fiber maps (forest ⊕ mixed), their maps-into-the-outer-carrier, and the
per-`A` agreement (image outer summand `A` = split-term sum over `A`'s fiber).  This is exactly one side of
body-55's fibration engine. -/
structure ResolvedOuterImageFiberSupply (F : ResolvedCoassocGrandFullSupply D G) where
  /-- The forest-cover fiber map: each surviving-forest split choice lands over an outer forest. -/
  forestFiber : {s : ResolvedCoassocSplitChoice D G //
      F.ImageTerm.toImageSideTermSupply.toSplitPhiData.discriminator
        (F.ImageTerm.toImageSideTermSupply.toSplitPhiData.imageOf s)} → (D.supply G).ForestIdx
  /-- The mixed-cover fiber map: each mixed split choice lands over an outer forest. -/
  mixedFiber : {s : ResolvedCoassocSplitChoice D G //
      ¬ F.ImageTerm.toImageSideTermSupply.toSplitPhiData.discriminator
        (F.ImageTerm.toImageSideTermSupply.toSplitPhiData.imageOf s)} → (D.supply G).ForestIdx
  /-- The forest fiber map lands in the outer forest carrier. -/
  forestFiber_maps_to : ∀ q ∈ F.forestCarrier, forestFiber q ∈ (D.supply G).forestCarrier
  /-- The mixed fiber map lands in the outer forest carrier. -/
  mixedFiber_maps_to : ∀ q ∈ F.mixedCarrier, mixedFiber q ∈ (D.supply G).forestCarrier
  /-- The image outer summand for `A` equals the split-term sum over `A`'s fiber (forest ⊕ mixed). -/
  image_fiber_agree : ∀ A ∈ (D.supply G).forestCarrier,
    ((1 : ResolvedHopfH) ⊗ₜ[ℚ] ((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A)
        + D.coassocRightTail ((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A))
      = (∑ q ∈ F.forestCarrier with forestFiber q = A, D.resolvedSplitChoiceTerm q.1)
        + (∑ q ∈ F.mixedCarrier with mixedFiber q = A, D.resolvedSplitChoiceTerm q.1)

/-- **R-6c-body-56 — the BRANCH fiber-map supply** (the coassoc-LEFT decomposition).  Same shape as the image
supply, with the branch outer summand. -/
structure ResolvedOuterBranchFiberSupply (F : ResolvedCoassocGrandFullSupply D G) where
  /-- The forest-cover fiber map for the branch side. -/
  forestFiber : {s : ResolvedCoassocSplitChoice D G //
      F.ImageTerm.toImageSideTermSupply.toSplitPhiData.discriminator
        (F.ImageTerm.toImageSideTermSupply.toSplitPhiData.imageOf s)} → (D.supply G).ForestIdx
  /-- The mixed-cover fiber map for the branch side. -/
  mixedFiber : {s : ResolvedCoassocSplitChoice D G //
      ¬ F.ImageTerm.toImageSideTermSupply.toSplitPhiData.discriminator
        (F.ImageTerm.toImageSideTermSupply.toSplitPhiData.imageOf s)} → (D.supply G).ForestIdx
  /-- The forest fiber map lands in the outer forest carrier. -/
  forestFiber_maps_to : ∀ q ∈ F.forestCarrier, forestFiber q ∈ (D.supply G).forestCarrier
  /-- The mixed fiber map lands in the outer forest carrier. -/
  mixedFiber_maps_to : ∀ q ∈ F.mixedCarrier, mixedFiber q ∈ (D.supply G).forestCarrier
  /-- The branch outer summand for `A` equals the split-term sum over `A`'s fiber (forest ⊕ mixed). -/
  branch_fiber_agree : ∀ A ∈ (D.supply G).forestCarrier,
    ((Algebra.TensorProduct.assoc ℚ ℚ ℚ ResolvedHopfH ResolvedHopfH ResolvedHopfH).toAlgHom
          (((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A) ⊗ₜ[ℚ] (1 : ResolvedHopfH))
        + D.coassocLeftTail ((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A))
      = (∑ q ∈ F.forestCarrier with forestFiber q = A, D.resolvedSplitChoiceTerm q.1)
        + (∑ q ∈ F.mixedCarrier with mixedFiber q = A, D.resolvedSplitChoiceTerm q.1)

/-- **R-6c-body-56 — the image side via the shared engine.**  body-55's `resolved_outer_cover_fibration` at the
image summand + the image fiber map. -/
theorem ResolvedOuterImageFiberSupply.outer_image_cover {F : ResolvedCoassocGrandFullSupply D G}
    (S : ResolvedOuterImageFiberSupply F) :
    (∑ A ∈ (D.supply G).forestCarrier,
        ((1 : ResolvedHopfH) ⊗ₜ[ℚ] ((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A)
          + D.coassocRightTail ((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A)))
      = (∑ q ∈ F.forestCarrier, D.resolvedSplitChoiceTerm q.1)
          + (∑ q ∈ F.mixedCarrier, D.resolvedSplitChoiceTerm q.1) :=
  resolved_outer_cover_fibration F _ D.resolvedSplitChoiceTerm S.forestFiber S.mixedFiber
    S.forestFiber_maps_to S.mixedFiber_maps_to S.image_fiber_agree

/-- **R-6c-body-56 — the branch side via the shared engine.**  body-55's `resolved_outer_cover_fibration` at the
branch summand + the branch fiber map, oriented to match body-54's `outer_branch_cover`. -/
theorem ResolvedOuterBranchFiberSupply.outer_branch_cover {F : ResolvedCoassocGrandFullSupply D G}
    (S : ResolvedOuterBranchFiberSupply F) :
    (∑ q ∈ F.forestCarrier, D.resolvedSplitChoiceTerm q.1)
      + (∑ q ∈ F.mixedCarrier, D.resolvedSplitChoiceTerm q.1)
      = ∑ A ∈ (D.supply G).forestCarrier,
          ((Algebra.TensorProduct.assoc ℚ ℚ ℚ ResolvedHopfH ResolvedHopfH ResolvedHopfH).toAlgHom
              (((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A) ⊗ₜ[ℚ] (1 : ResolvedHopfH))
            + D.coassocLeftTail ((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A)) :=
  (resolved_outer_cover_fibration F _ D.resolvedSplitChoiceTerm S.forestFiber S.mixedFiber
    S.forestFiber_maps_to S.mixedFiber_maps_to S.branch_fiber_agree).symm

/-- **R-6c-body-56 — the two fiber supplies bundle to body-54's σ-cover skeleton.**  Image + branch fiber
supplies give `ResolvedOuterCoverSigmaSupply`, hence (body-54) the reindexes and on to `coassoc_gen`. -/
def toOuterCoverSigmaSupply {F : ResolvedCoassocGrandFullSupply D G}
    (SI : ResolvedOuterImageFiberSupply F) (SB : ResolvedOuterBranchFiberSupply F) :
    ResolvedOuterCoverSigmaSupply F where
  outer_image_cover := SI.outer_image_cover
  outer_branch_cover := SB.outer_branch_cover

end GaugeGeometry.QFT.Combinatorial
