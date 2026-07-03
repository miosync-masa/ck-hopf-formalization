import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocResolvedOuterCoverSigma

/-!
# R-6c-body-55 — outer↔cover σ-reindex unification scout: shared fibration form, two fiber maps

Fifty-fifth genuine-body step, a SCOUT judging whether body-54's two σ-cover reindexes (`outer_image_cover`,
`outer_branch_cover`) collapse to one carrier bijection + weight agreements.

## Decision: NOT one bijection — one shared fibration FORM with two DIFFERENT fiber maps

Both reindexes have the shape `∑ A ∈ (D.supply G).forestCarrier, (outer summand A) = ∑ forestCarrier splitTerm
+ ∑ mixedCarrier splitTerm` — the SAME split-term cover target (body-54), but DIFFERENT source summands: the
image summand is the coassoc-RIGHT tail `1 ⊗ (leftTerm A ⊗ rightTerm A) + coassocRightTail …` (the quotient
decomposition), the branch summand the coassoc-LEFT tail `assoc((…) ⊗ 1) + coassocLeftTail …`.  A single
carrier bijection with a weight-only difference is therefore IMPOSSIBLE: it would force `image summand A =
branch summand A` per `A`, false in general (that per-`A` inequality IS the coassoc content).

Instead each reindex is a σ-cover FIBRATION: the split-choice cover fibered over the outer forest carrier, with
the outer summand `A` equal to the split-term sum of `A`'s fiber.  Both share this fibration FORM — the generic
`Finset.sum_fiberwise_of_maps_to` engine below — but with DIFFERENT fiber maps (`imageFiber` via the quotient
decomposition, `branchFiber` via the left decomposition).  So they unify to `{one fibration lemma} + {two
(fiberMap, per-A agreement) instances}`, not to one bijection.

## The shared engine

`resolved_outer_cover_fibration`: given a fiber map (cover → outer forest, mapping into the outer carrier) and a
per-`A` agreement (outer summand `A` = split-term sum of `A`'s fiber), the outer summand sum equals the full
split-term cover sum — by `Finset.sum_fiberwise_of_maps_to` on each of the forest / mixed carriers.  Applied
with the image summand + `imageFiber` gives `outer_image_cover`; with the branch summand + `branchFiber` gives
`outer_branch_cover`.

Per the HALT, the concrete fiber maps (the σ-cover bijection data) are NOT built; only the shared fibration form
is fixed, and the two-vs-one question is decided (two fiber maps, one form).

Landed:

* `resolved_outer_cover_fibration` — the shared σ-cover fibration engine (`∑ A summand = ∑ split-term cover`
  from a fiber map + per-`A` agreement), for any `M`.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

set_option linter.unusedSectionVars false in
/-- **R-6c-body-55 — the shared σ-cover fibration engine.**  A fiber map from the split-choice cover to the
outer forest carrier, with the per-`A` agreement (outer summand `A` = split-term sum of `A`'s fiber), gives the
outer summand sum = the full split-term cover sum.  Applied with the image / branch summand + the respective
fiber map, this yields body-54's `outer_image_cover` / `outer_branch_cover` — one form, two fiber maps. -/
theorem resolved_outer_cover_fibration {M : Type*} [AddCommMonoid M]
    (F : ResolvedCoassocGrandFullSupply D G)
    (summand : (D.supply G).ForestIdx → M)
    (weight : ResolvedCoassocSplitChoice D G → M)
    (forestFiber : {s : ResolvedCoassocSplitChoice D G //
        F.ImageTerm.toImageSideTermSupply.toSplitPhiData.discriminator
          (F.ImageTerm.toImageSideTermSupply.toSplitPhiData.imageOf s)} → (D.supply G).ForestIdx)
    (mixedFiber : {s : ResolvedCoassocSplitChoice D G //
        ¬ F.ImageTerm.toImageSideTermSupply.toSplitPhiData.discriminator
          (F.ImageTerm.toImageSideTermSupply.toSplitPhiData.imageOf s)} → (D.supply G).ForestIdx)
    (hforest : ∀ q ∈ F.forestCarrier, forestFiber q ∈ (D.supply G).forestCarrier)
    (hmixed : ∀ q ∈ F.mixedCarrier, mixedFiber q ∈ (D.supply G).forestCarrier)
    (hagree : ∀ A ∈ (D.supply G).forestCarrier,
      summand A = (∑ q ∈ F.forestCarrier with forestFiber q = A, weight q.1)
        + (∑ q ∈ F.mixedCarrier with mixedFiber q = A, weight q.1)) :
    ∑ A ∈ (D.supply G).forestCarrier, summand A =
      (∑ q ∈ F.forestCarrier, weight q.1) + (∑ q ∈ F.mixedCarrier, weight q.1) := by
  classical
  rw [Finset.sum_congr rfl hagree, Finset.sum_add_distrib,
    Finset.sum_fiberwise_of_maps_to hforest, Finset.sum_fiberwise_of_maps_to hmixed]

end GaugeGeometry.QFT.Combinatorial
