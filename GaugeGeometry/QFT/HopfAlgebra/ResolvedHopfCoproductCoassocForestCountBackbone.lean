import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightRegionCount
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocTouchedLegLiftDatum
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocTouchedLocalizationEdge

/-!
# R-6c-body-435 — the forest count-exclusion backbone (PROVED)

Four-hundred-and-thirty-fifth genuine-body step — the `count`-safe backbone for the forest region exclusion.  The forest
parent has one term more than the right survivor: its internal edges split into the touched outer forest plus the
quotient-edge preimage (`localizedParentWithTouchedLegs`).  This body fixes the three directions that are pure
`count` arithmetic, leaving only the preimage retarget transport (with the touched↔whole star alignment) for the next
body.

* `count_internalEdges_add_complementEdges` — the generic ledger identity: `count e A.internalEdges +
  count e A.complementEdges = count e G.internalEdges`, from `A.internalEdges ≤ G.internalEdges` (pairwise-disjoint) and
  `Multiset.count_sub`.  This is the exact arithmetic that turns `< count e outer.I + count e outer.complementEdges` into
  `< count e G.internalEdges` at the end of the forest chain.
* `localizedParentWithTouchedLegs_count_internalEdges` — the additive decomposition of the parent count:
  `count e parent.internalEdges = count e touchedOuterForest.internalEdges + count e quotientEdgePreimage`
  (`Multiset.count_add` on the definitional `internalEdges = touchedOuterForest.internalEdges + quotientEdgePreimage`).
* `touchedOuterForest_count_internalEdges_le` — the touched bound: `count e touchedOuterForest.internalEdges ≤
  count e z.1.1.internalEdges`, from `touchedOuterForest_internalEdges_le` (`touchedOuterForest` is a sub-forest of the
  outer) via `Multiset.count_le_of_le`.

The remaining preimage transport `count e quotientEdgePreimage = count (retargetEdge e) δ.internalEdges` (widened `InjOn`
domain over `touchedOuterForest.complementEdges`, with the `whole_touched_retargetVertex_eq` / `touched_vertex_ok`
alignment and `quotientEdgePreimage_map` + `touchedLocalComponent_internalEdges`) and the full
`forestRegion_component_count_lt` are the dedicated next body; the closure assembly (raw-owner left/right/forest
classification + the body-431 witness bound) follows.

Per the HALT/guards: everything stays in `count` (no `∉`); the additive decomposition uses the parent's own definitional
`internalEdges` (no re-derivation); no forward-outer, identity, or cover.  No facade, no flat term, no `forgetHopf`, no
rep/perm, and NO strict `star_mapPerm` / `promote_collapse` / singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

set_option linter.unusedSectionVars false

namespace ResolvedAdmissibleSubgraph

variable {G : ResolvedFeynmanGraph}

/-- **R-6c-body-435 — the internal/complement count ledger.**  An edge's ambient count splits exactly into its count in
`A` and its count in `A`'s complement. -/
theorem count_internalEdges_add_complementEdges (A : ResolvedAdmissibleSubgraph G)
    (e : ResolvedFeynmanEdge) :
    Multiset.count e A.internalEdges + Multiset.count e A.complementEdges
      = Multiset.count e G.internalEdges := by
  have hle : A.internalEdges ≤ G.internalEdges :=
    resolvedAdmissibleSubgraph_internalEdges_le_of_pairwise A A.isPairwiseDisjoint
  have hcle : Multiset.count e A.internalEdges ≤ Multiset.count e G.internalEdges :=
    Multiset.count_le_of_le e hle
  show Multiset.count e A.internalEdges
    + Multiset.count e (G.internalEdges - A.internalEdges) = _
  rw [Multiset.count_sub]; omega

end ResolvedAdmissibleSubgraph

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-body-435 — the parent internal-edge count decomposition.**  The localized forest parent's internal edges are
the touched outer forest's plus the quotient-edge preimage, so their counts add. -/
theorem localizedParentWithTouchedLegs_count_internalEdges (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
    (datum : ResolvedTouchedLegLiftDatum z δ)
    (hE : ∀ e ∈ G.internalEdges, e.source ∈ G.vertices ∧ e.target ∈ G.vertices)
    (hL : ∀ ℓ ∈ G.externalLegs, ℓ.attachedTo ∈ G.vertices)
    (e : ResolvedFeynmanEdge) :
    Multiset.count e (localizedParentWithTouchedLegs z δ datum hE hL).internalEdges
      = Multiset.count e (touchedOuterForest z δ).internalEdges
        + Multiset.count e (quotientEdgePreimage (touchedOuterForest z δ) (D.starOf G z.1.1)
            (touchedLocalComponent z δ)) := by
  show Multiset.count e ((touchedOuterForest z δ).internalEdges
      + quotientEdgePreimage (touchedOuterForest z δ) (D.starOf G z.1.1) (touchedLocalComponent z δ))
    = _
  rw [Multiset.count_add]

/-- **R-6c-body-435 — the touched outer forest count bound.**  `touchedOuterForest` is a sub-forest of the outer
`z.1.1`, so its count of any edge is bounded by the outer's. -/
theorem touchedOuterForest_count_internalEdges_le (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
    (e : ResolvedFeynmanEdge) :
    Multiset.count e (touchedOuterForest z δ).internalEdges
      ≤ Multiset.count e z.1.1.internalEdges :=
  Multiset.count_le_of_le e (touchedOuterForest_internalEdges_le z δ)

end GaugeGeometry.QFT.Combinatorial
