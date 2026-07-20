import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocPromotedCorrectedVerticesSupport

/-!
# R-6c-body-459 — the local/global retarget agreement + external legs support (PROVED)

Four-hundred-and-fifty-ninth genuine-body step — the retarget agreement between the LOCAL retarget (through the
occurrence forest `B` over `γ.tRFG`) and the GLOBAL retarget (through the selected-outer forest `S` over `G`), and the
external-legs support that follows.  The load-bearing survivor disjointness is body-458; the star case uses
`retargetVertex_eq_star_of_mem_element` (which already bakes in componentAt uniqueness).

Fix `S := selectedOuterRawOf s`, `γ := o.γ.1`, `B := o.B.1`.

* `promoted_retargetVertex_eq_selectedOuter` — for `v ∈ γ.vertices`, `B.retargetVertex promotedStar v =
  S.retargetVertex globalStar v`.  `v ∈ B.vertices`: both are `globalStar (γ.promote (B.componentAt v))` (the local star
  IS the global star of the promoted component, by definition + body-385 membership); `v ∉ B.vertices`: body-458 gives
  `v ∉ S.vertices`, so both are the identity.
* `promoted_retargetEdge_eq_selectedOuter` / `promoted_retargetExternalLeg_eq_selectedOuter` — the endpoint corollaries.
* `promotedCorrectedSource_externalLegs_le` — `C.externalLegs ≤ (selectedOuterContractGraph s).externalLegs`
  (`γ.externalLegs ≤ G.externalLegs` + `map_le_map` + the leg agreement via `map_congr`); NO subtraction.

The internal-edges support needs the additive Multiset lemma `B.complementEdges ≤ S.complementEdges` — an INDEPENDENT
load-bearing theorem — and is left to the next body.

Per the HALT/guards: NO permutation equality; strict `StarProm` / `InnerStarRaw` NOT used; only the external-legs support
is closed here (internal complement + provider are later bodies); promoted-component membership is the EXPLICIT body-385
consumption; `Concrete` / `VBuild` NOT wired; body-445 stays a valid conditional.  NOT the unconditional theorem.  No
facade, no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}
  (s : ResolvedCoassocSplitChoice D G)
  (o : ResolvedCoassocSplitChoice.ForestChoiceOccurrence s)

/-- **R-6c-body-459 — the local/global retarget-vertex agreement.** -/
theorem promoted_retargetVertex_eq_selectedOuter {v : VertexId} (hv : v ∈ o.γ.1.vertices) :
    o.B.1.retargetVertex (promotedOccurrenceStar s o) v
      = ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).retargetVertex
          (D.starOf G ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s)) v := by
  by_cases hvB : v ∈ o.B.1.vertices
  · rw [retargetVertex_eq_star_of_mem_element o.B.1 (promotedOccurrenceStar s o)
        (o.B.1.componentAt_mem hvB) (o.B.1.componentAt_vertex_mem hvB)]
    have hpm : v ∈ (o.γ.1.promote (o.B.1.componentAt hvB)).vertices := by
      rw [ResolvedFeynmanSubgraph.promote_vertices]; exact o.B.1.componentAt_vertex_mem hvB
    rw [retargetVertex_eq_star_of_mem_element
        ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s)
        (D.starOf G ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s))
        (promote_mem_selectedOuterRawOf_raw s o (o.B.1.componentAt_mem hvB)) hpm]
    rfl
  · rw [ResolvedAdmissibleSubgraph.retargetVertex_of_not_mem o.B.1 _ hvB,
      ResolvedAdmissibleSubgraph.retargetVertex_of_not_mem
        ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s) _
        (occurrence_survivor_notMem_selectedOuter s o hv hvB)]

/-- **R-6c-body-459 — the local/global retarget-edge agreement.** -/
theorem promoted_retargetEdge_eq_selectedOuter {e : ResolvedFeynmanEdge}
    (hs : e.source ∈ o.γ.1.vertices) (ht : e.target ∈ o.γ.1.vertices) :
    o.B.1.retargetEdge (promotedOccurrenceStar s o) e
      = ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).retargetEdge
          (D.starOf G ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s)) e := by
  simp only [ResolvedAdmissibleSubgraph.retargetEdge, ResolvedFeynmanEdge.retarget]
  rw [promoted_retargetVertex_eq_selectedOuter s o hs, promoted_retargetVertex_eq_selectedOuter s o ht]

/-- **R-6c-body-459 — the local/global retarget-leg agreement.** -/
theorem promoted_retargetExternalLeg_eq_selectedOuter {ℓ : ResolvedExternalLeg}
    (ha : ℓ.attachedTo ∈ o.γ.1.vertices) :
    o.B.1.retargetExternalLeg (promotedOccurrenceStar s o) ℓ
      = ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).retargetExternalLeg
          (D.starOf G ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s)) ℓ := by
  simp only [ResolvedAdmissibleSubgraph.retargetExternalLeg, ResolvedExternalLeg.retarget]
  rw [promoted_retargetVertex_eq_selectedOuter s o ha]

variable (Fstar : ResolvedCanonicalStarFacts D)

/-- **R-6c-body-459 ∎ — the forward corrected source's external-legs support.** -/
theorem promotedCorrectedSource_externalLegs_le :
    (promotedCorrectedOccurrenceSourceGraph Fstar s o).externalLegs
      ≤ (ResolvedCoassocSplitChoice.selectedOuterContractGraph s).externalLegs := by
  rw [← promotedCorrectedSource_eq Fstar s o,
    ResolvedAdmissibleSubgraph.contractWithStars_externalLegs,
    ResolvedFeynmanSubgraph.toResolvedFeynmanGraph_externalLegs,
    ResolvedCoassocSplitChoice.selectedOuterContractGraph,
    ResolvedAdmissibleSubgraph.contractWithStars_externalLegs]
  calc o.γ.1.externalLegs.map (o.B.1.retargetExternalLeg (promotedOccurrenceStar s o))
      = o.γ.1.externalLegs.map (((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).retargetExternalLeg
          (D.starOf G ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s))) :=
        Multiset.map_congr rfl (fun ℓ hℓ =>
          promoted_retargetExternalLeg_eq_selectedOuter s o (o.γ.1.legs_supported ℓ hℓ))
    _ ≤ G.externalLegs.map (((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).retargetExternalLeg
          (D.starOf G ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s))) :=
        Multiset.map_le_map o.γ.1.externalLegs_le

end GaugeGeometry.QFT.Combinatorial
