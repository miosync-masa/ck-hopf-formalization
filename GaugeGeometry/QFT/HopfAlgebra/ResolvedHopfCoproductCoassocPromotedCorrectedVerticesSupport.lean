import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocPromotedCorrectedSource
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocPromotedVertices
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocLeftPrimitiveFactor
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightSurvivor

/-!
# R-6c-body-458 — the forward corrected source's survivor geometry + vertices support (PROVED)

Four-hundred-and-fifty-eighth genuine-body step — the LOAD-BEARING disjointness of the forward corrected source's
embedding into the global selected-outer contraction, and the vertices support that follows from it.  This is genuine
geometry (a local contraction embedding into a global one), NOT a record assembly.

Fix `S := selectedOuterRawOf q.1`, `γ := o.γ.1`, `B := o.B.1`.  The load-bearing fact:

* `occurrence_survivor_notMem_selectedOuter` — a `γ`-vertex outside `B` is outside `S` entirely.  Proof: `v ∈ S.vertices`
  puts `v` in some `S`-component `σ ∈ leftOf ∪ promotedOf`; the `leftOf` case forces `σ = γ` (pairwise disjointness),
  contradicting `o.hchoice` via `not_leftSelectedConcrete_of_inr`, or `σ ≠ γ` gives disjointness; the `promotedOf` case
  recovers a source `γ'` — if `γ' ≠ γ` disjointness, if `γ' = γ` then `σ` is a promote of `B` (via `o.hchoice`), so
  `v ∈ σ.vertices = b.vertices ⊆ B.vertices`, contradicting `v ∉ B.vertices`.

* `promotedCorrectedSource_vertices_subset` — `C.vertices ⊆ q.1.selectedOuterContractGraph.vertices` (rewriting `C` to
  `B.contractWithStars promotedOccurrenceStar` via body-456): local survivors land in the global difference (survivor
  lemma + `γ ⊆ G`), local stars land in the global star vertices (body-385 `promote_mem_selectedOuterRawOf`).

Per the HALT/guards: NO permutation equality; strict `StarProm` / `InnerStarRaw` NOT used; only the VERTICES support is
built here (the retarget agreement for edges/legs + the provider are later bodies); promoted-component membership is the
EXPLICIT body-385 consumption; `Concrete` / `VBuild` NOT wired; body-445 stays a valid conditional.  NOT the unconditional
theorem.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
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
  (q : FilteredForestBlockDom D G)
  (o : ResolvedCoassocSplitChoice.ForestChoiceOccurrence q.1)

/-- **R-6c-body-458 — the load-bearing survivor disjointness.**  A `γ`-vertex outside the occurrence forest `B` lies
outside the whole selected-outer forest `S`. -/
theorem occurrence_survivor_notMem_selectedOuter {v : VertexId}
    (hvγ : v ∈ o.γ.1.vertices) (hvB : v ∉ o.B.1.vertices) :
    v ∉ ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf q.1).vertices := by
  intro hvS
  rw [ResolvedAdmissibleSubgraph.mem_vertices] at hvS
  obtain ⟨σ, hσ, hvσ⟩ := hvS
  simp only [ResolvedForestPromoteSupply.selectedOuterRawOf,
    ResolvedAdmissibleSubgraph.union_elements, Finset.mem_union] at hσ
  rcases hσ with hσL | hσP
  · have hσL' : σ ∈ ((resolvedConcreteLeftSelectionSupply D G).leftOf q.1).elements := hσL
    rw [resolved_leftOf_elements_eq, Finset.mem_filter] at hσL'
    by_cases hσγ : σ = o.γ.1
    · exact (ResolvedCoassocSplitChoice.not_leftSelectedConcrete_of_inr q.1 o.γ.2 o.hchoice)
        (hσγ ▸ hσL'.2)
    · exact Finset.disjoint_left.mp (q.1.1.1.pairwiseDisjoint hσL'.1 o.γ.2 hσγ) hvσ hvγ
  · have hσP' : σ ∈ ((resolvedPromotedOfSupply D G).promotedOf q.1).elements := hσP
    rw [ResolvedPromotedOfSupply.promotedOf_elements] at hσP'
    obtain ⟨γ', hσ'⟩ := ResolvedCoassocSplitChoice.mem_promotedElements hσP'
    by_cases hγγ : γ'.1 = o.γ.1
    · rw [Subtype.ext hγγ, ResolvedCoassocSplitChoice.promotedComponentElements_inr q.1 o.hchoice] at hσ'
      simp only [ResolvedAdmissibleSubgraph.promote_elements, Finset.mem_image] at hσ'
      obtain ⟨b, hb, rfl⟩ := hσ'
      rw [ResolvedFeynmanSubgraph.promote_vertices] at hvσ
      exact hvB (ResolvedAdmissibleSubgraph.mem_vertices.mpr ⟨b, hb, hvσ⟩)
    · exact Finset.disjoint_left.mp (q.1.1.1.pairwiseDisjoint γ'.2 o.γ.2 hγγ)
        (ResolvedCoassocSplitChoice.promotedComponentElements_vertices_subset_parent q.1 hσ' hvσ) hvγ

variable (Fstar : ResolvedCanonicalStarFacts D)

/-- **R-6c-body-458 ∎ — the forward corrected source's vertices support.**  The corrected source graph's vertices sit in
the global selected-outer contraction. -/
theorem promotedCorrectedSource_vertices_subset :
    (promotedCorrectedOccurrenceSourceGraph Fstar q o).vertices
      ⊆ (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1).vertices := by
  rw [← promotedCorrectedSource_eq Fstar q o]
  intro v hv
  rw [ResolvedAdmissibleSubgraph.contractWithStars_vertices,
    ResolvedFeynmanSubgraph.toResolvedFeynmanGraph_vertices, Finset.mem_union] at hv
  rw [ResolvedCoassocSplitChoice.selectedOuterContractGraph,
    ResolvedAdmissibleSubgraph.contractWithStars_vertices, Finset.mem_union]
  rcases hv with hvL | hvR
  · left
    rw [Finset.mem_sdiff] at hvL ⊢
    exact ⟨o.γ.1.vertices_subset hvL.1,
      occurrence_survivor_notMem_selectedOuter q o hvL.1 hvL.2⟩
  · right
    rw [ResolvedAdmissibleSubgraph.mem_starVertices] at hvR ⊢
    obtain ⟨b, hb, hbv⟩ := hvR
    exact ⟨o.γ.1.promote b, promote_mem_selectedOuterRawOf q o hb, hbv⟩

end GaugeGeometry.QFT.Combinatorial
