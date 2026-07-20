import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocPromotedRetargetAgreement
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocComponentOwnerCount
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocComplementCountBackbone
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocComplementEdgesMono

/-!
# R-6c-body-460 — the internal complement inclusion + internal edges support (PROVED)

Four-hundred-and-sixtieth genuine-body step — the last load-bearing Multiset geometry of the cross-ambient migration: the
occurrence forest's complement edges inject into the selected-outer forest's complement edges, and the internal-edges
support that follows.  Done count-safely (body-432 owner lemma, per-edge count proof) — NO `∉`, NO global `biUnion` sum,
NO source-map injectivity.

Fix `S := selectedOuterRawOf s`, `γ := o.γ.1`, `B := o.B.1`.

* `selectedOuter_count_le_occurrence` — for `e ∈ γ.internalEdges`, `count e S.internalEdges ≤ count e B.internalEdges`.
  The `S`-owner `σ` of `e` (body-432) is never a `leftOf` component (`σ = γ` clashes with `o.hchoice`; `σ ≠ γ` clashes
  with pairwise disjointness on `e ∈ σ.I ∩ γ.I`), so `σ ∈ promotedOf`, whose source is `γ` (disjointness), pinned by
  `o.hchoice` to a promote of `B`; then `count e S.I = count e σ.I = count e b.I ≤ count e B.I`.
* `occurrence_complementEdges_add_selectedOuter_internalEdges_le` — the additive core `B.complementEdges + S.internalEdges
  ≤ G.internalEdges`, per-edge via `Multiset.count_sub` + `omega`.
* `occurrence_complementEdges_le_selectedOuter_complementEdges` — `B.complementEdges ≤ S.complementEdges`
  (`le_tsub_iff_right`).
* `promotedCorrectedSource_internalEdges_le` — the internal-edges support (`map_congr` via body-459 retarget agreement +
  `map_le_map` via the complement inclusion).

Per the HALT/guards: NO permutation equality; strict `StarProm` / `InnerStarRaw` NOT used; the provider assembly + the
corrected `hround` are the next body; promoted-component membership is the EXPLICIT body-385/458 consumption;
`Concrete` / `VBuild` NOT wired; body-445 stays a valid conditional.  NOT the unconditional theorem.  No facade, no flat
term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
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

/-- **R-6c-body-460 — the count-safe owner bound.**  A `γ`-internal edge occurs no more often in the selected-outer
forest than in the occurrence forest. -/
theorem selectedOuter_count_le_occurrence {e : ResolvedFeynmanEdge}
    (heγ : e ∈ o.γ.1.internalEdges) :
    Multiset.count e ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).internalEdges
      ≤ Multiset.count e o.B.1.internalEdges := by
  by_cases hcS : Multiset.count e
      ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).internalEdges = 0
  · rw [hcS]; exact Nat.zero_le _
  · have heS : e ∈ ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).internalEdges :=
      Multiset.count_pos.mp (Nat.pos_of_ne_zero hcS)
    obtain ⟨σ, hσ, heσ⟩ := resolvedAdmissible_mem_internalEdges'.mp heS
    have howner : Multiset.count e
        ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).internalEdges
        = Multiset.count e σ.internalEdges :=
      ResolvedAdmissibleSubgraph.count_internalEdges_eq_of_mem_component hσ heσ
    simp only [ResolvedForestPromoteSupply.selectedOuterRawOf,
      ResolvedAdmissibleSubgraph.union_elements, Finset.mem_union] at hσ
    rcases hσ with hσL | hσP
    · exfalso
      have hσL' : σ ∈ ((resolvedConcreteLeftSelectionSupply D G).leftOf s).elements := hσL
      rw [resolved_leftOf_elements_eq, Finset.mem_filter] at hσL'
      by_cases hσγ : σ = o.γ.1
      · exact (ResolvedCoassocSplitChoice.not_leftSelectedConcrete_of_inr s o.γ.2 o.hchoice)
          (hσγ ▸ hσL'.2)
      · exact Finset.disjoint_left.mp (s.1.1.pairwiseDisjoint hσL'.1 o.γ.2 hσγ)
          (σ.edges_supported e heσ).1 (o.γ.1.edges_supported e heγ).1
    · have hσP' : σ ∈ ((resolvedPromotedOfSupply D G).promotedOf s).elements := hσP
      rw [ResolvedPromotedOfSupply.promotedOf_elements] at hσP'
      obtain ⟨γ', hσ'⟩ := ResolvedCoassocSplitChoice.mem_promotedElements hσP'
      have hσγ' : γ'.1 = o.γ.1 := by
        by_contra hne
        exact Finset.disjoint_left.mp (s.1.1.pairwiseDisjoint γ'.2 o.γ.2 hne)
          (ResolvedCoassocSplitChoice.promotedComponentElements_vertices_subset_parent s hσ'
            (σ.edges_supported e heσ).1)
          (o.γ.1.edges_supported e heγ).1
      rw [Subtype.ext hσγ', ResolvedCoassocSplitChoice.promotedComponentElements_inr s o.hchoice] at hσ'
      simp only [ResolvedAdmissibleSubgraph.promote_elements, Finset.mem_image] at hσ'
      obtain ⟨b, hb, rfl⟩ := hσ'
      rw [howner, ResolvedFeynmanSubgraph.promote_internalEdges]
      exact Multiset.count_le_of_le e (ResolvedAdmissibleSubgraph.internalEdges_le_of_mem o.B.1 hb)

/-- **R-6c-body-460 — the additive core.**  `B.complementEdges + S.internalEdges ≤ G.internalEdges`. -/
theorem occurrence_complementEdges_add_selectedOuter_internalEdges_le :
    o.B.1.complementEdges
        + ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).internalEdges
      ≤ G.internalEdges := by
  rw [Multiset.le_iff_count]
  intro e
  rw [Multiset.count_add]
  by_cases hcB : e ∈ o.B.1.complementEdges
  · have heγ : e ∈ o.γ.1.internalEdges := by
      have h := ResolvedAdmissibleSubgraph.mem_internalEdges_of_mem_complementEdges hcB
      rwa [ResolvedFeynmanSubgraph.toResolvedFeynmanGraph_internalEdges] at h
    have hSB := selectedOuter_count_le_occurrence s o heγ
    have hcomp : Multiset.count e o.B.1.complementEdges
        = Multiset.count e o.γ.1.internalEdges - Multiset.count e o.B.1.internalEdges := by
      show Multiset.count e (o.γ.1.toResolvedFeynmanGraph.internalEdges - o.B.1.internalEdges) = _
      rw [Multiset.count_sub, ResolvedFeynmanSubgraph.toResolvedFeynmanGraph_internalEdges]
    have hBγ : Multiset.count e o.B.1.internalEdges ≤ Multiset.count e o.γ.1.internalEdges := by
      have h := Multiset.count_le_of_le e o.B.1.internalEdges_le
      rwa [ResolvedFeynmanSubgraph.toResolvedFeynmanGraph_internalEdges] at h
    have hγG : Multiset.count e o.γ.1.internalEdges ≤ Multiset.count e G.internalEdges :=
      Multiset.count_le_of_le e o.γ.1.internalEdges_le
    rw [hcomp]; omega
  · rw [Multiset.count_eq_zero.mpr hcB, Nat.zero_add]
    exact Multiset.count_le_of_le e (ResolvedAdmissibleSubgraph.internalEdges_le _)

/-- **R-6c-body-460 — the complement inclusion.**  `B.complementEdges ≤ S.complementEdges`. -/
theorem occurrence_complementEdges_le_selectedOuter_complementEdges :
    o.B.1.complementEdges
      ≤ ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).complementEdges := by
  show o.B.1.complementEdges
    ≤ G.internalEdges - ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).internalEdges
  exact (le_tsub_iff_right (ResolvedAdmissibleSubgraph.internalEdges_le _)).2
    (occurrence_complementEdges_add_selectedOuter_internalEdges_le s o)

variable (Fstar : ResolvedCanonicalStarFacts D)

/-- **R-6c-body-460 ∎ — the forward corrected source's internal-edges support.** -/
theorem promotedCorrectedSource_internalEdges_le :
    (promotedCorrectedOccurrenceSourceGraph Fstar s o).internalEdges
      ≤ (ResolvedCoassocSplitChoice.selectedOuterContractGraph s).internalEdges := by
  rw [← promotedCorrectedSource_eq Fstar s o,
    ResolvedAdmissibleSubgraph.contractWithStars_internalEdges,
    ResolvedCoassocSplitChoice.selectedOuterContractGraph,
    ResolvedAdmissibleSubgraph.contractWithStars_internalEdges]
  calc o.B.1.complementEdges.map (o.B.1.retargetEdge (promotedOccurrenceStar s o))
      = o.B.1.complementEdges.map
          (((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).retargetEdge
            (D.starOf G ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s))) :=
        Multiset.map_congr rfl (fun e he => by
          have heγ : e ∈ o.γ.1.internalEdges := by
            have h := ResolvedAdmissibleSubgraph.mem_internalEdges_of_mem_complementEdges he
            rwa [ResolvedFeynmanSubgraph.toResolvedFeynmanGraph_internalEdges] at h
          exact promoted_retargetEdge_eq_selectedOuter s o
            (o.γ.1.edges_supported e heγ).1 (o.γ.1.edges_supported e heγ).2)
    _ ≤ ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).complementEdges.map
          (((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).retargetEdge
            (D.starOf G ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s))) :=
        Multiset.map_le_map (occurrence_complementEdges_le_selectedOuter_complementEdges s o)

end GaugeGeometry.QFT.Combinatorial
