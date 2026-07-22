import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaQuotientComplement

/-!
# R-6c-body-527 (Step 1) — selected-outer exact counts (PROVED)

Five-hundred-and-twenty-seventh genuine-body step (Step 1) — exacting body-500's one-directional
`selectedOuter_count_le_occurrence` into exact `Multiset.count` equalities, the foundation for the reverse inclusion
`R.map f ≤ Q.internalEdges` (Steps 3/4) and the exact residual equality `Q.internalEdges = R.map f`, from which
`internalEdges_domain` follows by pure subtraction algebra (Steps 5/6).

Three exact-count banks, all over a split choice `s` (count-safe, `EdgeIdsUnique` NOT used as `Nodup`):

* `selectedOuter_count_eq_forestOccurrence` — for `e ∈ o.γ.internalEdges`, `count e S = count e o.B` (the `≤` is
  body-460; the reverse splits on `count e o.B = 0`, else recovers the owner block `b`, promotes it into `S`
  (`promote_mem_selectedOuterRawOf_raw`), and closes by the two owner-counts + `promote_internalEdges`);
* `selectedOuter_count_eq_left` — for a left-primitive component `γ` and `e ∈ γ.internalEdges`, `count e S = count e A`
  (both owner-counts through `γ`, since `γ ∈ leftOf ⊆ S` and `γ ∈ A`);
* `selectedOuter_count_eq_zero_right` — for a right-primitive component `r` and `e ∈ r.internalEdges`, `count e S = 0`
  (`isRightPrimitive_disjoint_vertices_selectedOuterRaw`).

The component exact transports / reverse inclusion / exact residual equality / complement subtraction / socket inhabitant
(Steps 2–6) follow.

Per the HALT/guards: everything is count-safe; body-485 parent reconstruction / `ValueGeometry` are NOT used; no
`∉ Q.internalEdges` shortcut; no `sourceLeftStar = targetLeftStar` / local permutation / three-route correspondence; strict
`StarProm` / `InnerStarRaw` stay ZERO; NO unconditional-coassoc claim.  No facade, no flat term, no `forgetHopf`, no
rep/perm, and NO `promote_collapse` / singleton / floor-297.
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

/-- **R-6c-body-527 ∎ — the selected-outer/occurrence exact count.**  For `e ∈ o.γ.internalEdges`,
`count e S.internalEdges = count e o.B.internalEdges`. -/
theorem selectedOuter_count_eq_forestOccurrence (s : ResolvedCoassocSplitChoice D G)
    (o : ResolvedCoassocSplitChoice.ForestChoiceOccurrence s) {e : ResolvedFeynmanEdge}
    (heγ : e ∈ o.γ.1.internalEdges) :
    Multiset.count e ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).internalEdges
      = Multiset.count e o.B.1.internalEdges := by
  refine le_antisymm (selectedOuter_count_le_occurrence s o heγ) ?_
  by_cases hcB : Multiset.count e o.B.1.internalEdges = 0
  · omega
  · obtain ⟨b, hb, heb⟩ := resolvedAdmissible_mem_internalEdges'.mp (Multiset.count_pos.mp (Nat.pos_of_ne_zero hcB))
    have hownerB := ResolvedAdmissibleSubgraph.count_internalEdges_eq_of_mem_component hb heb
    have hownerS := ResolvedAdmissibleSubgraph.count_internalEdges_eq_of_mem_component
      (promote_mem_selectedOuterRawOf_raw s o hb)
      (show e ∈ (o.γ.1.promote b).internalEdges by rw [ResolvedFeynmanSubgraph.promote_internalEdges]; exact heb)
    rw [ResolvedFeynmanSubgraph.promote_internalEdges] at hownerS
    omega

/-- **R-6c-body-527 ∎ — the left-primitive exact count.**  For a left-primitive component `γ` and `e ∈ γ.internalEdges`,
`count e S.internalEdges = count e A.internalEdges` (both owner-counts through `γ`). -/
theorem selectedOuter_count_eq_left (s : ResolvedCoassocSplitChoice D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ s.1.1.elements}) (hγL : s.isLeftPrimitive γ)
    {e : ResolvedFeynmanEdge} (he : e ∈ γ.1.internalEdges) :
    Multiset.count e ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).internalEdges
      = Multiset.count e s.1.1.internalEdges := by
  have hγS : γ.1 ∈ ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).elements := by
    simp only [ResolvedForestPromoteSupply.selectedOuterRawOf, ResolvedAdmissibleSubgraph.union_elements,
      Finset.mem_union]
    refine Or.inl ?_
    show γ.1 ∈ ((resolvedConcreteLeftSelectionSupply D G).leftOf s).elements
    rw [resolved_leftOf_elements_eq]
    exact Finset.mem_filter.mpr ⟨γ.2, (ResolvedCoassocSplitChoice.isLeftPrimitive_iff_leftSelectedConcrete s γ).mp hγL⟩
  rw [ResolvedAdmissibleSubgraph.count_internalEdges_eq_of_mem_component hγS he, ResolvedAdmissibleSubgraph.count_internalEdges_eq_of_mem_component γ.2 he]

/-- **R-6c-body-527 ∎ — the right-primitive zero count.**  For a right-primitive component `r` and `e ∈ r.internalEdges`,
`count e S.internalEdges = 0` (right components are vertex-disjoint from the selected outer). -/
theorem selectedOuter_count_eq_zero_right (s : ResolvedCoassocSplitChoice D G)
    (r : {x : {y : ResolvedFeynmanSubgraph G // y ∈ s.1.1.elements} // x ∈ s.rightComponents})
    {e : ResolvedFeynmanEdge} (he : e ∈ r.1.1.internalEdges) :
    Multiset.count e ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).internalEdges = 0 := by
  rw [Multiset.count_eq_zero]
  intro heS
  have hdisj : Disjoint r.1.1.vertices
      ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).vertices :=
    s.isRightPrimitive_disjoint_vertices_selectedOuterRaw (Finset.mem_filter.mp r.2).2
      ⟨e.source, (r.1.1.edges_supported e he).1⟩
  exact Finset.disjoint_left.mp hdisj (r.1.1.edges_supported e he).1
    (((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).source_mem_vertices_of_mem_internalEdges heS)

end GaugeGeometry.QFT.Combinatorial
