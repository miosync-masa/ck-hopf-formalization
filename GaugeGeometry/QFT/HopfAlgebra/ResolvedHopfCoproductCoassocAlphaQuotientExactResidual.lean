import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaSelectedOuterExactCount
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaQuotientMemComplete

/-!
# R-6c-body-528 — quotient exact residual `Q.internalEdges = R.map f` (Steps 2–4, PROVED)

Five-hundred-and-twenty-eighth genuine-body step — the load-bearing exact residual equality for `internalEdges_domain`.
Body-500 gave `Q.internalEdges ≤ R.map f`; this body proves the reverse and hence the exact equality, from Step 1's exact
counts.  `R := A.internalEdges - S.internalEdges` (`A := q.1.1.1`, `S := selectedOuterRawOf q.1`), `f := S.retargetEdge
(starOf G S)`, `Q := canonicalCorrectedQuotientRaw … q.1`.

* **Step 2 — component exact transport**: `survivorComponent_internalEdges_eq_inputMap`
  (`(survivorComponent s r).internalEdges = r.internalEdges.map f`, `f = id` on `r`'s edges),
  `correctedRemnantComponent_internalEdges_eq_inputMap`
  (`(correctedRemnantComponent o).internalEdges = o.B.complementEdges.map f`, body-459 retarget agreement);
* **Step 3 — reverse inclusion**: `canonicalCorrectedQuotientRaw_inputResidual_le_internalEdges`
  (`R.map f ≤ Q.internalEdges`, by `count` — recover `e ∈ R`, its `A`-owner `γ`, dispatch left/right/forest through Step 1's
  exact counts and the `count_map_eq_count_of_injOn_mem` engine, land in `Q.elements`);
* **Step 4 — exact equality**: `canonicalCorrectedQuotientRaw_internalEdges_eq_inputResidual` (`le_antisymm`).

Per the HALT/guards: count-safe (`EdgeIdsUnique` NOT used as `Nodup`); no `∉ Q.internalEdges` shortcut; complement
subtraction / `internalEdges_domain` / socket inhabitant / class equality / `quot_eq` / `ValueGeometry` are NOT entered
(next body); no `sourceLeftStar = targetLeftStar` / local permutation / three-route correspondence; strict `StarProm` /
`InnerStarRaw` stay ZERO; NO unconditional-coassoc claim.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO
`promote_collapse` / singleton / floor-297.
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
set_option maxHeartbeats 3200000

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-! ## Step 2 — component exact transport -/

/-- **R-6c-body-528 ∎ — the right-survivor exact map.**  `(survivorComponent s r).internalEdges = r.internalEdges.map f`
(the retarget is the identity on `r`'s edges — disjoint from `S`). -/
theorem survivorComponent_internalEdges_eq_inputMap
    (Measure : ResolvedMeasureLeafSupply D) (s : ResolvedCoassocSplitChoice D G)
    (r : {x : {y : ResolvedFeynmanSubgraph G // y ∈ s.1.1.elements} // x ∈ s.rightComponents}) :
    ((survivorSupply_of_measure Measure G).survivorComponent s r).internalEdges
      = r.1.1.internalEdges.map
          (((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).retargetEdge
            (D.starOf G ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s))) := by
  show r.1.1.internalEdges = _
  conv_lhs => rw [← Multiset.map_id r.1.1.internalEdges]
  refine Multiset.map_congr rfl (fun e he => ?_)
  obtain ⟨hs, ht⟩ := r.1.1.edges_supported e he
  have hdisj : Disjoint r.1.1.vertices
      ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).vertices :=
    s.isRightPrimitive_disjoint_vertices_selectedOuterRaw (Finset.mem_filter.mp r.2).2 ⟨e.source, hs⟩
  show e = _
  unfold ResolvedAdmissibleSubgraph.retargetEdge ResolvedFeynmanEdge.retarget
  rw [ResolvedAdmissibleSubgraph.retargetVertex_of_not_mem _ _ (Finset.disjoint_left.mp hdisj hs),
    ResolvedAdmissibleSubgraph.retargetVertex_of_not_mem _ _ (Finset.disjoint_left.mp hdisj ht)]

/-- **R-6c-body-528 ∎ — the corrected-remnant exact map.**  `(correctedRemnantComponent o).internalEdges =
o.B.complementEdges.map f` (body-459 local/global retarget agreement). -/
theorem correctedRemnantComponent_internalEdges_eq_inputMap
    (Fstar : ResolvedCanonicalStarFacts D) (s : ResolvedCoassocSplitChoice D G)
    (o : ResolvedCoassocSplitChoice.ForestChoiceOccurrence s) :
    ((canonicalCorrectedRemnantReembedSupply s Fstar).correctedRemnantComponent o).internalEdges
      = o.B.1.complementEdges.map
          (((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).retargetEdge
            (D.starOf G ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s))) := by
  have hEq : ((canonicalCorrectedRemnantReembedSupply s Fstar).correctedRemnantComponent o).internalEdges
      = (promotedCorrectedOccurrenceSourceGraph Fstar s o).internalEdges := rfl
  rw [hEq, ← promotedCorrectedSource_eq Fstar s o,
    ResolvedAdmissibleSubgraph.contractWithStars_internalEdges]
  refine Multiset.map_congr rfl (fun e he => ?_)
  have heγ : e ∈ o.γ.1.internalEdges := by
    have h := ResolvedAdmissibleSubgraph.mem_internalEdges_of_mem_complementEdges he
    rwa [ResolvedFeynmanSubgraph.toResolvedFeynmanGraph_internalEdges] at h
  exact promoted_retargetEdge_eq_selectedOuter s o
    (o.γ.1.edges_supported e heγ).1 (o.γ.1.edges_supported e heγ).2

/-! ## Step 3 — reverse inclusion (over a filtered `q`) -/

/-- **R-6c-body-528 ∎ — the reverse inclusion.**  `R.map f ≤ Q.internalEdges` — each residual edge `f e` (`e ∈ R`) is
recovered on the corresponding `Q` component (survivor / corrected remnant) with equal count, via Step 1's exact counts and
the `count_map_eq_count_of_injOn_mem` engine. -/
theorem canonicalCorrectedQuotientRaw_inputResidual_le_internalEdges
    (Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalUniqueSupportedCarrierProperSupply.toData G) :
    (q.1.1.1.internalEdges
        - ((resolvedConcreteForestPromoteSupply canonicalUniqueSupportedCarrierProperSupply.toData G).selectedOuterRawOf
            q.1).internalEdges).map
        (((resolvedConcreteForestPromoteSupply canonicalUniqueSupportedCarrierProperSupply.toData G).selectedOuterRawOf
            q.1).retargetEdge
          (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G
            ((resolvedConcreteForestPromoteSupply canonicalUniqueSupportedCarrierProperSupply.toData G).selectedOuterRawOf
              q.1)))
      ≤ (canonicalCorrectedQuotientRaw Measure
          canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
          canonicalUniqueStarFactsOfW' q.1).internalEdges := by
  set S := (resolvedConcreteForestPromoteSupply canonicalUniqueSupportedCarrierProperSupply.toData G).selectedOuterRawOf
    q.1 with hSdef
  set f := S.retargetEdge (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G S) with hfdef
  have hId : G.EdgeIdsUnique := edgeIdsUnique_of_carrier_mem q.1.1.2
  rw [Multiset.le_iff_count]
  intro e'
  by_cases hc : Multiset.count e' ((q.1.1.1.internalEdges - S.internalEdges).map f) = 0
  · omega
  · obtain ⟨e, heR, rfl⟩ := Multiset.mem_map.mp (Multiset.count_pos.mp (Nat.pos_of_ne_zero hc))
    have heA : e ∈ q.1.1.1.internalEdges := Multiset.mem_of_le (Multiset.sub_le_self _ _) heR
    have heG : e ∈ G.internalEdges := Multiset.mem_of_le q.1.1.1.internalEdges_le heA
    have hmap : Multiset.count (f e) ((q.1.1.1.internalEdges - S.internalEdges).map f)
        = Multiset.count e (q.1.1.1.internalEdges - S.internalEdges) :=
      count_map_eq_count_of_injOn_mem
        (ResolvedAdmissibleSubgraph.retargetEdge_injOn_internalEdges hId S _)
        (fun a ha => Multiset.mem_of_le q.1.1.1.internalEdges_le
          (Multiset.mem_of_le (Multiset.sub_le_self _ _) ha)) heG
    rw [hmap]
    obtain ⟨γ, hγ, heγ⟩ := resolvedAdmissible_mem_internalEdges'.mp heA
    have hownerA : Multiset.count e q.1.1.1.internalEdges = Multiset.count e γ.internalEdges :=
      ResolvedAdmissibleSubgraph.count_internalEdges_eq_of_mem_component hγ heγ
    rcases ResolvedCoassocSplitChoice.isLeftPrimitive_or_isRightPrimitive_or_isForestChoice q.1 ⟨γ, hγ⟩ with
      hL | hR | hF
    · -- LEFT: count e R = 0
      rw [Multiset.count_sub]
      have hSA : Multiset.count e S.internalEdges = Multiset.count e q.1.1.1.internalEdges :=
        selectedOuter_count_eq_left q.1 ⟨γ, hγ⟩ hL heγ
      omega
    · -- RIGHT
      set r : {x : {y : ResolvedFeynmanSubgraph G // y ∈ q.1.1.1.elements} //
          x ∈ ResolvedCoassocSplitChoice.rightComponents q.1} :=
        ⟨⟨γ, hγ⟩, Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, hR⟩⟩ with hr
      have hS0 : Multiset.count e S.internalEdges = 0 := selectedOuter_count_eq_zero_right q.1 r heγ
      have hsurvEq : ((survivorSupply_of_measure Measure G).survivorComponent q.1 r).internalEdges
          = γ.internalEdges.map f := survivorComponent_internalEdges_eq_inputMap Measure q.1 r
      have hsurvMem : (survivorSupply_of_measure Measure G).survivorComponent q.1 r
          ∈ (canonicalCorrectedQuotientRaw Measure
            canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
            canonicalUniqueStarFactsOfW' q.1).elements := by
        simp only [canonicalCorrectedQuotientRaw, ResolvedAdmissibleSubgraph.union_elements, Finset.mem_union]
        refine Or.inl ?_
        rw [ResolvedRightSurvivorSupply.rightSurvivorForest_elements]
        exact Finset.mem_image.mpr ⟨r, Finset.mem_attach _ _, rfl⟩
      have hfeMem : f e ∈ ((survivorSupply_of_measure Measure G).survivorComponent q.1 r).internalEdges := by
        rw [hsurvEq]; exact Multiset.mem_map.mpr ⟨e, heγ, rfl⟩
      have hownerQ : Multiset.count (f e) (canonicalCorrectedQuotientRaw Measure
            canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
            canonicalUniqueStarFactsOfW' q.1).internalEdges
          = Multiset.count (f e) ((survivorSupply_of_measure Measure G).survivorComponent q.1 r).internalEdges :=
        ResolvedAdmissibleSubgraph.count_internalEdges_eq_of_mem_component hsurvMem hfeMem
      have hmapcount : Multiset.count (f e) (γ.internalEdges.map f) = Multiset.count e γ.internalEdges :=
        count_map_eq_count_of_injOn_mem
          (ResolvedAdmissibleSubgraph.retargetEdge_injOn_internalEdges hId S _)
          (fun a ha => Multiset.mem_of_le q.1.1.1.internalEdges_le
            (Multiset.mem_of_le (ResolvedAdmissibleSubgraph.internalEdges_le_of_mem q.1.1.1 hγ) ha)) heG
      rw [Multiset.count_sub, hownerQ, hsurvEq, hmapcount]
      omega
    · -- FOREST
      have hfmem : (⟨γ, hγ⟩ : {x : ResolvedFeynmanSubgraph G // x ∈ q.1.1.1.elements})
          ∈ ResolvedCoassocSplitChoice.forestComponents q.1 :=
        Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, hF⟩
      set o := ResolvedCoassocSplitChoice.forestComponentOccurrence q.1 ⟨⟨γ, hγ⟩, hfmem⟩ with ho
      have heγo : e ∈ o.γ.1.internalEdges := heγ
      have hSocc : Multiset.count e S.internalEdges = Multiset.count e o.B.1.internalEdges :=
        selectedOuter_count_eq_forestOccurrence q.1 o heγo
      have hownerA' : Multiset.count e q.1.1.1.internalEdges = Multiset.count e o.γ.1.internalEdges :=
        ResolvedAdmissibleSubgraph.count_internalEdges_eq_of_mem_component o.γ.2 heγo
      have hcompl : Multiset.count e o.B.1.complementEdges
          = Multiset.count e o.γ.1.internalEdges - Multiset.count e o.B.1.internalEdges := by
        show Multiset.count e (o.γ.1.toResolvedFeynmanGraph.internalEdges - o.B.1.internalEdges) = _
        rw [Multiset.count_sub, ResolvedFeynmanSubgraph.toResolvedFeynmanGraph_internalEdges]
      have heBc : e ∈ o.B.1.complementEdges := by
        rw [← Multiset.count_pos, hcompl]
        have heRpos : 0 < Multiset.count e (q.1.1.1.internalEdges - S.internalEdges) :=
          hmap ▸ Nat.pos_of_ne_zero hc
        rw [Multiset.count_sub] at heRpos
        omega
      have hremEq : ((canonicalCorrectedRemnantReembedSupply q.1 canonicalUniqueStarFactsOfW').correctedRemnantComponent
            o).internalEdges = o.B.1.complementEdges.map f :=
        correctedRemnantComponent_internalEdges_eq_inputMap canonicalUniqueStarFactsOfW' q.1 o
      have hremMem : (canonicalCorrectedRemnantReembedSupply q.1 canonicalUniqueStarFactsOfW').correctedRemnantComponent o
          ∈ (canonicalCorrectedQuotientRaw Measure
            canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
            canonicalUniqueStarFactsOfW' q.1).elements := by
        simp only [canonicalCorrectedQuotientRaw, ResolvedAdmissibleSubgraph.union_elements, Finset.mem_union]
        refine Or.inr ?_
        rw [ResolvedRemnantComponentSupply.remnantForest_elements]
        exact Finset.mem_image.mpr ⟨⟨⟨γ, hγ⟩, hfmem⟩, Finset.mem_attach _ _, rfl⟩
      have hfeMem : f e ∈ ((canonicalCorrectedRemnantReembedSupply q.1
          canonicalUniqueStarFactsOfW').correctedRemnantComponent o).internalEdges := by
        rw [hremEq]; exact Multiset.mem_map.mpr ⟨e, heBc, rfl⟩
      have hownerQ : Multiset.count (f e) (canonicalCorrectedQuotientRaw Measure
            canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
            canonicalUniqueStarFactsOfW' q.1).internalEdges
          = Multiset.count (f e) ((canonicalCorrectedRemnantReembedSupply q.1
              canonicalUniqueStarFactsOfW').correctedRemnantComponent o).internalEdges :=
        ResolvedAdmissibleSubgraph.count_internalEdges_eq_of_mem_component hremMem hfeMem
      have hmapcount : Multiset.count (f e) (o.B.1.complementEdges.map f) = Multiset.count e o.B.1.complementEdges :=
        count_map_eq_count_of_injOn_mem
          (ResolvedAdmissibleSubgraph.retargetEdge_injOn_internalEdges hId S _)
          (fun a ha => Multiset.mem_of_le q.1.1.1.internalEdges_le
            (Multiset.mem_of_le (ResolvedAdmissibleSubgraph.internalEdges_le_of_mem q.1.1.1 o.γ.2)
              (by have h := ResolvedAdmissibleSubgraph.mem_internalEdges_of_mem_complementEdges ha
                  rwa [ResolvedFeynmanSubgraph.toResolvedFeynmanGraph_internalEdges] at h))) heG
      rw [Multiset.count_sub, hownerQ, hremEq, hmapcount, hcompl]
      omega

/-! ## Step 4 — the exact residual equality (the load-bearing theorem) -/

/-- **R-6c-body-528 ∎ — the exact residual equality.**  `Q.internalEdges = R.map f` — body-500's `≤` and Step 3's `≥`. -/
theorem canonicalCorrectedQuotientRaw_internalEdges_eq_inputResidual
    (Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalUniqueSupportedCarrierProperSupply.toData G) :
    (canonicalCorrectedQuotientRaw Measure
        canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
        canonicalUniqueStarFactsOfW' q.1).internalEdges
      = (q.1.1.1.internalEdges
          - ((resolvedConcreteForestPromoteSupply canonicalUniqueSupportedCarrierProperSupply.toData G).selectedOuterRawOf
              q.1).internalEdges).map
          (((resolvedConcreteForestPromoteSupply canonicalUniqueSupportedCarrierProperSupply.toData G).selectedOuterRawOf
              q.1).retargetEdge
            (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G
              ((resolvedConcreteForestPromoteSupply canonicalUniqueSupportedCarrierProperSupply.toData G).selectedOuterRawOf
                q.1))) :=
  le_antisymm
    (canonicalCorrectedQuotientRaw_internalEdges_le_inputResidual Measure
      canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider canonicalUniqueStarFactsOfW' q.1)
    (canonicalCorrectedQuotientRaw_inputResidual_le_internalEdges Measure q)

end GaugeGeometry.QFT.Combinatorial
