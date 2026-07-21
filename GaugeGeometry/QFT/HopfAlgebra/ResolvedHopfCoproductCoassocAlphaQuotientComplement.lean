import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocPromotedCorrectedInternalSupport
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocComplementEdgesPositive
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocComplementEdgesMono
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCorrectedRemnantProvider
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocFilteredQuotientValue

/-!
# R-6c-body-500 — quotient complement: the input-outer residual bound `Q ≤ R.map f` (PROVED)

Five-hundredth genuine-body step — the count-arithmetic core for body-499's sole residual
`0 < (canonicalCorrectedQuotientRaw ... q.1).complementEdges.card`.  The route: the quotient value `Q` lives over the
contract graph `H = S.contractWithStars (starOf)` (`S := selectedOuterRawOf s`); its internal edges are bounded by the
INPUT-OUTER residual `R := A.internalEdges - S.internalEdges` (`A := s.1.1`) retargeted through `f := S.retargetEdge`, so
the input outer's own complement witness survives into `H`'s complement of `Q` — giving strict count (body-501).

This body proves the full **`Q.internalEdges ≤ R.map f`** — the body-500 core — via the input-outer residual strengthening
(body-460's additive core sharpened from the whole ambient `G` to the input outer `A`) and both per-component residual
bounds:

* `selectedOuter_internalEdges_le_inputOuter` — `S.internalEdges ≤ A.internalEdges` (aggregate of body-263's component
  bound under `internalEdges_le_of_components_le`);
* `occurrence_complementEdges_add_selectedOuter_internalEdges_le_inputOuter` — body-460's additive core with the ambient
  bound sharpened from `o.γ.1.internalEdges ≤ G.internalEdges` to `≤ A.internalEdges` (`internalEdges_le_of_mem`) and the
  `S ≤ G` tail replaced by `S ≤ A`;
* `occurrence_complementEdges_le_inputResidual` — `o.B.1.complementEdges ≤ R` (`le_tsub_iff_right`);
* `rightComponent_internalEdges_add_selectedOuter_le_inputOuter` — the survivor additive core (owner localization +
  whole-`S` vertex disjointness);
* `survivorComponent_internalEdges_le_inputResidual` — the RIGHT-SURVIVOR residual bound `≤ R.map f` (`f = id` on `r`'s
  edges + `map_le_map`);
* `correctedRemnantComponent_internalEdges_le_inputResidual` — the CORRECTED-REMNANT residual bound `≤ R.map f`
  (body-460 mirror with the residual sharpened to `R`);
* `canonicalCorrectedQuotientRaw_internalEdges_le_inputResidual` — the whole-union core, aggregated by
  `internalEdges_le_of_components_le` (survivor / remnant dispatch on `union_elements`).

## Status — the body-500 plan's three named banks, all PROVED

```text
S.internalEdges ≤ A.internalEdges                        PROVED
input-outer additive core / residual                     PROVED
right-survivor residual bound → R.map f                  PROVED   (named bank 1)
corrected-remnant residual bound → R.map f               PROVED   (named bank 2)
Q.internalEdges ≤ R.map f                                 PROVED   (named bank 3 — the core)
strict count / complementEdges_card_pos / quotient_mem   body-501 (pure count transport)
```

Per the body-500 plan's safe-stop, the three named banks (survivor / remnant residual + `Q ≤ R.map f`) are done, so the
remainder is pure `Multiset.count` transport over the existing body-433/436 engines (`retargetEdge_injOn_complementEdges`,
`count_complementEdges_eq_count_contractWithStars`, `complementEdges_card_pos_of_count_lt`) plus the W'-level witness — the
body-501 continuation.  `canonicalCorrectedQuotient_mem` is NOT completed here.

Per the HALT/guards: everything stays count-safe (`EdgeIdsUnique` NOT used as `Nodup`); no `∉ Q.internalEdges` shortcut;
per-component counts are NOT hand-added (`internalEdges_le_of_components_le` / the owner lemma do the aggregation); no raw
`∀ s` generalization beyond the split `s` these lemmas already range over (the filtered `q` specialization is the
consumer's, body-501); `quotient_mem` / `quot_eq` / round-trip are NOT back-computed; `OccRaw` / `ValueGeometry` NOT
entered; strict `StarProm` / `InnerStarRaw` stay ZERO; body-445 and the reduced root (body-498/499) are NOT edited.  No
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

/-- **R-6c-body-500 ∎ — the selected outer is inside the input outer (edges).**  Each selected-outer component has
`internalEdges ≤ A.internalEdges` (body-263), aggregated under the disjoint-forest count lemma. -/
theorem selectedOuter_internalEdges_le_inputOuter (s : ResolvedCoassocSplitChoice D G) :
    ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).internalEdges
      ≤ s.1.1.internalEdges :=
  ResolvedAdmissibleSubgraph.internalEdges_le_of_components_le _
    (fun _ hη => selectedOuterRaw_component_internalEdges_le s hη)

/-- **R-6c-body-500 ∎ — the input-outer additive core.**  `B.complementEdges + S.internalEdges ≤ A.internalEdges` — the
body-460 additive core with the ambient bound sharpened from `G` to the input outer `A` (`o.γ ∈ A.elements`). -/
theorem occurrence_complementEdges_add_selectedOuter_internalEdges_le_inputOuter
    (s : ResolvedCoassocSplitChoice D G) (o : ResolvedCoassocSplitChoice.ForestChoiceOccurrence s) :
    o.B.1.complementEdges
        + ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).internalEdges
      ≤ s.1.1.internalEdges := by
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
    have hγA : Multiset.count e o.γ.1.internalEdges ≤ Multiset.count e s.1.1.internalEdges :=
      Multiset.count_le_of_le e (ResolvedAdmissibleSubgraph.internalEdges_le_of_mem s.1.1 o.γ.2)
    rw [hcomp]; omega
  · rw [Multiset.count_eq_zero.mpr hcB, Nat.zero_add]
    exact Multiset.count_le_of_le e (selectedOuter_internalEdges_le_inputOuter s)

/-- **R-6c-body-500 ∎ — the input-outer residual bound.**  `B.complementEdges ≤ A.internalEdges - S.internalEdges`. -/
theorem occurrence_complementEdges_le_inputResidual
    (s : ResolvedCoassocSplitChoice D G) (o : ResolvedCoassocSplitChoice.ForestChoiceOccurrence s) :
    o.B.1.complementEdges
      ≤ s.1.1.internalEdges
        - ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).internalEdges :=
  (le_tsub_iff_right (selectedOuter_internalEdges_le_inputOuter s)).2
    (occurrence_complementEdges_add_selectedOuter_internalEdges_le_inputOuter s o)

/-! ## The right-survivor residual bound -/

variable (Measure : ResolvedMeasureLeafSupply D)

/-- **R-6c-body-500 ∎ — the right-component input-outer additive core.**  A right-primitive component `r` and the
selected outer `S` have disjoint internal-edge support inside `A`, so `r.internalEdges + S.internalEdges ≤ A.internalEdges`
(owner localization + whole-`S` vertex disjointness). -/
theorem rightComponent_internalEdges_add_selectedOuter_le_inputOuter
    (s : ResolvedCoassocSplitChoice D G)
    (r : {x : {y : ResolvedFeynmanSubgraph G // y ∈ s.1.1.elements} // x ∈ s.rightComponents}) :
    r.1.1.internalEdges
        + ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).internalEdges
      ≤ s.1.1.internalEdges := by
  rw [Multiset.le_iff_count]
  intro e
  rw [Multiset.count_add]
  by_cases hcr : e ∈ r.1.1.internalEdges
  · have hown : Multiset.count e s.1.1.internalEdges = Multiset.count e r.1.1.internalEdges :=
      ResolvedAdmissibleSubgraph.count_internalEdges_eq_of_mem_component r.1.2 hcr
    have hne_r : r.1.1.vertices.Nonempty := ⟨e.source, (r.1.1.edges_supported e hcr).1⟩
    have hdisj : Disjoint r.1.1.vertices
        ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).vertices :=
      s.isRightPrimitive_disjoint_vertices_selectedOuterRaw (Finset.mem_filter.mp r.2).2 hne_r
    have hS0 : Multiset.count e
        ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).internalEdges = 0 := by
      rw [Multiset.count_eq_zero]
      intro heS
      exact Finset.disjoint_left.mp hdisj (r.1.1.edges_supported e hcr).1
        (((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).source_mem_vertices_of_mem_internalEdges
          heS)
    rw [hown, hS0]; omega
  · rw [Multiset.count_eq_zero.mpr hcr, Nat.zero_add]
    exact Multiset.count_le_of_le e (selectedOuter_internalEdges_le_inputOuter s)

/-- **R-6c-body-500 ∎ — the right-survivor residual bound.**  `(survivorComponent s r).internalEdges ≤ R.map f` — the
survivor is `r` re-embedded through `S` (`internalEdges = r.internalEdges`, `rfl`), the retarget is the identity on `r`'s
edges (disjoint from `S`), and `r.internalEdges ≤ R` (the additive core), so `map_le_map` finishes. -/
theorem survivorComponent_internalEdges_le_inputResidual
    (s : ResolvedCoassocSplitChoice D G)
    (r : {x : {y : ResolvedFeynmanSubgraph G // y ∈ s.1.1.elements} // x ∈ s.rightComponents}) :
    ((survivorSupply_of_measure Measure G).survivorComponent s r).internalEdges
      ≤ (s.1.1.internalEdges
            - ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).internalEdges).map
          (((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).retargetEdge
            (D.starOf G ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s))) := by
  have hle_R : r.1.1.internalEdges
      ≤ s.1.1.internalEdges
          - ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).internalEdges :=
    (le_tsub_iff_right (selectedOuter_internalEdges_le_inputOuter s)).2
      (rightComponent_internalEdges_add_selectedOuter_le_inputOuter s r)
  have hdisj : Disjoint r.1.1.vertices
      ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).vertices :=
    s.isRightPrimitive_disjoint_vertices_selectedOuterRaw (Finset.mem_filter.mp r.2).2
      (rightComponentNonempty_of_measure Measure s r)
  have hmapid : r.1.1.internalEdges.map
      (((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).retargetEdge
        (D.starOf G ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s)))
      = r.1.1.internalEdges := by
    conv_rhs => rw [← Multiset.map_id r.1.1.internalEdges]
    apply Multiset.map_congr rfl
    intro e he
    obtain ⟨hs, ht⟩ := r.1.1.edges_supported e he
    unfold ResolvedAdmissibleSubgraph.retargetEdge ResolvedFeynmanEdge.retarget
    rw [ResolvedAdmissibleSubgraph.retargetVertex_of_not_mem _ _ (Finset.disjoint_left.mp hdisj hs),
      ResolvedAdmissibleSubgraph.retargetVertex_of_not_mem _ _ (Finset.disjoint_left.mp hdisj ht)]
    rfl
  show r.1.1.internalEdges ≤ _
  rw [← hmapid]
  exact Multiset.map_le_map hle_R

/-! ## The corrected-remnant residual bound -/

/-- **R-6c-body-500 ∎ — the corrected-remnant residual bound.**  `(correctedRemnantComponent o).internalEdges ≤ R.map f`
— the corrected remnant re-embeds `o.B`'s promoted-star contraction (`internalEdges = B.complementEdges.map (B.retarget
(promotedStar))`), each such edge's retarget agrees with the selected-outer retarget (body-459), and `B.complementEdges ≤
R` (the input-outer residual), so `map_le_map` finishes.  Body-460's `promotedCorrectedSource_internalEdges_le` with the
ambient sharpened from `S.complementEdges` to the input-outer residual `R`. -/
theorem correctedRemnantComponent_internalEdges_le_inputResidual
    (Fstar : ResolvedCanonicalStarFacts D) (s : ResolvedCoassocSplitChoice D G)
    (o : ResolvedCoassocSplitChoice.ForestChoiceOccurrence s) :
    ((canonicalCorrectedRemnantReembedSupply s Fstar).correctedRemnantComponent o).internalEdges
      ≤ (s.1.1.internalEdges
            - ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).internalEdges).map
          (((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).retargetEdge
            (D.starOf G ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s))) := by
  have hEq : ((canonicalCorrectedRemnantReembedSupply s Fstar).correctedRemnantComponent o).internalEdges
      = (promotedCorrectedOccurrenceSourceGraph Fstar s o).internalEdges := rfl
  rw [hEq, ← promotedCorrectedSource_eq Fstar s o,
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
    _ ≤ (s.1.1.internalEdges
            - ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).internalEdges).map
          (((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).retargetEdge
            (D.starOf G ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s))) :=
        Multiset.map_le_map (occurrence_complementEdges_le_inputResidual s o)

/-! ## The whole-union residual bound (the body-500 core) -/

/-- **R-6c-body-500 ∎ — the quotient value's internal edges are inside the input-outer residual.**  `Q.internalEdges ≤
R.map f` — the union's components (survivor / corrected remnant) each land in `R.map f` (the two residual bounds above),
aggregated by the disjoint-forest count lemma.  This is the body-500 core: the input outer's complement witness, retargeted
through `S`, is NOT absorbed by `Q`, so it survives into `H`'s complement of `Q` (the strict count — body-501). -/
theorem canonicalCorrectedQuotientRaw_internalEdges_le_inputResidual
    (Measure : ResolvedMeasureLeafSupply D) (CarrierProper : ResolvedCarrierProperProvider D)
    (Fstar : ResolvedCanonicalStarFacts D) (s : ResolvedCoassocSplitChoice D G) :
    (canonicalCorrectedQuotientRaw Measure CarrierProper Fstar s).internalEdges
      ≤ (s.1.1.internalEdges
            - ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).internalEdges).map
          (((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).retargetEdge
            (D.starOf G ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s))) := by
  refine ResolvedAdmissibleSubgraph.internalEdges_le_of_components_le _ (fun γ hγ => ?_)
  simp only [canonicalCorrectedQuotientRaw, ResolvedAdmissibleSubgraph.union_elements,
    Finset.mem_union] at hγ
  rcases hγ with hS | hR
  · rw [ResolvedRightSurvivorSupply.rightSurvivorForest_elements] at hS
    obtain ⟨r, -, rfl⟩ := Finset.mem_image.mp hS
    exact survivorComponent_internalEdges_le_inputResidual Measure s r
  · rw [ResolvedRemnantComponentSupply.remnantForest_elements] at hR
    obtain ⟨γ', -, rfl⟩ := Finset.mem_image.mp hR
    exact correctedRemnantComponent_internalEdges_le_inputResidual Fstar s
      (ResolvedCoassocSplitChoice.forestComponentOccurrence s γ')

end GaugeGeometry.QFT.Combinatorial
