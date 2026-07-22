import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaInnerRawSaturation
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaSaturationAlgebra
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocFilteredQuotientValue
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightSurvivor
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocPromotedRetargetAgreement
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCorrectedFamilyDisjoint
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocPromotedCorrectedSource
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCorrectedRemnantSupplyBuild
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocFreeClusterBank
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCanonicalStarFacts
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocTouchedOccurrenceConcrete
import GaugeGeometry.QFT.HopfAlgebra.ResolvedSigmaSaturation

/-!
# R-6c-body-539 — the `W″` corrected-quotient external-leg-saturation checkpoint (PROVED)

Five-hundred-and-thirty-ninth genuine-body step — the LAST combinatorial fourth-axis (external-leg-saturation) checkpoint:
the two regions of `canonicalCorrectedQuotientRaw` (the corrected / two-stage quotient) are each
`ResolvedExternalLegSaturated`, and their `union` inherits it.  This closes the `W″` audit for the corrected quotient at
the COMPONENT / forest level; the six-condition `W″` membership and the coassoc re-key are a later body (NOT touched here).

## Master architecture — saturation descends because the retarget is COHERENT and TRACEABLE

The quotient graph boundary is `s.selectedOuterContractGraph.externalLegs = G.externalLegs.map (S.retargetExternalLeg g)`
(`S := selectedOuterRawOf s`, `g := D.starOf G S`).  For a quotient component `δ` the saturation obligation is
`(G.externalLegs.map (S.retargetExternalLeg g)).filter (·.attachedTo ∈ δ.vertices) ≤ δ.externalLegs`.  It descends through
one GENERIC boundary-transport engine (Step 1) fed by two component facts:

* **traceability** (`htrace`): a leg whose GLOBALLY-retargeted attachment lands inside `δ.vertices` had its ORIGINAL
  attachment inside the parent component — the retarget image either is the identity (attachment outside `S`) or is a
  FRESH star (`Fstar.starOf_fresh`, `∉ G.vertices ⊇ δ.vertices` — impossible);
* **coherence** (`hcoh`): on legs of the parent component the global retarget agrees with the LOCAL promoted-star retarget
  (right survivor: both are the identity; corrected remnant: body-459 `promoted_retargetExternalLeg_eq_selectedOuter`).

## Classification of the two regions

```text
right survivor      = filter transport + star freshness            (Step 2, right-component/selectedOuter disjointness)
corrected remnant   = coherence (body-459) + star traceability     (Step 4, needs the Step-3 vertex trace)
union               = FREE                                          (Step 5, body-534 `..._union`)
```

The load-bearing lemma is **Step 3** `promotedCorrectedOccurrence_vertex_trace`: the corrected remnant's promoted-star
contraction vertices pull back to the parent input-outer component.  It mirrors body-459 / body-464's owner recovery and
uses ONLY the selected-outer allocator's `starOf_injective` — NO strict promoted-star equality, NO comparison of distinct
local correcting permutations.

## Running scoreboard (`W″` migration)

```text
selectedOuter        PASSED W″  (body-534)
recoveredRawUnion    PASSED W″  (body-537)
innerRaw             PASSED W″  (body-538)
corrected-quotient   PASSED W″  (body-539, this file)  ← both regions closed + union: THE LAST combinatorial checkpoint
```

Per the HALT/guards: the `W″` six-condition corrected-quotient MEMBERSHIP is NOT assembled (next body); body-501's `W′`
membership is NOT reused by coercion; distinct local correcting permutations are NOT compared / composed and no
`corrected = uncorrected` graph equality is asserted; NO leg-ID injectivity (this is trace + coherence, not cancellation);
no target quotient membership / round-trip / coassoc is read; strict `StarProm` / `InnerStarRaw` stay ZERO; NO
unconditional-coassoc claim.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton
/ floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-! ## Step 1 — the generic boundary-transport engine (ALWAYS closeable). -/

/-- **R-6c-body-539 — the generic boundary-transport engine.**  A `P`-filter of the `f`-image of `M` is `≤` the `g`-image
of `N`, PROVIDED (a) `P (f ℓ)` traces back to `Q ℓ` on `M` (`htrace`), (b) `M.filter Q ≤ N` (`hsource`), and (c) `f` and
`g` agree on the `Q`-part of `M` (`hcoh`).  Pure filter/map monotonicity — no injectivity, no count cancellation. -/
theorem mapped_externalLeg_filter_le_of_trace {α β : Type*} [DecidableEq α] [DecidableEq β]
    {M N : Multiset α} {f g : α → β} {P : β → Prop} [DecidablePred P] {Q : α → Prop} [DecidablePred Q]
    (htrace : ∀ ℓ ∈ M, P (f ℓ) → Q ℓ)
    (hsource : M.filter Q ≤ N)
    (hcoh : ∀ ℓ ∈ M, Q ℓ → f ℓ = g ℓ) :
    (M.map f).filter P ≤ N.map g := by
  have hmono : M.filter (fun a => P (f a)) ≤ M.filter Q := by
    rw [Multiset.le_iff_count]
    intro a
    simp only [Multiset.count_filter]
    by_cases hcnt : Multiset.count a M = 0
    · simp [hcnt]
    · have haM : a ∈ M := Multiset.count_pos.mp (Nat.pos_of_ne_zero hcnt)
      by_cases hPfa : P (f a)
      · rw [if_pos hPfa, if_pos (htrace a haM hPfa)]
      · rw [if_neg hPfa]; exact Nat.zero_le _
  rw [Multiset.filter_map]
  calc (M.filter (fun a => P (f a))).map f
      = (M.filter (fun a => P (f a))).map g := by
        refine Multiset.map_congr rfl (fun a ha => ?_)
        rw [Multiset.mem_filter] at ha
        exact hcoh a ha.1 (htrace a ha.1 ha.2)
    _ ≤ (M.filter Q).map g := Multiset.map_le_map hmono
    _ ≤ N.map g := Multiset.map_le_map hsource

/-! ## Step 2 — right survivor saturation (filter transport + star freshness). -/

/-- **R-6c-body-539 ∎ — a right-survivor component is externally-leg-saturated.**  The survivor re-embeds a right-primitive
component `r.1.1` KEEPING its vertices / legs, and `r.1.1` is vertex-disjoint from the selected outer, so the global
retarget is the identity on its legs (`hcoh`) and any global retarget landing in `r.1.1.vertices ⊆ G.vertices` is NOT a
fresh star, hence the identity too (`htrace`).  Descends the SOURCE outer saturation `hOuter r.1.1`. -/
theorem rightSurvivorComponent_externalLegSaturated (Measure : ResolvedMeasureLeafSupply D)
    (Fstar : ResolvedCanonicalStarFacts D) (s : ResolvedCoassocSplitChoice D G)
    (hOuter : ResolvedForestExternalLegSaturated s.1.1)
    (r : {γ : {x : ResolvedFeynmanSubgraph G // x ∈ s.1.1.elements} // γ ∈ s.rightComponents}) :
    ResolvedExternalLegSaturated s.selectedOuterContractGraph
      ((survivorSupply_of_measure Measure G).survivorComponent s r) := by
  have hdisj : Disjoint r.1.1.vertices
      ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).vertices :=
    s.isRightPrimitive_disjoint_vertices_selectedOuterRaw (Finset.mem_filter.mp r.2).2
      (rightComponentNonempty_of_measure Measure s r)
  -- the survivor keeps `r.1.1`'s vertices / legs (`reembed`, `rfl`)
  show s.selectedOuterContractGraph.externalLegs.filter (fun ℓ => ℓ.attachedTo ∈ r.1.1.vertices)
    ≤ r.1.1.externalLegs
  have hSOleg : s.selectedOuterContractGraph.externalLegs
      = G.externalLegs.map (((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).retargetExternalLeg
          (D.starOf G ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s))) := rfl
  -- on `r.1.1`'s legs the global retarget is the identity
  have hmapid : r.1.1.externalLegs.map (((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).retargetExternalLeg
        (D.starOf G ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s))) = r.1.1.externalLegs := by
    conv_rhs => rw [← Multiset.map_id r.1.1.externalLegs]
    refine Multiset.map_congr rfl (fun ℓ hℓ => ?_)
    have hnot : ℓ.attachedTo ∉ ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).vertices :=
      fun h => Finset.disjoint_left.mp hdisj (r.1.1.legs_supported ℓ hℓ) h
    show ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).retargetExternalLeg
        (D.starOf G ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s)) ℓ = ℓ
    unfold ResolvedAdmissibleSubgraph.retargetExternalLeg ResolvedExternalLeg.retarget
    rw [ResolvedAdmissibleSubgraph.retargetVertex_of_not_mem _ _ hnot]
  rw [hSOleg, ← hmapid]
  refine mapped_externalLeg_filter_le_of_trace (Q := fun ℓ => ℓ.attachedTo ∈ r.1.1.vertices) ?_
    (hOuter r.1.1 r.1.2) (fun _ _ _ => rfl)
  intro ℓ _ hPf
  by_cases hsel : ℓ.attachedTo ∈ ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).vertices
  · exfalso
    have hfresh : (((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).retargetExternalLeg
        (D.starOf G ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s)) ℓ).attachedTo ∉ G.vertices := by
      show ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).retargetVertex
          (D.starOf G ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s)) ℓ.attachedTo ∉ G.vertices
      rw [retargetVertex_eq_star_of_mem _ _ hsel]
      exact Fstar.starOf_fresh G _ _
        (((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).componentAt_mem hsel)
    exact hfresh (r.1.1.vertices_subset hPf)
  · have heq : (((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).retargetExternalLeg
        (D.starOf G ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s)) ℓ).attachedTo = ℓ.attachedTo := by
      show ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).retargetVertex
          (D.starOf G ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s)) ℓ.attachedTo = ℓ.attachedTo
      exact ResolvedAdmissibleSubgraph.retargetVertex_of_not_mem _ _ hsel
    rwa [heq] at hPf

/-! ## Step 3 — the corrected remnant vertex trace ★LOAD-BEARING★. -/

/-- **R-6c-body-539 ∎ — the promoted-star contraction vertex trace.**  If the GLOBALLY-retargeted image of a `G`-vertex
`v` lands in the corrected remnant's promoted-star contraction vertex set, then `v` lies in the parent input-outer
component `o.γ.1`.  Two cases on the contract vertex union (survivor `\` / promoted-star), each split on whether `v` sits
in the selected outer.  Uses ONLY the selected-outer allocator's `starOf_fresh` / `starOf_injective` — NO strict
promoted-star equality, NO local-permutation comparison. -/
theorem promotedCorrectedOccurrence_vertex_trace (Fstar : ResolvedCanonicalStarFacts D)
    (s : ResolvedCoassocSplitChoice D G) (o : s.ForestChoiceOccurrence) {v : VertexId}
    (hvG : v ∈ G.vertices)
    (hmem : ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).retargetVertex
        (D.starOf G ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s)) v
      ∈ (o.B.1.contractWithStars (promotedOccurrenceStar s o)).vertices) :
    v ∈ o.γ.1.vertices := by
  rw [ResolvedAdmissibleSubgraph.contractWithStars_vertices,
    ResolvedFeynmanSubgraph.toResolvedFeynmanGraph_vertices, Finset.mem_union] at hmem
  by_cases hvsel : v ∈ ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).vertices
  · -- `v ∈ S`: the retarget image is the (fresh) star of `v`'s selected-outer component
    have hstareq : ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).retargetVertex
        (D.starOf G ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s)) v
        = D.starOf G ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s)
            (((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).componentAt hvsel) :=
      retargetVertex_eq_star_of_mem _ _ hvsel
    rcases hmem with hsurv | hstar
    · -- survivor branch: a fresh star cannot lie in `o.γ.1.vertices ⊆ G.vertices`
      exfalso
      rw [Finset.mem_sdiff, hstareq] at hsurv
      exact Fstar.starOf_fresh G _ _
        (((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).componentAt_mem hvsel)
        (o.γ.1.vertices_subset hsurv.1)
    · -- promoted-star branch: injectivity of the selected-outer allocator recovers the owner
      rw [ResolvedAdmissibleSubgraph.mem_starVertices] at hstar
      obtain ⟨b, hb, hbw⟩ := hstar
      have hpromEq : o.γ.1.promote b
          = ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).componentAt hvsel :=
        Fstar.starOf_injective G _
          (promote_mem_selectedOuterRawOf_raw s o hb)
          (((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).componentAt_mem hvsel)
          (hbw.trans hstareq)
      have hv_in : v ∈ (o.γ.1.promote b).vertices := by
        rw [hpromEq]
        exact ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).componentAt_vertex_mem hvsel
      exact ResolvedFeynmanSubgraph.promote_vertices_subset_parent o.γ.1 b hv_in
  · -- `v ∉ S`: the retarget image is `v` itself
    have hid : ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).retargetVertex
        (D.starOf G ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s)) v = v :=
      ResolvedAdmissibleSubgraph.retargetVertex_of_not_mem _ _ hvsel
    rw [hid] at hmem
    rcases hmem with hsurv | hstar
    · rw [Finset.mem_sdiff] at hsurv; exact hsurv.1
    · -- `v` a promoted star: fresh, contradicting `v ∈ G.vertices`
      exfalso
      rw [ResolvedAdmissibleSubgraph.mem_starVertices] at hstar
      obtain ⟨b, hb, hbv⟩ := hstar
      rw [← hbv] at hvG
      exact Fstar.starOf_fresh G _ (o.γ.1.promote b) (promote_mem_selectedOuterRawOf_raw s o hb) hvG

/-! ## Step 4 — corrected remnant saturation (coherence + traceability). -/

/-- **R-6c-body-539 ∎ — a corrected remnant component is externally-leg-saturated.**  Its legs are the promoted-star
contraction's `o.γ.1.externalLegs.map (o.B.1.retargetExternalLeg (promotedOccurrenceStar s o))` (body-456/464), and on
`o.γ.1`'s legs the global retarget agrees with that local retarget (body-459 `hcoh`); the traceability `htrace` is Step 3.
Descends the SOURCE outer saturation `hOuter o.γ.1`. -/
theorem correctedRemnantComponent_externalLegSaturated (Fstar : ResolvedCanonicalStarFacts D)
    (CarrierProper : ResolvedCarrierProperProvider D) (s : ResolvedCoassocSplitChoice D G)
    (o : s.ForestChoiceOccurrence)
    (hL : ∀ ℓ ∈ G.externalLegs, ℓ.attachedTo ∈ G.vertices)
    (hOuter : ResolvedForestExternalLegSaturated s.1.1) :
    ResolvedExternalLegSaturated s.selectedOuterContractGraph
      ((canonicalCorrectedRemnantComponentSupply Fstar CarrierProper).remnantComponent s o) := by
  have hrv : ((canonicalCorrectedRemnantComponentSupply Fstar CarrierProper).remnantComponent s o).vertices
      = (o.B.1.contractWithStars (promotedOccurrenceStar s o)).vertices :=
    correctedRemnantComponent_vertices_eq_promoted s o Fstar
  have h1 : ((canonicalCorrectedRemnantComponentSupply Fstar CarrierProper).remnantComponent s o).externalLegs
      = (o.B.1.contractWithStars (promotedOccurrenceStar s o)).externalLegs :=
    (promotedCorrectedSource_externalLegs Fstar s o).symm
  have hrl : ((canonicalCorrectedRemnantComponentSupply Fstar CarrierProper).remnantComponent s o).externalLegs
      = o.γ.1.externalLegs.map (o.B.1.retargetExternalLeg (promotedOccurrenceStar s o)) := by
    rw [h1, ResolvedAdmissibleSubgraph.contractWithStars_externalLegs,
      ResolvedFeynmanSubgraph.toResolvedFeynmanGraph_externalLegs]
  show s.selectedOuterContractGraph.externalLegs.filter
      (fun ℓ => ℓ.attachedTo ∈ ((canonicalCorrectedRemnantComponentSupply Fstar CarrierProper).remnantComponent s o).vertices)
    ≤ ((canonicalCorrectedRemnantComponentSupply Fstar CarrierProper).remnantComponent s o).externalLegs
  have hSOleg : s.selectedOuterContractGraph.externalLegs
      = G.externalLegs.map (((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).retargetExternalLeg
          (D.starOf G ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s))) := rfl
  rw [hrv, hrl, hSOleg]
  refine mapped_externalLeg_filter_le_of_trace
    (Q := fun ℓ => ℓ.attachedTo ∈ o.γ.1.vertices) ?_ (hOuter o.γ.1 o.γ.2) ?_
  · intro ℓ hℓ hP
    exact promotedCorrectedOccurrence_vertex_trace Fstar s o (hL ℓ hℓ) hP
  · intro ℓ _ hQ
    exact (promoted_retargetExternalLeg_eq_selectedOuter s o hQ).symm

/-! ## Step 5 — forest / union assembly. -/

/-- **R-6c-body-539 ∎ — the right-survivor forest is external-leg-saturated.** -/
theorem rightSurvivorForest_forestExternalLegSaturated (Measure : ResolvedMeasureLeafSupply D)
    (Fstar : ResolvedCanonicalStarFacts D) (s : ResolvedCoassocSplitChoice D G)
    (hOuter : ResolvedForestExternalLegSaturated s.1.1) :
    ResolvedForestExternalLegSaturated ((survivorSupply_of_measure Measure G).rightSurvivorForest s) := by
  intro δ hδ
  rw [ResolvedRightSurvivorSupply.rightSurvivorForest_elements] at hδ
  obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hδ
  exact rightSurvivorComponent_externalLegSaturated Measure Fstar s hOuter r

/-- **R-6c-body-539 ∎ — the corrected remnant forest is external-leg-saturated.** -/
theorem correctedRemnantForest_forestExternalLegSaturated (Fstar : ResolvedCanonicalStarFacts D)
    (CarrierProper : ResolvedCarrierProperProvider D) (s : ResolvedCoassocSplitChoice D G)
    (hL : ∀ ℓ ∈ G.externalLegs, ℓ.attachedTo ∈ G.vertices)
    (hOuter : ResolvedForestExternalLegSaturated s.1.1) :
    ResolvedForestExternalLegSaturated
      ((canonicalCorrectedRemnantComponentSupply Fstar CarrierProper).remnantForest s) := by
  intro δ hδ
  rw [ResolvedRemnantComponentSupply.remnantForest_elements] at hδ
  obtain ⟨γ, _, rfl⟩ := Finset.mem_image.mp hδ
  exact correctedRemnantComponent_externalLegSaturated Fstar CarrierProper s
    (s.forestComponentOccurrence γ) hL hOuter

/-- **R-6c-body-539 ∎ — the corrected quotient is external-leg-saturated.**  `union` of the right-survivor forest (Step 5a)
and the corrected remnant forest (Step 5b) inherits saturation (body-534 `resolvedForestExternalLegSaturated_union`) — THE
LAST combinatorial fourth-axis checkpoint. -/
theorem canonicalCorrectedQuotientRaw_forestExternalLegSaturated (Measure : ResolvedMeasureLeafSupply D)
    (CarrierProper : ResolvedCarrierProperProvider D) (Fstar : ResolvedCanonicalStarFacts D)
    (s : ResolvedCoassocSplitChoice D G)
    (hL : ∀ ℓ ∈ G.externalLegs, ℓ.attachedTo ∈ G.vertices)
    (hOuter : ResolvedForestExternalLegSaturated s.1.1) :
    ResolvedForestExternalLegSaturated (canonicalCorrectedQuotientRaw Measure CarrierProper Fstar s) := by
  unfold canonicalCorrectedQuotientRaw
  exact resolvedForestExternalLegSaturated_union _ _ _
    (rightSurvivorForest_forestExternalLegSaturated Measure Fstar s hOuter)
    (correctedRemnantForest_forestExternalLegSaturated Fstar CarrierProper s hL hOuter)

end GaugeGeometry.QFT.Combinatorial
