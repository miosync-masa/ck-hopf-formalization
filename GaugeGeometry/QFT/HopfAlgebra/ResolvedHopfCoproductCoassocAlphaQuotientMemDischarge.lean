import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaSurvivorDischarge
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecoveredRawProperAudit
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRemnantSupport
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocIsNonemptyTransfer
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSelectedOuterNonempty
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocFilteredQuotientValue

/-!
# R-6c-body-499 — filtered canonical quotient membership: the five conditions, four discharged (PROVED)

Four-hundred-and-ninety-ninth genuine-body step — the fourth stop of the residual-purification campaign.  The reduced
quotient root's sole opaque field is `quotient_mem` (body-469): the forward quotient value
`canonicalCorrectedQuotientRaw Measure W'.toCarrierProperProvider canonicalUniqueStarFactsOfW' q.1` lies in `W'`'s
carrier over the contracted graph `H := q.1.selectedOuterContractGraph`.  This body normalizes that membership through
`mem_canonicalUniqueSupportedCarrier_iff` and discharges FOUR of the five conditions, reducing `quotient_mem` to the sole
strict-count residual `0 < complementEdges.card`.

## The four ambient conditions of `H` (DERIVED)

`H = (selectedOuterRawOf q.1).contractWithStars (starOf)`.  Each ambient fact transfers through the contraction:

* **`ResolvedAmbientSupported H`** — `contractWithStars_{internal,external}_supported` (body-425), fed the outer's own
  live ambient support `canonicalUniqueSupportedCarrier_ambientSupported q.1.1.2`;
* **`H.forget.IsConnectedDivergent`** — `Measure.contract_preserves_CD` (CK contraction stability) applied to the
  selected outer, with the ambient CD `canonicalUniqueSupportedCarrier_ambientCD q.1.1.2` fed as its class version
  (`isConnectedDivergent_toClass`, `Iff.rfl`);
* **`H.EdgeIdsUnique` / `H.LegIdsUnique`** — the two generic banked lemmas `{edge,leg}IdsUnique_contractWithStars`: the
  contract graph's edges/legs are `map (retargetEdge/Leg)` of `G`'s, and the retarget keeps `edgeId`/`legId`
  (`retarget_{edgeId,legId}`, `rfl`), so id-uniqueness transfers from `{edge,leg}IdsUnique_of_carrier_mem q.1.1.2`.
  No `Nodup`, no global-`∀ G` uniqueness.

## The `IsProperForest` conjuncts (1–4 DERIVED)

`isProperForest_of_isNonempty_complement` (body-428) reduces `IsProperForest` to `IsNonempty` (conjunct 1) +
`0 < complementEdges.card` (conjunct 5), discharging conjuncts 2/4 generically (the measure leaves `N`/`E`) and 3 from
1 + 4.  Conjunct 1 is the FILTERED advantage: `canonicalCorrectedQuotientRaw_isNonempty` uses `p ≠ p_L` (from the
forest-block filter) — a non-left component is right-primitive (→ a survivor component) or a forest choice (→ a corrected
remnant component), and either populates the survivor ∪ remnant union.  This is the non-circular route body-428's audit
called for.

## The sole residual

`canonicalCorrectedQuotient_mem_of_complement` assembles the four ambient conditions + the derived `IsNonempty` + the
reduction, leaving ONE named hypothesis: `0 < (canonicalCorrectedQuotientRaw ... q.1).complementEdges.card`.  Per the
body-428 verdict and the body-468 no-go, quotient complement positivity is the strict-count witness — its own object
(distinct from the recovered-outer `regionRawUnion_count_lt`, which is over `G`, not the contract graph `H`).  So this
body STOPS there; `quotient_mem` is NOT completed and the reduced quotient root is NOT edited.

```text
ambient support / CD / EdgeIds / LegIds   DERIVED
IsProperForest conjuncts 1–4               DERIVED
0 < complementEdges.card                    SOLE NAMED RESIDUAL  (strict-count, deferred to body-500)
```

Per the HALT/guards: `IsProperForest → membership` shortcut is NOT taken (all five `W'` conditions supplied); no raw
`∀ s` quotient membership (filtered `q` only, `p_L` no-go respected); no global ID uniqueness / `Nodup`; `quot_eq` /
`OccRaw` / `ValueGeometry` NOT entered; strict `StarProm` / `InnerStarRaw` stay ZERO; body-445 and the reduced root
(body-498) are NOT edited; NO unconditional-coassoc claim.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO
`promote_collapse` / singleton / floor-297.
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

/-! ## Generic contract-graph id-uniqueness (`retarget` keeps ids) -/

variable {G : ResolvedFeynmanGraph}

/-- **R-6c-body-499 ∎ — `contractWithStars` preserves edge-id uniqueness.**  `H`'s internal edges are
`A.complementEdges.map (A.retargetEdge starOf)` and the retarget keeps `edgeId`, so equal ids pull back to equal ids in
`G` and `G.EdgeIdsUnique` closes. -/
theorem edgeIdsUnique_contractWithStars (A : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId) (hId : G.EdgeIdsUnique) :
    (A.contractWithStars starOf).EdgeIdsUnique := by
  intro e₁' he₁' e₂' he₂' hid
  rw [ResolvedAdmissibleSubgraph.contractWithStars_internalEdges] at he₁' he₂'
  obtain ⟨e₁, he₁, rfl⟩ := Multiset.mem_map.mp he₁'
  obtain ⟨e₂, he₂, rfl⟩ := Multiset.mem_map.mp he₂'
  have hm₁ : e₁ ∈ G.internalEdges := Multiset.mem_of_le (Multiset.sub_le_self _ _) he₁
  have hm₂ : e₂ ∈ G.internalEdges := Multiset.mem_of_le (Multiset.sub_le_self _ _) he₂
  have hee : e₁ = e₂ := by
    refine hId e₁ hm₁ e₂ hm₂ ?_
    simpa only [ResolvedAdmissibleSubgraph.retargetEdge, ResolvedFeynmanEdge.retarget_edgeId] using hid
  rw [hee]

/-- **R-6c-body-499 ∎ — `contractWithStars` preserves leg-id uniqueness.**  `H`'s external legs are
`G.externalLegs.map (A.retargetExternalLeg starOf)` and the retarget keeps `legId`. -/
theorem legIdsUnique_contractWithStars (A : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId) (hId : G.LegIdsUnique) :
    (A.contractWithStars starOf).LegIdsUnique := by
  intro ℓ₁' hℓ₁' ℓ₂' hℓ₂' hid
  rw [ResolvedAdmissibleSubgraph.contractWithStars_externalLegs] at hℓ₁' hℓ₂'
  obtain ⟨ℓ₁, hℓ₁, rfl⟩ := Multiset.mem_map.mp hℓ₁'
  obtain ⟨ℓ₂, hℓ₂, rfl⟩ := Multiset.mem_map.mp hℓ₂'
  have hll : ℓ₁ = ℓ₂ := by
    refine hId ℓ₁ hℓ₁ ℓ₂ hℓ₂ ?_
    simpa only [ResolvedAdmissibleSubgraph.retargetExternalLeg, ResolvedExternalLeg.retarget_legId] using hid
  rw [hll]

/-! ## The non-left witness (mirror of `exists_nonright_of_ne_pR`) -/

variable {D : ResolvedCoproductProperForestData}

/-- **R-6c-body-499 — a non-all-left choice has a non-`inl true` component.**  If `p ≠ p_L`
(`fun _ _ => Sum.inl true`), some component's tag is not `Sum.inl true`. -/
theorem exists_nonleft_of_ne_pL
    {A : {A : ResolvedAdmissibleSubgraph G // A ∈ D.carrier G}}
    {p : ∀ γ ∈ A.1.elements.attach, Bool ⊕ (D.supply (γ.1.toResolvedFeynmanGraph)).ForestIdx}
    (hL : p ≠ (fun _ _ => Sum.inl true)) :
    ∃ (γ : {x : ResolvedFeynmanSubgraph G // x ∈ A.1.elements}) (hγ : γ ∈ A.1.elements.attach),
      p γ hγ ≠ Sum.inl true := by
  by_contra h
  push_neg at h
  exact hL (funext fun γ => funext fun hγ => h γ hγ)

/-! ## The quotient `IsNonempty` (conjunct 1) — the filtered `p ≠ p_L` route -/

/-- **R-6c-body-499 ∎ — the forward quotient value is nonempty.**  On the filtered domain `p ≠ p_L`, a non-left
component is right-primitive (→ a survivor component in the union) or a forest choice (→ a corrected remnant component in
the union), so `canonicalCorrectedQuotientRaw` (the survivor ∪ corrected-remnant union) has a nonempty component set. -/
theorem canonicalCorrectedQuotientRaw_isNonempty (Measure : ResolvedMeasureLeafSupply D)
    (CarrierProper : ResolvedCarrierProperProvider D) (Fstar : ResolvedCanonicalStarFacts D)
    (q : FilteredForestBlockDom D G) :
    (canonicalCorrectedQuotientRaw Measure CarrierProper Fstar q.1).IsNonempty := by
  have hp : q.1.2 ∈ forestChoiceCarrier q.1.1 := by
    have h := q.2
    simp only [forestBlockDomFinset, Finset.mem_sigma] at h
    exact h.2
  have hpL : q.1.2 ≠ (fun _ _ => Sum.inl true) := (Finset.mem_filter.mp hp).2.2
  obtain ⟨γ, hγ, hne⟩ := exists_nonleft_of_ne_pL hpL
  have hc : ResolvedCoassocSplitChoice.choiceAt q.1 γ ≠ Sum.inl true := by
    rw [ResolvedCoassocSplitChoice.choiceAt]; exact hne
  have hraw : canonicalCorrectedQuotientRaw Measure CarrierProper Fstar q.1
      = ((survivorSupply_of_measure Measure G).rightSurvivorForest q.1).union
          ((canonicalCorrectedRemnantComponentSupply Fstar CarrierProper).remnantForest q.1)
          ((canonicalCorrectedQuotientForestCrossSupply Fstar Measure CarrierProper).cross q.1) := rfl
  rw [hraw]
  rcases hcc : ResolvedCoassocSplitChoice.choiceAt q.1 γ with b | B
  · cases b
    · -- right-primitive → survivor
      have hγR : γ ∈ ResolvedCoassocSplitChoice.rightComponents q.1 :=
        Finset.mem_filter.mpr ⟨hγ, hcc⟩
      refine ResolvedAdmissibleSubgraph.union_isNonempty_left _ ?_
      refine ⟨(survivorSupply_of_measure Measure G).survivorComponent q.1 ⟨γ, hγR⟩, ?_⟩
      rw [ResolvedRightSurvivorSupply.rightSurvivorForest_elements]
      exact Finset.mem_image.mpr ⟨⟨γ, hγR⟩, Finset.mem_attach _ _, rfl⟩
    · exact absurd hcc hc
  · -- forest choice → corrected remnant
    have hγF : γ ∈ ResolvedCoassocSplitChoice.forestComponents q.1 :=
      Finset.mem_filter.mpr ⟨hγ, ⟨B, hcc⟩⟩
    refine ResolvedAdmissibleSubgraph.union_isNonempty_right _ ?_
    refine ⟨(canonicalCorrectedRemnantComponentSupply Fstar CarrierProper).remnantComponent q.1
      (ResolvedCoassocSplitChoice.forestComponentOccurrence q.1 ⟨γ, hγF⟩), ?_⟩
    rw [ResolvedRemnantComponentSupply.remnantForest_elements]
    exact Finset.mem_image.mpr ⟨⟨γ, hγF⟩, Finset.mem_attach _ _, rfl⟩

/-! ## The canonical `W'` assembly — `quotient_mem` reduced to the sole complement residual -/

/-- **R-6c-body-499 ∎ — canonical filtered quotient membership, modulo the strict-count residual.**  All four ambient
conditions of the contract graph `H` and `IsProperForest` conjuncts 1–4 are discharged; the SOLE remaining hypothesis is
`0 < complementEdges.card` (conjunct 5), the strict-count witness (deferred).  This exhibits `quotient_mem` as a single
named residual over the filtered `q`. -/
theorem canonicalCorrectedQuotient_mem_of_complement
    (Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    (E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H)
    (q : FilteredForestBlockDom canonicalUniqueSupportedCarrierProperSupply.toData G)
    (hCompl : 0 < (canonicalCorrectedQuotientRaw Measure
      canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
      canonicalUniqueStarFactsOfW' q.1).complementEdges.card) :
    canonicalCorrectedQuotientRaw Measure
        canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
        canonicalUniqueStarFactsOfW' q.1
      ∈ canonicalUniqueSupportedCarrierProperSupply.toData.carrier
          (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1) := by
  set A := (resolvedConcreteForestPromoteSupply
    canonicalUniqueSupportedCarrierProperSupply.toData G).selectedOuterRawOf q.1 with hA
  have hAmbG : ResolvedAmbientSupported G := canonicalUniqueSupportedCarrier_ambientSupported q.1.1.2
  have hCDG : G.forget.IsConnectedDivergent := canonicalUniqueSupportedCarrier_ambientCD q.1.1.2
  refine (mem_canonicalUniqueSupportedCarrier_iff _).mpr ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · -- ResolvedAmbientSupported H (edges)
    exact A.contractWithStars_internalEdges_supported _ hAmbG.1
  · -- ResolvedAmbientSupported H (legs)
    exact A.contractWithStars_externalLegs_supported _ hAmbG.2
  · -- H.forget.IsConnectedDivergent
    exact Measure.contract_preserves_CD G A hCDG
  · -- H.EdgeIdsUnique
    exact edgeIdsUnique_contractWithStars A _ (edgeIdsUnique_of_carrier_mem q.1.1.2)
  · -- H.LegIdsUnique
    exact legIdsUnique_contractWithStars A _ (legIdsUnique_of_carrier_mem q.1.1.2)
  · -- IsProperForest, reduced to conjunct 1 + conjunct 5
    exact isProperForest_of_isNonempty_complement
      (Measure.toConnectedDivergentNonemptySupply _) (E _) _
      (canonicalCorrectedQuotientRaw_isNonempty Measure _ _ q) hCompl

end GaugeGeometry.QFT.Combinatorial
