import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocQuotientPartitionMulti

/-!
# R-6c-body-345 — survivor tag partition: `isRightPrimitive(recovered) ↔ rightRecovered` (PROVED)

Three-hundred-and-forty-fifth genuine-body step — stage 1 of the survivor collection alignment.  The
right-primitive components of the reconstruction `recoveredPreimageValue z` are EXACTLY the right region's
components, read directly off body-282's `recoverChoiceValue` tags — no 6-gate bridge, no forward round-trip,
no survivor round-trip yet.  This is the `recovered`-specific structure the abstract `fwd q` bridge cannot see.

## The characterization

`isRightPrimitive (recovered) γ` unfolds (via `choiceAt_recovered_eq'`, body-340) to
`recoverChoiceValue z γ = Sum.inl false`.  The `dite` cascade (`leftResidual → inl true`, `rightRecovered →
inl false`, `forestRecovered → inr`, else `inl true`) hits `inl false` on EXACTLY the `rightRecovered` branch:

* `⟸` `right_tag` (body-282): `γ.1 ∈ rightRecovered ⟹ recoverChoiceValue = inl false`;
* `⟹` case split on the three memberships — every other branch is `inl true` / `inr`, so `inl false` forces
  `γ.1 ∈ rightRecovered`.

Landed axiom-clean: `mem_rightComponents_iff`.

Per the HALT: only the tag partition is proved (stage 1); the survivor round-trip
`survivorComponent(recovered)(rightReembed δ) = δ` (stage 2, the `HEq` cross-graph identity) and the collection
`HEq` bridge (stage 3, feeding body-290's `heq_finset_of_mem_iff` / body-344's `quotient_elements_heq`) are the
next survivor step; the six bridge gates, forward round-trip, carrier membership, and remnant geometry are NOT
used.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

variable {D : ResolvedCoproductProperForestData}

set_option linter.unusedSectionVars false

namespace ResolvedRegionTagValueSupply

variable {Fmem : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}

/-- **R-6c-body-345 — the right-primitive components of the reconstruction are the right region.**  Pure tag
characterization (`recoverChoiceValue` + `right_tag`), specific to `recoveredPreimageValue z`. -/
theorem mem_rightComponents_iff (T : ResolvedRegionTagValueSupply Fmem V)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ (T.Closure.unionOuterValue z).1.elements}) :
    γ ∈ ResolvedCoassocSplitChoice.rightComponents (T.recoveredPreimageValue z)
      ↔ γ.1 ∈ (T.Closure.Assembly.Region.rightRecovered z).elements := by
  constructor
  · intro h
    rw [ResolvedCoassocSplitChoice.rightComponents] at h
    have hp : ResolvedCoassocSplitChoice.choiceAt (T.recoveredPreimageValue z) γ = Sum.inl false :=
      (Finset.mem_filter.mp h).2
    rcases (T.Closure.mem_unionOuterValue_iff z γ.1).mp γ.2 with hl | hr | hf
    · exact absurd (Sum.inl.inj
        (hp.symm.trans ((T.choiceAt_recovered_eq' z γ).trans (T.left_tag z γ hl)))) (by decide)
    · exact hr
    · obtain ⟨B, hB⟩ := T.forest_tag z γ hf
      exact absurd (hp.symm.trans ((T.choiceAt_recovered_eq' z γ).trans hB)) Sum.inl_ne_inr
  · intro h
    rw [ResolvedCoassocSplitChoice.rightComponents]
    refine Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, ?_⟩
    show ResolvedCoassocSplitChoice.choiceAt (T.recoveredPreimageValue z) γ = Sum.inl false
    rw [T.choiceAt_recovered_eq' z γ]
    exact T.right_tag z γ h

end ResolvedRegionTagValueSupply

end GaugeGeometry.QFT.Combinatorial
