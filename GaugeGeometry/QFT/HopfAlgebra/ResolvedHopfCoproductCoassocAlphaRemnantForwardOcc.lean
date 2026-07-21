import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaRecoveredExactB

/-!
# R-6c-body-507 — alpha remnant correspondence migrated onto the recovered tag construction (PROVED)

Five-hundred-and-seventh genuine-body step — the last direct `OccInv` consumer migration.  Body-495's
`remnant_mem_alpha` uses `M.innerIdx_occurrence S z δ (recovered) o hp` at the RECOVERED `z`; body-506's
`recoveredOccurrence_B_heq_innerIdx_alpha` supplies the SAME `HEq (occurrence.B) (M.innerIdx z δ)` from the recovered
choice's own inserted `forestTag` — so the legacy `∀ s` `OccInv` supply `S` is dropped in favour of `Measure + hFT`.  The
body-506 helper's orientation is already `HEq o.B (M.innerIdx z δ)`, so the legacy `.symm` disappears.

## Migrated (Phase 1)

```text
remnant_mem_alpha_forwardOcc
```

Both `(M.innerIdx_occurrence S z δ (recovered) o hp).symm` atoms become
`T.recoveredOccurrence_B_heq_innerIdx_alpha M Fstar Measure hForest hFT z γ δ hp'` (no `.symm`); body-489's raw `hround`
consumes the resulting `hidx` unchanged.  `ForwardOcc` is NOT used on the recovered branch (that is the forward-`q`
consumers' owner); this branch reads the tag it wrote.

Phases 2–4 (the single canonical owner chain `AssemblyF` / `TagsF` / `houterF` / geometry bridges / membership boundary /
round-trip / final quotient-root wrapper) are the body-508 continuation (per the plan's safe-stop — the remnant
correspondence is the last direct consumer; the owner-threading assembly is deferred rather than rushed, the only real
risk there being double owner issuance, not mathematics).

Per the HALT/guards: the forward socket is NOT applied on the recovered branch; no backward socket; `hidx` is NOT
back-computed from `remnant_mem` / quotient HEq / coassoc; body-489 is NOT reverse-used for `hidx`; the legacy body-495
stays a valid conditional (NON-destructive); `quot_eq` / `legComplete` are NOT entered; strict `StarProm` / `InnerStarRaw`
stay ZERO; NO unconditional-coassoc claim.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO
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

variable {D : ResolvedCoproductProperForestData}
  {Fmem : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedFilteredConcreteSummandValueSupply D}

namespace ResolvedRegionTagAlphaValueSupply

/-- **R-6c-body-507 ∎ — `remnant_mem`, on the recovered tag construction** (body-495 mirror; `recoveredOccurrence_B`
replaces `innerIdx_occurrence S`, so no `∀ s` `OccInv`). -/
theorem remnant_mem_alpha_forwardOcc (M : ResolvedMultiStarDecontractionSupply D)
    (Fstar : ResolvedCanonicalStarFacts D) (Measure : ResolvedMeasureLeafSupply D)
    (CarrierProper : ResolvedCarrierProperProvider D) (T : ResolvedRegionTagAlphaValueSupply Fmem V)
    (hFT : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
      (γ' : {x : ResolvedFeynmanSubgraph G // x ∈ (T.Closure.unionOuterAlphaValue z).1.elements})
      (h : γ'.1 ∈ (T.Closure.Assembly.Region.forestRecovered z).elements)
      (h' : γ'.1 ∈ (M.forestRecoveredMulti Fstar z).elements),
      T.forestTag z γ' h = M.forestTag Fstar z ⟨γ'.1, h'⟩)
    (hForest : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
      (T.Closure.Assembly.Region.forestRecovered z).elements
        = (M.forestRecoveredMulti Fstar z).elements)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (houter : (resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf
      (T.recoveredPreimageAlphaValue z) = z.1.1)
    (x₁ : ResolvedFeynmanSubgraph (ResolvedCoassocSplitChoice.selectedOuterContractGraph
      (T.recoveredPreimageAlphaValue z)))
    (x₂ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
    (hx : HEq x₁ x₂) :
    x₁ ∈ ((canonicalCorrectedRemnantComponentSupply Fstar CarrierProper).remnantForest
        (T.recoveredPreimageAlphaValue z)).elements
      ↔ x₂ ∈ forestDomain z := by
  have hround : ∀ (γ : {x : {y : ResolvedFeynmanSubgraph G //
        y ∈ (T.recoveredPreimageAlphaValue z).1.1.elements} // x ∈
        ResolvedCoassocSplitChoice.forestComponents (T.recoveredPreimageAlphaValue z)})
      (δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) //
        x ∈ forestDomain z}),
      (ResolvedCoassocSplitChoice.forestComponentOccurrence (T.recoveredPreimageAlphaValue z) γ).γ.1 = M.parent z δ →
      HEq (ResolvedCoassocSplitChoice.forestComponentOccurrence (T.recoveredPreimageAlphaValue z) γ).B (M.innerIdx z δ) →
      HEq ((canonicalCorrectedRemnantComponentSupply Fstar CarrierProper).remnantComponent
        (T.recoveredPreimageAlphaValue z)
        (ResolvedCoassocSplitChoice.forestComponentOccurrence (T.recoveredPreimageAlphaValue z) γ)) δ.1 := by
    intro γ δ hp hi
    have hConn : (touchedLocalComponent z δ.1).forget.IsConnected :=
      (touchedLocalComponent_isConnectedDivergent z δ.1
        (z.2.1.isConnectedDivergent δ.1 (Finset.mem_filter.mp δ.2).1)).1
    have hPos : 0 < (touchedLocalComponent z δ.1).internalEdges.card := by
      rw [touchedLocalComponent_internalEdges]
      exact (CarrierProper.carrier_isProperForest _ z.2.1 z.2.2).2.2.2.1 δ.1
        (Finset.mem_filter.mp δ.2).1
    exact canonicalCorrectedRemnantComponent_roundtrip_raw M z δ (T.recoveredPreimageAlphaValue z)
      (ResolvedCoassocSplitChoice.forestComponentOccurrence (T.recoveredPreimageAlphaValue z) γ) Fstar
      hp hi hConn hPos houter
  constructor
  · intro hx₁
    rw [ResolvedRemnantComponentSupply.remnantForest_elements] at hx₁
    obtain ⟨γ, -, hγ⟩ := Finset.mem_image.mp hx₁
    have hfr : γ.1.1 ∈ (M.forestRecoveredMulti Fstar z).elements := by
      rw [← hForest]; exact (T.mem_forestComponents_iff_alpha z γ.1).mp γ.2
    have hp : M.parent z (M.forestSource Fstar z ⟨γ.1.1, hfr⟩) = γ.1.1 :=
      M.forestSource_spec Fstar z ⟨γ.1.1, hfr⟩
    have hi : HEq (ResolvedCoassocSplitChoice.forestComponentOccurrence (T.recoveredPreimageAlphaValue z) γ).B
        (M.innerIdx z (M.forestSource Fstar z ⟨γ.1.1, hfr⟩)) :=
      T.recoveredOccurrence_B_heq_innerIdx_alpha M Fstar Measure hForest hFT z γ
        (M.forestSource Fstar z ⟨γ.1.1, hfr⟩) hp.symm
    have hheq := hround γ (M.forestSource Fstar z ⟨γ.1.1, hfr⟩) hp.symm hi
    rw [hγ] at hheq
    have hx₂eq : x₂ = (M.forestSource Fstar z ⟨γ.1.1, hfr⟩).1 := eq_of_heq (hx.symm.trans hheq)
    rw [hx₂eq]; exact (M.forestSource Fstar z ⟨γ.1.1, hfr⟩).2
  · intro hx₂
    have hmemMulti : M.parent z ⟨x₂, hx₂⟩ ∈ (M.forestRecoveredMulti Fstar z).elements := by
      rw [M.forestRecoveredMulti_elements Fstar z]
      exact Finset.mem_image.mpr ⟨⟨x₂, hx₂⟩, Finset.mem_attach _ _, rfl⟩
    have hfrec : M.parent z ⟨x₂, hx₂⟩ ∈ (T.Closure.Assembly.Region.forestRecovered z).elements := by
      rw [hForest]; exact hmemMulti
    have hmemU : M.parent z ⟨x₂, hx₂⟩ ∈ (T.Closure.unionOuterAlphaValue z).1.elements :=
      (T.Closure.mem_unionOuterAlphaValue_iff z _).mpr (Or.inr (Or.inr hfrec))
    have hfc : (⟨M.parent z ⟨x₂, hx₂⟩, hmemU⟩ :
        {y : ResolvedFeynmanSubgraph G // y ∈ (T.recoveredPreimageAlphaValue z).1.1.elements})
        ∈ ResolvedCoassocSplitChoice.forestComponents (T.recoveredPreimageAlphaValue z) :=
      (T.mem_forestComponents_iff_alpha z ⟨M.parent z ⟨x₂, hx₂⟩, hmemU⟩).mpr hfrec
    set γ : {x : {y : ResolvedFeynmanSubgraph G // y ∈ (T.recoveredPreimageAlphaValue z).1.1.elements} //
        x ∈ ResolvedCoassocSplitChoice.forestComponents (T.recoveredPreimageAlphaValue z)} :=
      ⟨⟨M.parent z ⟨x₂, hx₂⟩, hmemU⟩, hfc⟩ with hγdef
    have hi : HEq (ResolvedCoassocSplitChoice.forestComponentOccurrence (T.recoveredPreimageAlphaValue z) γ).B
        (M.innerIdx z ⟨x₂, hx₂⟩) :=
      T.recoveredOccurrence_B_heq_innerIdx_alpha M Fstar Measure hForest hFT z γ ⟨x₂, hx₂⟩ rfl
    have hheq := hround γ ⟨x₂, hx₂⟩ rfl hi
    have hx₁eq : x₁ = (canonicalCorrectedRemnantComponentSupply Fstar CarrierProper).remnantComponent
        (T.recoveredPreimageAlphaValue z)
        (ResolvedCoassocSplitChoice.forestComponentOccurrence (T.recoveredPreimageAlphaValue z) γ) :=
      eq_of_heq (hx.trans hheq.symm)
    rw [hx₁eq, ResolvedRemnantComponentSupply.remnantForest_elements]
    exact Finset.mem_image.mpr ⟨γ, Finset.mem_attach _ _, rfl⟩

end ResolvedRegionTagAlphaValueSupply

end GaugeGeometry.QFT.Combinatorial
