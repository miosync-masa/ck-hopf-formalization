import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRemnantRoundTrip

/-!
# R-6c-body-359 — remnant collection: `HEq (remnantForest recovered).elements (forestDomain z)` (PROVED)

Three-hundred-and-fifty-ninth genuine-body step — the remnant collection `HEq`, the exact mirror of body-347
(survivor).  Body-206's `heq_finset_of_mem_iff` reduces it to a membership bridge, closed both ways by the tag
partition (body-348) and the component round-trip (body-358, received as `hround`), with the round-trip's `HEq`
consumed INSIDE the membership predicate and the ambient aligned by body-341's `houter`.

* **Forward** — `x₁ ∈ remnantForest` gives a forest component `γ` (image); body-348 lands `γ.1.1 ∈ forestRecovered`;
  `hForest` recovers `δ := forestSource γ.1.1 ∈ forestDomain` with `M.parent z δ = γ.1.1` (`forestSource_spec`);
  body-343's `innerIdx_occurrence` gives `HEq (occurrence γ).B (innerIdx z δ)`; `hround` then gives `HEq x₁ δ`.
* **Backward** — `x₂ ∈ forestDomain` gives `δ`; `M.parent z δ ∈ forestRecovered` (image); body-348 (mpr) lands it
  in `forestComponents`; `hround` gives `HEq (remnant image) x₂`.

Landed axiom-clean: `remnantForest_elements_heq`.

Per the HALT: only the collection `HEq` is proved; the round-trip `hround` (body-358 for the concrete remnant),
`hForest` (`forestRecovered = forestRecoveredMulti`, an rfl for the concrete `T`), and the assembly into
`quotient_elements_heq` (body-360) stay supplied gates; the full `V.Remnant` provider is NOT claimed complete;
no forward quotient / global forward round-trip.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO
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

variable {D : ResolvedCoproductProperForestData}

set_option linter.unusedSectionVars false

namespace ResolvedMultiStarDecontractionSupply

variable (M : ResolvedMultiStarDecontractionSupply D)
  {Fmem : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}

/-- **R-6c-body-359 — the remnant collection HEq.** -/
theorem remnantForest_elements_heq (Fstar : ResolvedCanonicalStarFacts D)
    (S : ResolvedForestOccurrenceInversionSupply M) (T : ResolvedRegionTagValueSupply Fmem V)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (R : ResolvedRemnantComponentSupply D G)
    (houter : (resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf
      (T.recoveredPreimageValue z) = z.1.1)
    (hForest : (T.Closure.Assembly.Region.forestRecovered z).elements
      = (M.forestRecoveredMulti Fstar z).elements)
    (hround : ∀ (γ : {x : {y : ResolvedFeynmanSubgraph G //
        y ∈ (T.recoveredPreimageValue z).1.1.elements} // x ∈
        ResolvedCoassocSplitChoice.forestComponents (T.recoveredPreimageValue z)})
      (δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) //
        x ∈ forestDomain z}),
      (ResolvedCoassocSplitChoice.forestComponentOccurrence (T.recoveredPreimageValue z) γ).γ.1 = M.parent z δ →
      HEq (ResolvedCoassocSplitChoice.forestComponentOccurrence (T.recoveredPreimageValue z) γ).B (M.innerIdx z δ) →
      HEq (R.remnantComponent (T.recoveredPreimageValue z)
        (ResolvedCoassocSplitChoice.forestComponentOccurrence (T.recoveredPreimageValue z) γ)) δ.1) :
    HEq (R.remnantForest (T.recoveredPreimageValue z)).elements (forestDomain z) := by
  refine heq_finset_of_mem_iff houter (fun x₁ x₂ hx => ?_)
  constructor
  · intro hx₁
    rw [ResolvedRemnantComponentSupply.remnantForest_elements] at hx₁
    obtain ⟨γ, -, hγ⟩ := Finset.mem_image.mp hx₁
    have hfr : γ.1.1 ∈ (M.forestRecoveredMulti Fstar z).elements := by
      rw [← hForest]; exact (T.mem_forestComponents_iff z γ.1).mp γ.2
    have hp : M.parent z (M.forestSource Fstar z ⟨γ.1.1, hfr⟩) = γ.1.1 :=
      M.forestSource_spec Fstar z ⟨γ.1.1, hfr⟩
    have hi : HEq (ResolvedCoassocSplitChoice.forestComponentOccurrence (T.recoveredPreimageValue z) γ).B
        (M.innerIdx z (M.forestSource Fstar z ⟨γ.1.1, hfr⟩)) :=
      (M.innerIdx_occurrence S z (M.forestSource Fstar z ⟨γ.1.1, hfr⟩) (T.recoveredPreimageValue z)
        (ResolvedCoassocSplitChoice.forestComponentOccurrence (T.recoveredPreimageValue z) γ) hp).symm
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
    have hmemU : M.parent z ⟨x₂, hx₂⟩ ∈ (T.Closure.unionOuterValue z).1.elements :=
      (T.Closure.mem_unionOuterValue_iff z _).mpr (Or.inr (Or.inr hfrec))
    have hfc : (⟨M.parent z ⟨x₂, hx₂⟩, hmemU⟩ :
        {y : ResolvedFeynmanSubgraph G // y ∈ (T.recoveredPreimageValue z).1.1.elements})
        ∈ ResolvedCoassocSplitChoice.forestComponents (T.recoveredPreimageValue z) :=
      (T.mem_forestComponents_iff z ⟨M.parent z ⟨x₂, hx₂⟩, hmemU⟩).mpr hfrec
    set γ : {x : {y : ResolvedFeynmanSubgraph G // y ∈ (T.recoveredPreimageValue z).1.1.elements} //
        x ∈ ResolvedCoassocSplitChoice.forestComponents (T.recoveredPreimageValue z)} :=
      ⟨⟨M.parent z ⟨x₂, hx₂⟩, hmemU⟩, hfc⟩ with hγdef
    have hi : HEq (ResolvedCoassocSplitChoice.forestComponentOccurrence (T.recoveredPreimageValue z) γ).B
        (M.innerIdx z ⟨x₂, hx₂⟩) :=
      (M.innerIdx_occurrence S z ⟨x₂, hx₂⟩ (T.recoveredPreimageValue z)
        (ResolvedCoassocSplitChoice.forestComponentOccurrence (T.recoveredPreimageValue z) γ) rfl).symm
    have hheq := hround γ ⟨x₂, hx₂⟩ rfl hi
    have hx₁eq : x₁ = R.remnantComponent (T.recoveredPreimageValue z)
        (ResolvedCoassocSplitChoice.forestComponentOccurrence (T.recoveredPreimageValue z) γ) :=
      eq_of_heq (hx.trans hheq.symm)
    rw [hx₁eq, ResolvedRemnantComponentSupply.remnantForest_elements]
    exact Finset.mem_image.mpr ⟨γ, Finset.mem_attach _ _, rfl⟩

end ResolvedMultiStarDecontractionSupply

end GaugeGeometry.QFT.Combinatorial
