import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSurvivorRoundTrip
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSurvivorElementsRecovery

/-!
# R-6c-body-347 — survivor collection: `HEq (rightSurvivorForest recovered).elements (rightDomain z)` (PROVED)

Three-hundred-and-forty-seventh genuine-body step — stage 3, the survivor collection HEq: the right exit of
culprit B is now fully sealed.  Body-206's generic `heq_finset_of_mem_iff` reduces the collection HEq to a
membership bridge, which the survivor round-trip (body-346) and the tag partition (body-345) close in both
directions with NO forced `eq_of_heq` at the component level — the HEq is consumed inside the membership
predicate, aligned by body-341's `houter`.

## The two directions (bookkeeping over bodies 345/346)

* **Forward** — `x₁ ∈ survivorForest` gives a right component `γ` (image); body-345 lands `γ.1.1 ∈ rightRecovered`;
  `hRight` recovers `δ ∈ rightDomain` with `γ.1.1 = rightReembed δ`; body-346 gives `HEq x₁ δ`; with the bridge's
  `HEq x₁ x₂` this forces `x₂ = δ ∈ rightDomain`.
* **Backward** — `x₂ ∈ rightDomain` gives `δ`; `rightReembed δ ∈ rightRecovered` (image); body-345 (mpr) lands it
  in `rightComponents`; its survivor image is in `survivorForest`; body-346 gives `HEq (survivorComponent …) x₂`;
  with `HEq x₁ x₂` this forces `x₁` to be that image.

Landed axiom-clean: `rightSurvivorForest_elements_heq`.

Per the HALT: only the collection HEq is proved; `hRight` (`rightRecovered = rightReembed`-image, an rfl for the
concrete multi-star `T`) is a wiring HYPOTHESIS; `V` is not wired, the six bridge gates / carrier membership /
remnant geometry are NOT used.  Culprit B's RIGHT half is sealed; the remnant (left half) is next.  No facade,
no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
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

/-- **R-6c-body-347 — the survivor collection HEq.**  The right half of the forward-quotient element bridge:
the recovered right-survivor forest's components are heterogeneously the codomain's star-avoiding survivors. -/
theorem rightSurvivorForest_elements_heq (Measure : ResolvedMeasureLeafSupply D)
    (T : ResolvedRegionTagValueSupply Fmem V) {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (houter : (resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf
      (T.recoveredPreimageValue z) = z.1.1)
    (hRight : (T.Closure.Assembly.Region.rightRecovered z).elements
      = (rightDomain z).attach.image (rightReembed z)) :
    HEq ((survivorSupply_of_measure Measure G).rightSurvivorForest
        (T.recoveredPreimageValue z)).elements (rightDomain z) := by
  refine heq_finset_of_mem_iff houter (fun x₁ x₂ hx => ?_)
  constructor
  · intro hx₁
    rw [ResolvedRightSurvivorSupply.rightSurvivorForest_elements] at hx₁
    obtain ⟨γa, -, hγa⟩ := Finset.mem_image.mp hx₁
    have hrr : γa.1.1 ∈ (T.Closure.Assembly.Region.rightRecovered z).elements :=
      (T.mem_rightComponents_iff z γa.1).mp γa.2
    rw [hRight] at hrr
    obtain ⟨δa, -, hδa⟩ := Finset.mem_image.mp hrr
    have hheq := T.rightSurvivor_roundtrip Measure z houter δa γa hδa.symm
    rw [hγa] at hheq
    have hx₂eq : x₂ = δa.1 := eq_of_heq (hx.symm.trans hheq)
    rw [hx₂eq]; exact δa.2
  · intro hx₂
    have hrr : rightReembed z ⟨x₂, hx₂⟩ ∈ (T.Closure.Assembly.Region.rightRecovered z).elements := by
      rw [hRight]; exact Finset.mem_image.mpr ⟨⟨x₂, hx₂⟩, Finset.mem_attach _ _, rfl⟩
    have hmemU : rightReembed z ⟨x₂, hx₂⟩ ∈ (T.Closure.unionOuterValue z).1.elements :=
      (T.Closure.mem_unionOuterValue_iff z _).mpr (Or.inr (Or.inl hrr))
    have hright : (⟨rightReembed z ⟨x₂, hx₂⟩, hmemU⟩ :
        {x : ResolvedFeynmanSubgraph G // x ∈ (T.recoveredPreimageValue z).1.1.elements})
        ∈ ResolvedCoassocSplitChoice.rightComponents (T.recoveredPreimageValue z) :=
      (T.mem_rightComponents_iff z ⟨rightReembed z ⟨x₂, hx₂⟩, hmemU⟩).mpr hrr
    have hheq := T.rightSurvivor_roundtrip Measure z houter ⟨x₂, hx₂⟩
      ⟨⟨rightReembed z ⟨x₂, hx₂⟩, hmemU⟩, hright⟩ rfl
    have hx₁eq : x₁ = (survivorSupply_of_measure Measure G).survivorComponent
        (T.recoveredPreimageValue z) ⟨⟨rightReembed z ⟨x₂, hx₂⟩, hmemU⟩, hright⟩ :=
      eq_of_heq (hx.trans hheq.symm)
    rw [hx₁eq, ResolvedRightSurvivorSupply.rightSurvivorForest_elements]
    exact Finset.mem_image.mpr ⟨⟨⟨rightReembed z ⟨x₂, hx₂⟩, hmemU⟩, hright⟩,
      Finset.mem_attach _ _, rfl⟩

end ResolvedRegionTagValueSupply

end GaugeGeometry.QFT.Combinatorial
