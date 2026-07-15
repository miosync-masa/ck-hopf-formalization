import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecoveredPreimageValueMem
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocConcreteRemnant

/-!
# R-6c-body-294 — the remnant membership bridge reduced to two z-local directions (PROVED)

Two-hundred-and-ninety-fourth genuine-body step — the value-root re-key of the total-root remnant image correspondence
(bodies 207/216/222), the mirror of the survivor reduction (body-293).  It reduces body-290/291's `remnant_mem_value`
leaf to TWO honest z-LOCAL directions (`remnant_sound_value`, `remnant_complete_value` — the `inr` ⟷ star-touching
correspondence, with the de-contraction geometry folded inside the two `HEq`-directions), proving everything else by the
image structure + `Finset.mem_image`.

## Anti-circularity (same as survivor)

The reduction goes `remnantForest (recoveredPreimageValue z) ⟷ forestDomain z` DIRECTLY, via `remnantForest_elements`
(rfl) + `forestDomain` / `Finset.mem_filter` — all z-local.  It NEVER uses body-278's forest bridge (which would
presuppose `fwd (recoveredPreimageValue z) = z`), and NEVER uses `forestTag_agrees` (body-288, forward-image only) —
the remnant generation reads `(recoveredPreimageValue z)`'s OWN forest components / `recoverChoiceValue`.

## The two z-local directions

The `remnantComponent` re-embed is `rfl`-level (`remnantGraph_eq`), but its intrinsic graph is the de-contracted
`o.contractedSourceGraph`, so the two `HEq`-directions genuinely carry the de-contraction — heavier than survivor's
near-definitional `HEq`, but still exactly two directions (no separate de-contraction compatibility leaf at this layer).

Per the HALT: `remnant_mem_value` is reduced to `remnant_sound_value` + `remnant_complete_value`; the image structure +
`mem_image` + `eq_of_heq` are proved; no body-278, no `forestTag_agrees`, no `fwd q = z`.  No `S` / `Forward` / legacy in
any declaration type.  No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData}

set_option linter.unusedSectionVars false

/-- **R-6c-body-294 — the remnant image correspondence supply** (value root).  Body-283's data + the two z-local
remnant directions (the `inr` ⟷ star-touching correspondence). -/
structure ResolvedRemnantImageCorrespondenceValueSupply
    (F : ResolvedSelectedOuterFilteredMemSupply D) (V : ResolvedConcreteSummandValueSupply D) where
  /-- The membership supply (body-283). -/
  Data : ResolvedRecoveredPreimageValueMemSupply F V
  /-- Sound: a recovered `remnantComponent` image (`HEq`-linked to `x₂`) forces `x₂` star-touching. -/
  remnant_sound_value : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (γ : {y // y ∈ ResolvedCoassocSplitChoice.forestComponents (Data.Tags.recoveredPreimageValue z)})
    (x₂ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))),
    HEq (V.Remnant.remnant.remnantComponent (Data.Tags.recoveredPreimageValue z)
        (ResolvedCoassocSplitChoice.forestComponentOccurrence
          (Data.Tags.recoveredPreimageValue z) γ)) x₂ →
    (x₂ ∈ z.2.1.elements ∧ ¬ Disjoint x₂.vertices (starOfZ z))
  /-- Complete: every star-touching `x₂` has a recovered `remnantComponent` preimage (`HEq`-linked). -/
  remnant_complete_value : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (x₂ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))),
    (x₂ ∈ z.2.1.elements ∧ ¬ Disjoint x₂.vertices (starOfZ z)) →
    ∃ γ : {y // y ∈ ResolvedCoassocSplitChoice.forestComponents (Data.Tags.recoveredPreimageValue z)},
      HEq (V.Remnant.remnant.remnantComponent (Data.Tags.recoveredPreimageValue z)
        (ResolvedCoassocSplitChoice.forestComponentOccurrence
          (Data.Tags.recoveredPreimageValue z) γ)) x₂

namespace ResolvedRemnantImageCorrespondenceValueSupply

variable {F : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}

/-- **R-6c-body-294 — the remnant image correspondence from the two directions** (body-222 shape, value root). -/
theorem remnant_image_correspondence_value (R : ResolvedRemnantImageCorrespondenceValueSupply F V)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (x₁ : ResolvedFeynmanSubgraph (ResolvedCoassocSplitChoice.selectedOuterContractGraph
        (R.Data.Tags.recoveredPreimageValue z)))
    (x₂ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
    (hxx : HEq x₁ x₂) :
    (x₁ ∈ (ResolvedCoassocSplitChoice.forestComponents
          (R.Data.Tags.recoveredPreimageValue z)).attach.image
          (fun γ => V.Remnant.remnant.remnantComponent (R.Data.Tags.recoveredPreimageValue z)
            (ResolvedCoassocSplitChoice.forestComponentOccurrence
              (R.Data.Tags.recoveredPreimageValue z) γ))
      ↔ x₂ ∈ z.2.1.elements ∧ ¬ Disjoint x₂.vertices (starOfZ z)) := by
  constructor
  · intro h
    obtain ⟨γ, _, rfl⟩ := Finset.mem_image.mp h
    exact R.remnant_sound_value z γ x₂ hxx
  · intro hand
    obtain ⟨γ, hγlink⟩ := R.remnant_complete_value z x₂ hand
    have heq : V.Remnant.remnant.remnantComponent (R.Data.Tags.recoveredPreimageValue z)
        (ResolvedCoassocSplitChoice.forestComponentOccurrence
          (R.Data.Tags.recoveredPreimageValue z) γ) = x₁ :=
      eq_of_heq (hγlink.trans hxx.symm)
    exact heq ▸ Finset.mem_image.mpr ⟨γ, Finset.mem_attach _ _, rfl⟩

/-- **R-6c-body-294 — body-290/291's `remnant_mem_value` from the correspondence** (body-216 shape, value root). -/
theorem remnant_mem_value (R : ResolvedRemnantImageCorrespondenceValueSupply F V)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (x₁ : ResolvedFeynmanSubgraph (ResolvedCoassocSplitChoice.selectedOuterContractGraph
        (R.Data.Tags.recoveredPreimageValue z)))
    (x₂ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
    (h : HEq x₁ x₂) :
    (x₁ ∈ (V.Remnant.remnant.remnantForest (R.Data.Tags.recoveredPreimageValue z)).elements
      ↔ x₂ ∈ forestDomain z) := by
  simp only [ResolvedRemnantComponentSupply.remnantForest_elements, forestDomain, Finset.mem_filter]
  exact R.remnant_image_correspondence_value z x₁ x₂ h

end ResolvedRemnantImageCorrespondenceValueSupply

end GaugeGeometry.QFT.Combinatorial
