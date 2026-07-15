import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecoveredPreimageValueMem
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightSurvivor

/-!
# R-6c-body-293 — the survivor membership bridge reduced to two z-local directions (PROVED)

Two-hundred-and-ninety-third genuine-body step — the value-root re-key of the total-root survivor image correspondence
(bodies 205/206/211/221).  It reduces body-290/291's `survivor_mem_value` leaf to TWO honest z-LOCAL directions
(`survivor_sound_value`, `survivor_complete_value` — the pure `inl false` ⟷ star-avoiding bijection), proving everything
else by the image structure + `Finset.mem_image`.

## Anti-circularity

The reduction goes `rightSurvivorForest (recoveredPreimageValue z) ⟷ rightDomain z` DIRECTLY, via
`rightSurvivorForest_elements` (rfl) + `rightDomain` / `Finset.mem_filter` — all z-local.  It NEVER uses body-278's
`rightRecovered_forward_value_membership` (stated only at `z = fwdMapFilteredValue F V q`, which would presuppose the
forward round-trip `fwd (recoveredPreimageValue z) = z` we are still proving).  No `fwdMapFilteredValue`, no
`rightRecovered`/`rightPrimSelected`, no `fwd q = z`.

## The two z-local directions

```text
survivor_sound_value    : HEq (survivorComponent (recovered) γ) x₂ → x₂ ∈ z.2.1.elements ∧ Disjoint x₂.vertices (starOfZ z)
survivor_complete_value : x₂ ∈ z.2.1.elements ∧ Disjoint x₂.vertices (starOfZ z)
                            → ∃ γ ∈ rightComponents (recovered), HEq (survivorComponent (recovered) γ) x₂
```

Per the HALT: `survivor_mem_value` is reduced to these two directions; the image structure + `mem_image` +
`eq_of_heq` are proved; no body-278, no `fwd q = z`; the remnant / other leaves are NOT entered.  No `S` / `Forward` /
legacy in any declaration type.  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-293 — the survivor image correspondence supply** (value root).  Body-283's data + the two z-local
survivor directions (the pure `inl false` ⟷ star-avoiding bijection). -/
structure ResolvedSurvivorImageCorrespondenceValueSupply
    (F : ResolvedSelectedOuterFilteredMemSupply D) (V : ResolvedConcreteSummandValueSupply D) where
  /-- The membership supply (body-283). -/
  Data : ResolvedRecoveredPreimageValueMemSupply F V
  /-- Sound: a recovered `survivorComponent` image (`HEq`-linked to `x₂`) forces `x₂` star-avoiding. -/
  survivor_sound_value : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (γ : {y // y ∈ ResolvedCoassocSplitChoice.rightComponents (Data.Tags.recoveredPreimageValue z)})
    (x₂ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))),
    HEq (V.Survivor.survivor.survivorComponent (Data.Tags.recoveredPreimageValue z) γ) x₂ →
    (x₂ ∈ z.2.1.elements ∧ Disjoint x₂.vertices (starOfZ z))
  /-- Complete: every star-avoiding `x₂` has a recovered `survivorComponent` preimage (`HEq`-linked). -/
  survivor_complete_value : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (x₂ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))),
    (x₂ ∈ z.2.1.elements ∧ Disjoint x₂.vertices (starOfZ z)) →
    ∃ γ : {y // y ∈ ResolvedCoassocSplitChoice.rightComponents (Data.Tags.recoveredPreimageValue z)},
      HEq (V.Survivor.survivor.survivorComponent (Data.Tags.recoveredPreimageValue z) γ) x₂

namespace ResolvedSurvivorImageCorrespondenceValueSupply

variable {F : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}

/-- **R-6c-body-293 — the survivor image correspondence from the two directions** (body-221 shape, value root). -/
theorem survivor_image_correspondence_value (R : ResolvedSurvivorImageCorrespondenceValueSupply F V)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (x₁ : ResolvedFeynmanSubgraph (ResolvedCoassocSplitChoice.selectedOuterContractGraph
        (R.Data.Tags.recoveredPreimageValue z)))
    (x₂ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
    (hxx : HEq x₁ x₂) :
    (x₁ ∈ (ResolvedCoassocSplitChoice.rightComponents
          (R.Data.Tags.recoveredPreimageValue z)).attach.image
          (V.Survivor.survivor.survivorComponent (R.Data.Tags.recoveredPreimageValue z))
      ↔ x₂ ∈ z.2.1.elements ∧ Disjoint x₂.vertices (starOfZ z)) := by
  constructor
  · intro h
    obtain ⟨γ, _, rfl⟩ := Finset.mem_image.mp h
    exact R.survivor_sound_value z γ x₂ hxx
  · intro hand
    obtain ⟨γ, hγlink⟩ := R.survivor_complete_value z x₂ hand
    have heq : V.Survivor.survivor.survivorComponent (R.Data.Tags.recoveredPreimageValue z) γ = x₁ :=
      eq_of_heq (hγlink.trans hxx.symm)
    exact heq ▸ Finset.mem_image.mpr ⟨γ, Finset.mem_attach _ _, rfl⟩

/-- **R-6c-body-293 — body-290/291's `survivor_mem_value` from the correspondence** (body-211 shape, value root). -/
theorem survivor_mem_value (R : ResolvedSurvivorImageCorrespondenceValueSupply F V)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (x₁ : ResolvedFeynmanSubgraph (ResolvedCoassocSplitChoice.selectedOuterContractGraph
        (R.Data.Tags.recoveredPreimageValue z)))
    (x₂ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
    (h : HEq x₁ x₂) :
    (x₁ ∈ (V.Survivor.survivor.rightSurvivorForest (R.Data.Tags.recoveredPreimageValue z)).elements
      ↔ x₂ ∈ rightDomain z) := by
  simp only [ResolvedRightSurvivorSupply.rightSurvivorForest_elements, rightDomain, Finset.mem_filter]
  exact R.survivor_image_correspondence_value z x₁ x₂ h

end ResolvedSurvivorImageCorrespondenceValueSupply

end GaugeGeometry.QFT.Combinatorial
