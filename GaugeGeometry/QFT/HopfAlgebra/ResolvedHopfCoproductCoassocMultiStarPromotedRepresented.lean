import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocMultiStarForestBridge
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocInnerRawM3
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRepresentedByTouched
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocPromotedOf
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestOccurrenceInversion

/-!
# R-6c-body-371 — Front-3 bank-2: the multi-star LEFT load-bearing theorem `promoted_mem_representedByTouched` (PROVED)

Three-hundred-and-seventy-first genuine-body step — the load-bearing theorem of the multi-star LEFT bridge.  The LEFT
sector is NOT a plain right/forest complement: `representedByTouched` is not parent-equality but membership in the
components a parent ABSORBED.  This body banks the one theorem the whole left bridge turns on — a promoted component of
`q`'s split choice is `representedByTouched` at the forward image — routing through the SAME occurrence machinery as the
forest bridge:

```text
γ ∈ q.promotedElements  →  ∃ η (choiceAt η = inr Bη), γ ∈ (promote η Bη).elements   (biUnion + promotedComponentElements_inr)
o := forestComponentOccurrence η ;  δ := remnantComponent o ∈ forestDomain (fwd q)   (body-274)
M.parent (fwd q) δ = o.γ.1 = η        (parent_remnantComponent) ;  M.innerIdx δ ≍ o.B (OccInv, body-343)
(promote (M.parent δ) (M.innerIdx δ)).elements = touchedOuterComponents (fwd q) δ    (M3, body-328)
⇒ γ ∈ touchedOuterComponents (fwd q) δ  ⇒  representedByTouched (fwd q) γ
```

The dependent transport `promote η Bη ↦ promote (M.parent δ) (M.innerIdx δ)` (parent equality + heterogeneous index)
is isolated as `promote_elements_congr` (subst + `eq_of_heq`).

Landed axiom-clean: `promote_elements_congr`, `promoted_mem_representedByTouched`.

Per the HALT: only the LEFT load-bearing theorem is banked; the full left sound/complete + the left bridge supply are
the next step; inputs are exactly `parent_remnantComponent` (body-370 datum) + `OccInv` + body-274 + M3; the right
bridge is NOT needed; no `T` / cover / carrier.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO
`promote_collapse` / singleton / floor-297 (M3 REPLACES the singleton).
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

/-- **R-6c-body-371 — the promote-elements dependent transport.**  Parent equality + heterogeneous forest index give
equal promoted-component sets. -/
theorem promote_elements_congr {G : ResolvedFeynmanGraph} {A₁ A₂ : ResolvedFeynmanSubgraph G}
    (h : A₁ = A₂) (B₁ : (D.supply A₁.toResolvedFeynmanGraph).ForestIdx)
    (B₂ : (D.supply A₂.toResolvedFeynmanGraph).ForestIdx) (hB : HEq B₁ B₂) :
    (ResolvedAdmissibleSubgraph.promote A₁ B₁.1).elements
      = (ResolvedAdmissibleSubgraph.promote A₂ B₂.1).elements := by
  subst h
  rw [eq_of_heq hB]

namespace ResolvedMultiStarDecontractionSupply

variable (M : ResolvedMultiStarDecontractionSupply D)
  {Fmem : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}

/-- **R-6c-body-371 — the LEFT load-bearing theorem.**  A promoted component of `q`'s split choice is
`representedByTouched` at the forward image. -/
theorem promoted_mem_representedByTouched (OccInv : ResolvedForestOccurrenceInversionSupply M)
    (P : ResolvedValueQuotientRegionSplitSupply Fmem V)
    (parent_remnantComponent : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
      (o : ResolvedCoassocSplitChoice.ForestChoiceOccurrence q.1)
      (δ : {x // x ∈ forestDomain (fwdMapFilteredValue Fmem V q)}),
      HEq (V.Remnant.remnant.remnantComponent q.1 o) δ.1 →
      M.parent (fwdMapFilteredValue Fmem V q) δ = o.γ.1)
    {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (γc : ResolvedFeynmanSubgraph G) (hmem : γc ∈ ResolvedCoassocSplitChoice.promotedElements q.1) :
    representedByTouched (fwdMapFilteredValue Fmem V q) γc := by
  obtain ⟨η, hη⟩ := ResolvedCoassocSplitChoice.mem_promotedElements hmem
  rcases hc : ResolvedCoassocSplitChoice.choiceAt q.1 η with b | Bη
  · rw [ResolvedCoassocSplitChoice.promotedComponentElements, hc] at hη
    exact absurd hη (by simp)
  · rw [ResolvedCoassocSplitChoice.promotedComponentElements_inr q.1 hc] at hη
    have hfc : η ∈ ResolvedCoassocSplitChoice.forestComponents q.1 :=
      Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, ⟨Bη, hc⟩⟩
    set o := ResolvedCoassocSplitChoice.forestComponentOccurrence q.1 ⟨η, hfc⟩ with ho
    have hoB : o.B = Bη := Sum.inr.inj (o.hchoice.symm.trans hc)
    have hδmem : V.Remnant.remnant.remnantComponent q.1 o
        ∈ (V.Remnant.remnant.remnantForest q.1).elements :=
      Finset.mem_image.mpr ⟨⟨η, hfc⟩, Finset.mem_attach _ _, rfl⟩
    set δ : {x // x ∈ forestDomain (fwdMapFilteredValue Fmem V q)} :=
      ⟨V.Remnant.remnant.remnantComponent q.1 o, (P.forestDomain_value_mem q _).mpr hδmem⟩ with hδ
    have hp : M.parent (fwdMapFilteredValue Fmem V q) δ = o.γ.1 :=
      parent_remnantComponent q o δ HEq.rfl
    have hi : HEq (M.innerIdx (fwdMapFilteredValue Fmem V q) δ) o.B :=
      M.innerIdx_occurrence OccInv (fwdMapFilteredValue Fmem V q) δ q.1 o hp
    refine ⟨δ.1, δ.2, ?_⟩
    rw [← promote_innerRaw_elements (fwdMapFilteredValue Fmem V q) δ.1
      (M.legLift (fwdMapFilteredValue Fmem V q) δ) (M.hE (fwdMapFilteredValue Fmem V q)) (M.hL (fwdMapFilteredValue Fmem V q))]
    show γc ∈ (ResolvedAdmissibleSubgraph.promote (M.parent (fwdMapFilteredValue Fmem V q) δ)
      (M.innerIdx (fwdMapFilteredValue Fmem V q) δ).1).elements
    rw [promote_elements_congr hp (M.innerIdx (fwdMapFilteredValue Fmem V q) δ) o.B hi, hoB]
    exact hη

end ResolvedMultiStarDecontractionSupply

end GaugeGeometry.QFT.Combinatorial
