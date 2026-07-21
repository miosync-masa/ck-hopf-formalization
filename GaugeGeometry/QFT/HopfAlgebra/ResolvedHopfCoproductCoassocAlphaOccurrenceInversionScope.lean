import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestOccurrenceInversionValue
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaCorrectedTouched
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocInnerRawM3

/-!
# R-6c-body-502 — OccRaw scope audit + faithful alpha occurrence-inversion socket (PROVED)

Five-hundred-and-second genuine-body step — an X-ray of `OccRaw`'s over-quantification BEFORE any blind inhabitation.  The
reduced coassoc root's `OccRaw` field is the legacy `ResolvedForestOccurrenceInversionValueSupply`, whose sole field
`occurrence_inner_elements_raw` quantifies over **every** split choice `s` and occurrence `o` under only `hparent :
Core.parent z δ = o.γ.1`.  The actual alpha consumer only ever reads the ONE forward-filtered split `q`, so this legacy
socket is strictly stronger than what is used.

## The over-strength, formally (Step 1)

`occRaw_forces_B_elements_eq` — for a FIXED `z, δ`, two split choices `s₁/o₁`, `s₂/o₂` sharing the same de-contracted
parent are forced to have equal chosen-block element sets `HEq o₁.B.1.elements o₂.B.1.elements`.  This cross-split
coherence is never needed by the consumer (which fixes `s = q.1`); it is the excess the faithful socket drops.  The legacy
`OccRaw` stays a valid conditional — it is NOT the canonical target.

## The faithful socket (Step 2)

`ResolvedForwardForestOccurrenceInversionAlphaValueSupply M Fmem V` — the occurrence inversion restricted to the forward
filtered choice `q` (no lift to arbitrary `s`): the exact-B `HEq (M.innerIdx (fwd q) δ) o.B` under `hparent`.

## The geometric core, canonically (Step 3, safe-stop)

`promoted_innerIdx_elements_eq_promoted_B_alpha` — over the canonical alpha `V` (body-482's `VBuild`), given the corrected
remnant occurrence witness `hδ`, promoting the de-contracted inner forest recovers exactly the promoted chosen block:

```text
(promote (M.parent (fwd q) δ) (M.innerIdx (fwd q) δ).1).elements = (promote o.γ.1 o.B.1).elements
```

This is M3 (`promote_innerRaw_elements`, body-328) composed with body-484's `touchedOuterComponents_of_corrected_occurrence_
alpha` — the touched collection is BOTH the promoted inner forest (M3) and the promoted chosen block (body-484).  Per the
plan's safe-stop, the `promote_injective` image cancellation, the `hparent → hδ` derivation (forestDomain membership +
`eq_of_parent_eq`), the final `ForestIdx` `HEq` lift, and the canonical socket inhabitation are the body-503 continuation.

Per the HALT/guards: nothing is back-computed from body-495 `remnant_mem` / body-492 forward-quotient HEq / coassoc; the
legacy `OccRaw`'s `∀ s` universal is NOT fabricated canonically; body-489's corrected-remnant round-trip is NOT used to
prove `hidx` (it takes `hidx` as input — circular); the body-495 closed theorem is NOT edited; `quot_eq` / `legComplete`
are NOT entered; strict `StarProm` / `InnerStarRaw` stay ZERO; NO unconditional-coassoc claim.  No facade, no flat term, no
`forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
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

/-! ## Step 1 — the legacy `OccRaw` over-strength, formally -/

/-- **R-6c-body-502 ∎ — the legacy `OccRaw` forces cross-split block agreement.**  For a fixed `z, δ`, ANY two split
choices with the same de-contracted parent have equal chosen-block element sets — a coherence the forward-filtered
consumer never needs.  This exhibits the legacy socket's over-quantification. -/
theorem occRaw_forces_B_elements_eq
    {Core : ResolvedMultiStarDecontractionValueCoreSupply D}
    (OccRaw : ResolvedForestOccurrenceInversionValueSupply Core)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) // x ∈ forestDomain z})
    {s₁ : ResolvedCoassocSplitChoice D G} (o₁ : s₁.ForestChoiceOccurrence) (hp₁ : Core.parent z δ = o₁.γ.1)
    {s₂ : ResolvedCoassocSplitChoice D G} (o₂ : s₂.ForestChoiceOccurrence) (hp₂ : Core.parent z δ = o₂.γ.1) :
    HEq o₁.B.1.elements o₂.B.1.elements :=
  (OccRaw.occurrence_inner_elements_raw z δ s₁ o₁ hp₁).symm.trans
    (OccRaw.occurrence_inner_elements_raw z δ s₂ o₂ hp₂)

/-! ## Step 2 — the faithful forward-filtered alpha socket -/

/-- **R-6c-body-502 — the faithful forward occurrence-inversion socket.**  Restricted to the forward filtered choice `q`
(no `∀ s` lift): the exact-`B` inversion at the alpha value.  This is the properly-scoped replacement for the legacy
`OccRaw`. -/
structure ResolvedForwardForestOccurrenceInversionAlphaValueSupply
    (M : ResolvedMultiStarDecontractionSupply D)
    (Fmem : ResolvedSelectedOuterFilteredMemSupply D)
    (V : ResolvedFilteredConcreteSummandValueSupply D) where
  /-- De-contracting `δ`'s touched components at the forward choice `q` recovers exactly `q`'s chosen block `o.B`. -/
  occurrence_inner_idx_alpha : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (δ : {x : ResolvedFeynmanSubgraph
        ((fwdMapFilteredAlphaValue Fmem V q).1.1.contractWithStars
          (D.starOf G (fwdMapFilteredAlphaValue Fmem V q).1.1)) //
      x ∈ forestDomain (fwdMapFilteredAlphaValue Fmem V q)})
    (o : ResolvedCoassocSplitChoice.ForestChoiceOccurrence q.1)
    (_hparent : M.parent (fwdMapFilteredAlphaValue Fmem V q) δ = o.γ.1),
    HEq (M.innerIdx (fwdMapFilteredAlphaValue Fmem V q) δ) o.B

/-! ## Step 3 (safe-stop) — the promoted-collection geometric core, canonically -/

/-- **R-6c-body-502 ∎ — the canonical promoted-collection identity.**  Over the canonical alpha `V`, given the corrected
remnant occurrence witness `hδ`, the promoted de-contracted inner forest equals the promoted chosen block (as element
sets): M3 (the touched collection is the promoted inner forest) composed with body-484 (the touched collection is the
promoted chosen block).  The `promote_injective` cancellation and the `ForestIdx` `HEq` lift are body-503. -/
theorem promoted_innerIdx_elements_eq_promoted_B_alpha
    {Fmem : ResolvedSelectedOuterFilteredMemSupply canonicalUniqueSupportedCarrierProperSupply.toData}
    (M : ResolvedMultiStarDecontractionSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    (VBuild : ResolvedCanonicalUniqueAlphaFilteredValueConstructionSupply)
    {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalUniqueSupportedCarrierProperSupply.toData G)
    (o : ResolvedCoassocSplitChoice.ForestChoiceOccurrence q.1)
    (δ : {x : ResolvedFeynmanSubgraph
        ((fwdMapFilteredAlphaValue Fmem VBuild.toCanonicalFilteredValue q).1.1.contractWithStars
          (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G
            (fwdMapFilteredAlphaValue Fmem VBuild.toCanonicalFilteredValue q).1.1)) //
      x ∈ forestDomain (fwdMapFilteredAlphaValue Fmem VBuild.toCanonicalFilteredValue q)})
    (hδ : HEq (VBuild.toCanonicalFilteredValue.Remnant.remnant.remnantComponent q.1 o) δ.1) :
    (ResolvedAdmissibleSubgraph.promote
        (M.parent (fwdMapFilteredAlphaValue Fmem VBuild.toCanonicalFilteredValue q) δ)
        (M.innerIdx (fwdMapFilteredAlphaValue Fmem VBuild.toCanonicalFilteredValue q) δ).1).elements
      = (ResolvedAdmissibleSubgraph.promote o.γ.1 o.B.1).elements :=
  (promote_innerRaw_elements (fwdMapFilteredAlphaValue Fmem VBuild.toCanonicalFilteredValue q) δ.1
    (M.legLift (fwdMapFilteredAlphaValue Fmem VBuild.toCanonicalFilteredValue q) δ)
    (M.hE (fwdMapFilteredAlphaValue Fmem VBuild.toCanonicalFilteredValue q))
    (M.hL (fwdMapFilteredAlphaValue Fmem VBuild.toCanonicalFilteredValue q))).trans
    (touchedOuterComponents_of_corrected_occurrence_alpha VBuild q o δ hδ)

end GaugeGeometry.QFT.Combinatorial
