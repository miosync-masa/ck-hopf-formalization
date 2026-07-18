import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocInnerRawCarrierClosure
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestOccurrenceInversion

/-!
# R-6c-body-380 — bank-3b: occurrence inversion lowered to the raw value layer (PROVED)

Three-hundred-and-eightieth genuine-body step — the occurrence-inversion datum, stated on the RAW value core with the
MINIMAL `HEq` (no `ForestIdx` transport).  Body-343's `ResolvedForestOccurrenceInversionSupply.occurrence_inner_elements`
carries the transport `transportForestIdx` inside a homogeneous equality (a post-carrier-lift shape); the mathematics is
just the heterogeneous element equality `HEq (Core.innerRaw z δ).elements o.B.1.elements` — bank-3b value.

* `ResolvedForestOccurrenceInversionValueSupply Core` — the raw `HEq` datum `occurrence_inner_elements_raw`;
* `transportForestIdx_elements_heq` — the transport is `HEq`-the-identity on `.elements` (`subst` + `rfl`);
* `ResolvedMultiStarDecontractionValueCoreSupply.toForestOccurrenceInversionSupply` — value core + carrier closure +
  raw datum ⟶ body-343's supply, via `eq_of_heq` on `raw.trans (transport-heq).symm`.

`hparent` is kept a HYPOTHESIS (not a field) — it does not type the `HEq`, but it pins the datum to the correct parent
reconstruction and is needed by the downstream transport (body-343's `innerIdx_occurrence`).

Landed axiom-clean: `ResolvedForestOccurrenceInversionValueSupply`, `transportForestIdx_elements_heq`,
`toForestOccurrenceInversionSupply`.

Per the HALT: only the raw interface + the transport-`HEq` helper + the converter are done; the raw field carries NO
`innerRaw_mem` / `ForestIdx` / carrier proof; `transportForestIdx` appears ONLY in the converter; `hparent` stays a
hypothesis; this is body-342's HONEST occurrence-inversion datum, NOT derived from M1/M3.  No facade, no flat term, no
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

variable {D : ResolvedCoproductProperForestData}

set_option linter.unusedSectionVars false

/-- **R-6c-body-380 — the transport is `HEq`-the-identity on `.elements`.** -/
theorem transportForestIdx_elements_heq {H₁ H₂ : ResolvedFeynmanGraph} (h : H₁ = H₂)
    (B : (D.supply H₁).ForestIdx) :
    HEq (transportForestIdx h B).1.elements B.1.elements := by
  subst h; rfl

/-- **R-6c-body-380 — the raw occurrence-inversion datum** over a value core (minimal `HEq`, no `ForestIdx`). -/
structure ResolvedForestOccurrenceInversionValueSupply
    (Core : ResolvedMultiStarDecontractionValueCoreSupply D) where
  /-- De-contracting `δ`'s touched components recovers `q`'s chosen sub-forest (raw elements, `HEq`). -/
  occurrence_inner_elements_raw : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) // x ∈ forestDomain z})
    (s : ResolvedCoassocSplitChoice D G) (o : s.ForestChoiceOccurrence)
    (_hparent : Core.parent z δ = o.γ.1),
    HEq (Core.innerRaw z δ).elements o.B.1.elements

/-- **R-6c-body-380 — raw occurrence inversion ⟶ body-343's supply** (over the carrier-lifted `M`). -/
def ResolvedMultiStarDecontractionValueCoreSupply.toForestOccurrenceInversionSupply
    (Core : ResolvedMultiStarDecontractionValueCoreSupply D)
    (Closure : ResolvedMultiStarInnerRawCarrierClosureSupply Core)
    (OccRaw : ResolvedForestOccurrenceInversionValueSupply Core) :
    ResolvedForestOccurrenceInversionSupply (Core.toDecontractionSupply Closure) where
  occurrence_inner_elements := fun {_G} z δ s o hparent =>
    eq_of_heq ((OccRaw.occurrence_inner_elements_raw z δ s o hparent).trans
      (transportForestIdx_elements_heq
        (congrArg ResolvedFeynmanSubgraph.toResolvedFeynmanGraph hparent.symm) o.B).symm)

end GaugeGeometry.QFT.Combinatorial
