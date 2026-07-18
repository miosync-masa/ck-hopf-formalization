import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocInnerRawCarrierClosure
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocMultiStarForestBridge

/-!
# R-6c-body-381 — bank-3b: the parent/remnant section on the raw value layer, split to three data (PROVED)

Three-hundred-and-eighty-first genuine-body step — the last de-contraction coherence, `parent (remnantComponent o) =
o.γ.1` (body-370's honest datum), lowered to the RAW value core and REDUCED to a subgraph extensionality on three data.
`M.parent = Core.parent` is `rfl`, so the carrier lift is a field-by-field pass-through; the geometric content is
exactly the three projections.

* `ResolvedParentRemnantSectionValueSupply Core Fmem V` — the raw datum `parent_remnantComponent_raw`;
* `ResolvedMultiStarDecontractionValueCoreSupply.toParentRemnantSection` — raw datum ⟶ body-370's `parent_remnantComponent`
  gate (over the carrier-lifted `M`), `rfl` pass-through;
* `parent_remnantComponent_of_data` — the parent equality from `vertices` / `internalEdges` / `externalLegs`
  (`ResolvedFeynmanSubgraph.ext`).

## Three-projection audit (targets, NO premature verdict)

* **vertices** — the touched collection inside the forward-selected outer vs the occurrence `B`'s promotion.
* **internalEdges** — the quotient edge-preimage section.
* **externalLegs** — the coherence that `Core.legLift` picks the occurrence parent's legs.

Which of these are mechanical (forward construction) and which are an honest choice-coherence is a verdict to be
recorded only AFTER each projection is discharged — NOT assumed here.

Landed axiom-clean: `ResolvedParentRemnantSectionValueSupply`, `toParentRemnantSection`,
`parent_remnantComponent_of_data`.

Per the HALT: only the raw interface + the converter + the three-projection reduction are done; the cycle guards are
observed — body-341's `houter`, body-343's `OccInv`, the forest bridge / body-370, and `forestSource` are NOT used; only
the raw `fwdMapFilteredValue` / occurrence / `remnantComponent` / `Core.parent` are read.  No facade, no flat term, no
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

/-- **R-6c-body-381 — the raw parent/remnant section datum** over a value core. -/
structure ResolvedParentRemnantSectionValueSupply
    (Core : ResolvedMultiStarDecontractionValueCoreSupply D)
    (Fmem : ResolvedSelectedOuterFilteredMemSupply D) (V : ResolvedConcreteSummandValueSupply D) where
  /-- The de-contracted parent of a remnant component is the occurrence's source outer (raw). -/
  parent_remnantComponent_raw : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (o : ResolvedCoassocSplitChoice.ForestChoiceOccurrence q.1)
    (δ : {x // x ∈ forestDomain (fwdMapFilteredValue Fmem V q)})
    (_hδ : HEq (V.Remnant.remnant.remnantComponent q.1 o) δ.1),
    Core.parent (fwdMapFilteredValue Fmem V q) δ = o.γ.1

/-- **R-6c-body-381 — the parent equality from three data** (`ResolvedFeynmanSubgraph.ext`). -/
theorem parent_remnantComponent_of_data (Core : ResolvedMultiStarDecontractionValueCoreSupply D)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) // x ∈ forestDomain z})
    (A : ResolvedFeynmanSubgraph G)
    (hv : (Core.parent z δ).vertices = A.vertices)
    (hi : (Core.parent z δ).internalEdges = A.internalEdges)
    (hl : (Core.parent z δ).externalLegs = A.externalLegs) :
    Core.parent z δ = A :=
  ResolvedFeynmanSubgraph.ext hv hi hl

/-- **R-6c-body-381 — raw parent/remnant section ⟶ body-370's `parent_remnantComponent` gate** (over the
carrier-lifted `M`), by `rfl` pass-through. -/
def ResolvedMultiStarDecontractionValueCoreSupply.toParentRemnantSection
    (Core : ResolvedMultiStarDecontractionValueCoreSupply D)
    (Closure : ResolvedMultiStarInnerRawCarrierClosureSupply Core)
    {Fmem : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}
    (ParentRaw : ResolvedParentRemnantSectionValueSupply Core Fmem V) :
    ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
      (o : ResolvedCoassocSplitChoice.ForestChoiceOccurrence q.1)
      (δ : {x // x ∈ forestDomain (fwdMapFilteredValue Fmem V q)}),
      HEq (V.Remnant.remnant.remnantComponent q.1 o) δ.1 →
      (Core.toDecontractionSupply Closure).parent (fwdMapFilteredValue Fmem V q) δ = o.γ.1 :=
  fun {_G} q o δ hδ => ParentRaw.parent_remnantComponent_raw q o δ hδ

end GaugeGeometry.QFT.Combinatorial
