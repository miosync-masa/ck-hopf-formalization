import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestRegionSectorBridge
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocValueQuotientRegionSplit

/-!
# R-6c-body-305 — forest bridge construction audit: the occurrence root (PROVED)

Three-hundred-and-fifth genuine-body step — a construction-first audit of the value forest bridge (body-278
`forest_sound_value` / `forest_complete_value`).  The verdict: there is a single concrete de-contraction root — the
`ForestChoiceOccurrence` — from which BOTH `Region.componentToForest` AND `V.Remnant.remnant.remnantComponent` are built
with parent agreement FORCED by `V.Remnant`'s existing `remnantInj`; NO new coherence leaf is needed, only a concrete
DEFINITION of `componentToForest` as the parent-inverse of `remnantComponent`.  The `forestChoiceSelected`-from-occurrence
half (SOUND core) is banked here.

## The occurrence root (Verdict B)

`ForestChoiceOccurrence q = ⟨γ, B, hchoice : choiceAt q γ = inr B⟩` (Remnant.lean:50-56) carries all three quantities the
bridge needs:
* `o.γ.1 ∈ q.1.1.elements` — the parent in the DOMAIN outer (what `componentToForest` must return, what
  `forestChoiceSelected` requires);
* `o.B` + `o.hchoice` — gives `forestChoiceSelected` directly (`∃ B`) — the SOUND core, banked below;
* `o.contractedSourceGraph.reembedAsSubgraph …` = `remnantComponent o` — the quotient component `δ`.

The region-side and V-side maps are ALREADY the same on this root: `ResolvedSectorLocalComponentSupply.forestLocal s f
:= (L.remnant s).remnantComponent f.toOccurrence` (SectorIndexBridge.lean:82-85), and `remnantForest.elements` is
definitionally the occurrence image (Remnant.lean:101-105, rfl).

## No exact `B` (lighter than `forestTag_agrees`)

SOUND is immediate from `o.hchoice` (`∃ B`); COMPLETE from `V.Remnant.remnantInj` (RemnantTransport.lean:103-106,
occurrence-parent uniqueness).  Neither recovers the exact `B` — strictly lighter than body-295's `forestTag_agrees`
(which needs the exact `inr B` value).  Confirmed by body-276's docstring (ForestRegionValueBridge.lean:19-21).

## body-224 mismatch resolved at the value root

`(fwdMapFilteredValue F V q).1.1 = selectedOuterRawOf q.1` (rfl, ConcreteSummandValue.lean:108-113), and the occurrence
parent lives in `q.1.1.1.elements` (domain outer) by construction — matching `forestChoiceSelected q.1`'s requirement,
NEVER routing through `fwd q`'s outer where body-224's `selectedOuterOf q` mismatch arose.  Resolved.

## The generic-`z` construction target (for body-306)

`componentToForest` is a Region-core FIELD over generic `z` (used in `forestRecovered z` / `representedInQuotient` at
generic `z` in the round-trip), so the concrete construction must define it for all `z` (the de-contraction
δ ↦ source parent), agreeing with the `V.Remnant` occurrence parents at `z = fwd q` via body-274's
`forestDomain_value_mem` (`forestDomain (fwd q) ↔ V.Remnant.remnant.remnantForest q.1`) + `remnantInj`.  That concrete
`componentToForest` def is the body-306 target; then `forest_sound_value` discharges from `forestChoiceSelected_of_occurrence`
(below) and `forest_complete_value` from `remnantInj`.

Per the HALT: only the SOUND core (`forestChoiceSelected` from an occurrence) is proved; the concrete `componentToForest`
def and the two bridge directions are the body-306 target; no exact `B`; no LEFT bridge, no `forestTag_agrees`, no whole
round-trip.  No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

set_option linter.unusedSectionVars false

/-- **R-6c-body-305 — the SOUND core: a forest-choice occurrence's parent is forest-choice-selected.**  Directly from
the occurrence's own choice witness `hchoice` — no exact `B` recovery, no de-contraction. -/
theorem forestChoiceSelected_of_occurrence (q : ResolvedCoassocSplitChoice D G)
    (o : ResolvedCoassocSplitChoice.ForestChoiceOccurrence q) :
    forestChoiceSelected q o.γ.1 :=
  ⟨o.γ.2, o.B, o.hchoice⟩

end GaugeGeometry.QFT.Combinatorial
