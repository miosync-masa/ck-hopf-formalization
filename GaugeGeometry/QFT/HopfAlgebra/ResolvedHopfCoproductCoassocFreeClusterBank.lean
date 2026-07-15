import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocConcreteSurvivor
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocMeasureLeaves
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocGeometryFloorAssembly

/-!
# R-6c-body-302 — phase-1b free-cluster bank: the survivor supply from the measure leaf (PROVED)

Three-hundred-and-second genuine-body step — the first phase-1b provider assembly.  It banks the (thin) canonical/free
cluster: `carrier_isProperForest` is already proved from the proper-forest index (body-228), and here the concrete
right-survivor supply is built from the measure leaf's `cd_nonempty` alone — no separate survivor model input.  This
reduces `V.Survivor`'s `survivor` field to the measure supply (which `V` already carries), leaving only `survivorInj`
(an injection leaf) and `survivorGen` (rfl) on the survivor transport.

## The survivor `hne` connects to the measure

`resolvedConcreteRightSurvivorSupply` (body-6a) needs a per-component nonemptiness witness `rightComponentNonempty`.
Each right-primitive component `γ` is a component of the carrier forest `s.1.1`, hence connected-divergent
(`s.1.1.isConnectedDivergent`); and the measure leaf's `cd_nonempty` (body-1/34,
`γ.forget.IsConnectedDivergent → γ.vertices.Nonempty`, genuinely NOT derivable from the abstract typeclass) turns that
into `γ.1.1.vertices.Nonempty`.  So the witness is `cd_nonempty ∘ isConnectedDivergent` — no new model input.

## The bank

* `carrier_isProperForest` — BANKED (body-228): `ResolvedCanonicalCarrierProperSupply.toCarrierProperProvider`
  discharges it from the index's `mem_proper` (over `W.toData`).  The index root itself is Group-3 carrier work.
* `V.Survivor.survivor` — BANKED here: `survivorSupply_of_measure` from `V.Measure.cd_nonempty`.
* `V.Survivor.survivorInj` / `survivorGen` — an injection leaf (Group-2) / rfl; not entered here.

Per the HALT: only the survivor-from-measure connection is proved; the carrier index, `survivorInj`, and everything
downstream stay named for later bodies; no concrete `D` is inhabited; no mega-record is built; `carrier_isProperForest`
is NOT duplicated (it is banked at body-228).  No `S` / `Forward` / legacy.  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-302 — the survivor `hne` from the measure leaf.**  A right-primitive component is connected-divergent
(`isConnectedDivergent`), so the measure's `cd_nonempty` gives its vertex-nonemptiness. -/
theorem rightComponentNonempty_of_measure (Measure : ResolvedMeasureLeafSupply D)
    {G : ResolvedFeynmanGraph} (s : ResolvedCoassocSplitChoice D G)
    (γ : {x : {y : ResolvedFeynmanSubgraph G // y ∈ s.1.1.elements} // x ∈ s.rightComponents}) :
    γ.1.1.vertices.Nonempty :=
  Measure.cd_nonempty γ.1.1 (s.1.1.isConnectedDivergent γ.1.1 γ.1.2)

/-- **R-6c-body-302 — the concrete right-survivor supply from the measure leaf.**  No separate survivor model input:
the per-component nonemptiness comes from `V.Measure.cd_nonempty`. -/
noncomputable def survivorSupply_of_measure (Measure : ResolvedMeasureLeafSupply D)
    (G : ResolvedFeynmanGraph) : ResolvedRightSurvivorSupply D G :=
  resolvedConcreteRightSurvivorSupply D G (fun s γ => rightComponentNonempty_of_measure Measure s γ)

end GaugeGeometry.QFT.Combinatorial
