import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocComponentNonempty
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocInnerCDBody

/-!
# R-6c-body-34 — the measure / power-counting leaf bundle

Thirty-fourth genuine-body step, grouping the two divergence-MEASURE leaves — the ones that are genuine
properties of the power-counting measure, not combinatorial geometry — into a single record, so the final
theorem's assumptions separate cleanly into *geometry* leaves versus *measure* leaves.

The two measure leaves:

* `cd_nonempty` (body-1) — a connected-divergent subgraph has nonempty vertices (needed for
  `component_nonempty` / `contracted_nonempty`);
* `contract_preserves_CD` (body-33) — contracting an admissible subforest of a connected-divergent graph
  yields a connected-divergent graph (the Connes–Kreimer power-counting stability, resolved full-CD form).

Both are quantified over ALL resolved graphs, so the bundle serves every ambient `G`.

Per the HALT, no measure fact is proved; this only groups and adapts.

Landed:

* `ResolvedMeasureLeafSupply D` — `cd_nonempty` + `contract_preserves_CD`;
* `.toConnectedDivergentNonemptySupply` / `.toInnerCDPreservationSupply` — the two body-1 / body-33 supplies;
* `.toInputOuterElementNonemptySupply` / `.toInnerRightCDSupply` — the downstream leaf-11 / leaf-18 supplies.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-body-34 — the measure / power-counting leaf bundle.**  The two genuine divergence-measure facts:
CD-nonemptiness and CK contraction CD-stability. -/
structure ResolvedMeasureLeafSupply (D : ResolvedCoproductProperForestData) where
  /-- A connected-divergent subgraph has nonempty vertices (body-1). -/
  cd_nonempty : ∀ {H : ResolvedFeynmanGraph} (γ : ResolvedFeynmanSubgraph H),
    γ.forget.IsConnectedDivergent → γ.vertices.Nonempty
  /-- Contracting an admissible subforest of a CD graph preserves CD (body-33, CK power-counting stability). -/
  contract_preserves_CD : ∀ (H : ResolvedFeynmanGraph) (A : ResolvedAdmissibleSubgraph H),
    H.forget.toClass.IsConnectedDivergent →
    (A.contractWithStars (D.starOf H A)).forget.IsConnectedDivergent

/-- **R-6c-body-34 — the body-1 CD-nonempty supply at a given graph. -/
def ResolvedMeasureLeafSupply.toConnectedDivergentNonemptySupply
    (M : ResolvedMeasureLeafSupply D) (G : ResolvedFeynmanGraph) :
    ResolvedConnectedDivergentNonemptySupply G where
  cd_nonempty := fun γ h => M.cd_nonempty γ h

/-- **R-6c-body-34 — the body-33 contraction CD-preservation supply. -/
def ResolvedMeasureLeafSupply.toInnerCDPreservationSupply
    (M : ResolvedMeasureLeafSupply D) :
    ResolvedInnerCDPreservationSupply D where
  contract_preserves_CD := M.contract_preserves_CD

/-- **R-6c-body-34 — the leaf-11 input-outer element nonemptiness supply. -/
def ResolvedMeasureLeafSupply.toInputOuterElementNonemptySupply
    (M : ResolvedMeasureLeafSupply D) :
    ResolvedInputOuterElementNonemptySupply D G :=
  (M.toConnectedDivergentNonemptySupply G).toInputOuterElementNonemptySupply

/-- **R-6c-body-34 — the leaf-18 inner-right CD supply. -/
def ResolvedMeasureLeafSupply.toInnerRightCDSupply
    (M : ResolvedMeasureLeafSupply D) :
    ResolvedInnerRightCDSupply D G :=
  M.toInnerCDPreservationSupply.toInnerRightCDSupply

end GaugeGeometry.QFT.Combinatorial
