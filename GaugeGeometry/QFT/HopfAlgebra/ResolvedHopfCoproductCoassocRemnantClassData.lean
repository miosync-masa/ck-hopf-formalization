import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRemnantDecontraction

/-!
# R-6c-heart-6a-5c-4b — the remnant class equality via the intrinsic-graph route

Unlike `right_eq` (a contract-twice = contract-once between two *star-contracted* graphs), the remnant
class equality is between `(remnantComponent o).toResolvedFeynmanGraph` — the **intrinsic graph of a
subgraph**, not a `contractWithStars` — and `o.contractedSourceGraph`.  So the `FinalGeometryData` /
`EdgeLegData` machinery (which needs *both* graphs to be `contractWithStars`) does not fit; the remnant
takes its own, simpler coordinate.

The natural shape: the remnant component is the contracted source forest **re-embedded** (same data), so
the obligation is the **intrinsic graph equality** `(remnantComponent o).toResolvedFeynmanGraph =
o.contractedSourceGraph` — from which the class equality is `congrArg`.  (As with `reembed` / `promote`,
the de-contraction keeps the intrinsic graph; only its ambient changes.)

Per the HALT, `remnantComponent` and `remnantGraph_eq` are **not** constructed/proved — this only fixes
the remnant's route.

Landed:

* `ResolvedFeynmanGraph.toResolvedClass_eq_of_eq` — equal graphs have equal resolved classes (`congrArg`);
* `ResolvedRemnantClassEqSupply D G s` — `remnantComponent` + `remnantCD` + the intrinsic-graph equality
  `remnantGraph_eq`;
* `.remnantClass_eq` / `.toRemnantDecontractionSupply` — derive the class equality (hence `remnantGen`).

So the remnant route is `ResolvedRemnantClassEqSupply → ResolvedRemnantDecontractionSupply → remnantGen`,
separate from the right factor's `FinalGeometryData → right_eq`.

No facade, no flat term, no `forgetHopf`.  Constructing `remnantComponent` and proving `remnantGraph_eq`
(the genuine de-contraction) is the remaining work.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-6a-5c-4b — equal graphs have equal resolved classes.** -/
theorem ResolvedFeynmanGraph.toResolvedClass_eq_of_eq {G₁ G₂ : ResolvedFeynmanGraph} (h : G₁ = G₂) :
    G₁.toResolvedClass = G₂.toResolvedClass :=
  congrArg ResolvedFeynmanGraph.toResolvedClass h

/-- **R-6c-heart-6a-5c-4b — the remnant class-equality supply (intrinsic-graph route).**  The remnant
embedding, its connected-divergence, and the intrinsic-graph equality with the contracted source forest
(the de-contraction keeps the intrinsic graph). -/
structure ResolvedRemnantClassEqSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph) (s : ResolvedCoassocSplitChoice D G) where
  /-- The remnant of a forest choice, embedded into the quotient graph. -/
  remnantComponent : s.ForestChoiceOccurrence → ResolvedFeynmanSubgraph s.selectedOuterContractGraph
  /-- Each remnant component is connected-divergent. -/
  remnantCD : ∀ o, (remnantComponent o).forget.IsConnectedDivergent
  /-- The remnant component's intrinsic graph is the contracted source forest. -/
  remnantGraph_eq : ∀ o,
    (remnantComponent o).toResolvedFeynmanGraph = o.contractedSourceGraph

/-- **R-6c-heart-6a-5c-4b — the remnant class equality from the intrinsic-graph equality.** -/
theorem ResolvedRemnantClassEqSupply.remnantClass_eq
    {s : ResolvedCoassocSplitChoice D G} (R : ResolvedRemnantClassEqSupply D G s)
    (o : s.ForestChoiceOccurrence) :
    (R.remnantComponent o).toResolvedFeynmanGraph.toResolvedClass
      = o.contractedSourceGraph.toResolvedClass :=
  ResolvedFeynmanGraph.toResolvedClass_eq_of_eq (R.remnantGraph_eq o)

/-- **R-6c-heart-6a-5c-4b — into the de-contraction supply.**  Hence `remnantGen` (6a-4b). -/
def ResolvedRemnantClassEqSupply.toRemnantDecontractionSupply
    {s : ResolvedCoassocSplitChoice D G} (R : ResolvedRemnantClassEqSupply D G s) :
    ResolvedRemnantDecontractionSupply D G s where
  remnantComponent := R.remnantComponent
  remnantCD := R.remnantCD
  remnantClass_eq := R.remnantClass_eq

end GaugeGeometry.QFT.Combinatorial
