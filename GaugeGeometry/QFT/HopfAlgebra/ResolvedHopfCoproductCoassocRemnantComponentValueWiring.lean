import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocPromotedStarCoherence
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocConcreteRemnant

/-!
# R-6c-body-384 — bank-3b: the abstract/concrete remnant-component wiring pin (PROVED)

Three-hundred-and-eighty-fourth genuine-body step — the ownership pin found by the body-383 audit: the touched-collection
theorem needs `(V.Remnant.remnant.remnantComponent o).vertices = o.contractedSourceGraph.vertices`, but `V.Remnant.remnant`
is an ABSTRACT `ResolvedRemnantComponentSupply` field, so this is NOT free — it is the pointwise `V`-wiring gate,
symmetric to `hSurvivorComponent`, that identifies `V`'s remnant with the concrete contracted-source construction.  It is
isolated here as ONE field (an `rfl` once a concrete `V` is built with that remnant), NOT a full supply equality; then the
three data equalities to `contractedSourceGraph` fall out of the concrete remnant's `reembedAsSubgraph` data (`rfl`) — NO
new geometry.

* `ResolvedRemnantComponentValueWiringSupply V Concrete` — the pointwise gate `remnantComponent_eq`;
* `remnantComponent_{vertices,internalEdges,externalLegs}_eq_contractedSourceGraph` — the three data equalities.

Landed axiom-clean: the structure + the three data theorems.

Per the HALT: only the wiring pin + the three data equalities are done; NO new geometry; the concrete touched theorem
(over `Concrete.remnantComponent`) is body-385 and the abstract adapter (via this wiring) is body-386; the abstract `V`
and the concrete provider are NOT identified for free.  Record `hSurvivorComponent` / `hRemnantComponent` symmetrically in
the residual.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
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

/-- **R-6c-body-384 — the abstract/concrete remnant-component wiring gate** (pointwise, symmetric to
`hSurvivorComponent`). -/
structure ResolvedRemnantComponentValueWiringSupply (V : ResolvedConcreteSummandValueSupply D)
    (Concrete : ∀ {G : ResolvedFeynmanGraph} (s : ResolvedCoassocSplitChoice D G),
      ResolvedConcreteRemnantReembedSupply D G s) where
  /-- `V`'s abstract remnant component is the concrete contracted-source re-embedding. -/
  remnantComponent_eq : ∀ {G : ResolvedFeynmanGraph} (s : ResolvedCoassocSplitChoice D G)
    (o : s.ForestChoiceOccurrence),
    V.Remnant.remnant.remnantComponent s o = (Concrete s).remnantComponent o

namespace ResolvedRemnantComponentValueWiringSupply

variable {V : ResolvedConcreteSummandValueSupply D}
  {Concrete : ∀ {G : ResolvedFeynmanGraph} (s : ResolvedCoassocSplitChoice D G),
    ResolvedConcreteRemnantReembedSupply D G s}
  {G : ResolvedFeynmanGraph}

/-- **R-6c-body-384 — the remnant component's vertices are the contracted source graph's** (`rfl` after wiring). -/
theorem remnantComponent_vertices_eq_contractedSourceGraph
    (Wiring : ResolvedRemnantComponentValueWiringSupply V Concrete)
    (s : ResolvedCoassocSplitChoice D G) (o : s.ForestChoiceOccurrence) :
    (V.Remnant.remnant.remnantComponent s o).vertices = o.contractedSourceGraph.vertices := by
  rw [Wiring.remnantComponent_eq s o]; rfl

/-- **R-6c-body-384 — the remnant component's internal edges are the contracted source graph's.** -/
theorem remnantComponent_internalEdges_eq_contractedSourceGraph
    (Wiring : ResolvedRemnantComponentValueWiringSupply V Concrete)
    (s : ResolvedCoassocSplitChoice D G) (o : s.ForestChoiceOccurrence) :
    (V.Remnant.remnant.remnantComponent s o).internalEdges = o.contractedSourceGraph.internalEdges := by
  rw [Wiring.remnantComponent_eq s o]; rfl

/-- **R-6c-body-384 — the remnant component's external legs are the contracted source graph's.** -/
theorem remnantComponent_externalLegs_eq_contractedSourceGraph
    (Wiring : ResolvedRemnantComponentValueWiringSupply V Concrete)
    (s : ResolvedCoassocSplitChoice D G) (o : s.ForestChoiceOccurrence) :
    (V.Remnant.remnant.remnantComponent s o).externalLegs = o.contractedSourceGraph.externalLegs := by
  rw [Wiring.remnantComponent_eq s o]; rfl

end ResolvedRemnantComponentValueWiringSupply

end GaugeGeometry.QFT.Combinatorial
