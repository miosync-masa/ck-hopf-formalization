import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocContractTwiceShared

/-!
# R-6c-heart-6a-5a — the contract-twice star-geometry coordinate table (common entry)

Both `right_eq` (whole input outer `A`) and the remnant `remnantClass_eq` (per forest choice `B`) are a
**contract-twice = contract-once** class equality between a *one-stage* graph (contract once) and a
*two-stage* graph (contract `A'`, then the inner forest).  This file fixes the shared coordinate table:
a single **per-graph-pair** datum `ResolvedContractTwiceClassData G₁ G₂` carrying the **star permutation**
`σ` matching the one-stage stars to the two-stage stars (as the three graph-field equalities `G₁ = G₂.map
Perm σ`), from which the class equality follows by the shared engine (6a-4c).

So `ResolvedContractTwiceClassData` is the **common entry point**: the right-`eq` side
(`branchRightGraph` / `imageInnerRightGraph`) and the remnant side (`remnantComponent` /
`contractedSourceGraph`) are both instances, and each one's class equality is just `.classEq`.

Per the HALT, the three field equalities are **not proved** here — this only fixes the type-level
coordinate table so the last geometry obligation (`σ` + the field equalities) is a single named shape.

Landed:

* `oneStageContractGraph` / `twoStageContractGraph` — the right-`eq` one/two-stage graphs (abbrevs);
* `ResolvedContractTwiceClassData G₁ G₂` — the star permutation + three field equalities for one graph
  pair, with `.classEq` (via the shared engine);
* `contract_class_eq_of_classData` / `remnantClass_eq_of_classData` — the right-`eq` and remnant class
  equalities, each from a `ResolvedContractTwiceClassData`.

No facade, no flat term, no `forgetHopf`.  The star permutation and the field equalities (the genuine
de-contraction star geometry) are the remaining work — now a single shape across both sides.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-6a-5a — the one-stage contract graph** (input outer `A` contracted once). -/
noncomputable abbrev oneStageContractGraph (s : ResolvedCoassocSplitChoice D G) : ResolvedFeynmanGraph :=
  branchRightGraph s

/-- **R-6c-heart-6a-5a — the two-stage contract graph** (selected outer contracted, then quotient). -/
noncomputable abbrev twoStageContractGraph
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G)
    (s : ResolvedCoassocSplitChoice D G) : ResolvedFeynmanGraph :=
  imageInnerRightGraph imageOf s

/-- **R-6c-heart-6a-5a — the contract-twice star-geometry datum for one graph pair.**  The star
permutation `σ` matching `G₁` (one-stage) to `G₂` (two-stage), as the three graph-field equalities `G₁ =
G₂.mapPerm σ`.  The single shape shared by `right_eq` and the remnant class equality. -/
structure ResolvedContractTwiceClassData (G₁ G₂ : ResolvedFeynmanGraph) where
  /-- The star permutation relabeling the two-stage graph to the one-stage graph. -/
  starPerm : Equiv.Perm VertexId
  /-- One-stage vertices = relabeled two-stage vertices. -/
  vertices_eq : G₁.vertices = (G₂.mapPerm starPerm).vertices
  /-- One-stage internal edges = relabeled two-stage internal edges. -/
  internalEdges_eq : G₁.internalEdges = (G₂.mapPerm starPerm).internalEdges
  /-- One-stage external legs = relabeled two-stage external legs. -/
  externalLegs_eq : G₁.externalLegs = (G₂.mapPerm starPerm).externalLegs

/-- **R-6c-heart-6a-5a — the class equality from the star-geometry datum.**  Via the shared engine
`toResolvedClass_eq_of_mapPerm_fields`. -/
theorem ResolvedContractTwiceClassData.classEq {G₁ G₂ : ResolvedFeynmanGraph}
    (C : ResolvedContractTwiceClassData G₁ G₂) : G₁.toResolvedClass = G₂.toResolvedClass :=
  ResolvedFeynmanGraph.toResolvedClass_eq_of_mapPerm_fields C.starPerm
    C.vertices_eq C.internalEdges_eq C.externalLegs_eq

/-- **R-6c-heart-6a-5a — `right_eq`'s class equality from the star-geometry datum.** -/
theorem contract_class_eq_of_classData
    {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}
    {s : ResolvedCoassocSplitChoice D G}
    (C : ResolvedContractTwiceClassData (oneStageContractGraph s) (twoStageContractGraph imageOf s)) :
    (branchRightGraph s).toResolvedClass = (imageInnerRightGraph imageOf s).toResolvedClass :=
  C.classEq

/-- **R-6c-heart-6a-5a — the remnant class equality from the per-occurrence star-geometry data.**  The
same datum, at the per-forest-choice granularity (`remnantComponent` vs `contractedSourceGraph`). -/
theorem remnantClass_eq_of_classData {s : ResolvedCoassocSplitChoice D G}
    (remnantComponent : s.ForestChoiceOccurrence → ResolvedFeynmanSubgraph s.selectedOuterContractGraph)
    (C : ∀ o, ResolvedContractTwiceClassData (remnantComponent o).toResolvedFeynmanGraph
      o.contractedSourceGraph)
    (o : s.ForestChoiceOccurrence) :
    (remnantComponent o).toResolvedFeynmanGraph.toResolvedClass
      = o.contractedSourceGraph.toResolvedClass :=
  (C o).classEq

end GaugeGeometry.QFT.Combinatorial
