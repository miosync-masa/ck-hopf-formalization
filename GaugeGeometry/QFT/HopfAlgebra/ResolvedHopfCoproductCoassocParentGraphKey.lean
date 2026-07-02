import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocParentInjectivityBody

/-!
# R-6c-body-20 — parent-graph injectivity: scout + factoring through an id-bearing key

Twentieth genuine-body step, a SCOUT of body-19's residual `parent_graph_inj` (contracted-source-graph
equality ⇒ parent intrinsic graph equality) with an honest re-scope.

## Scout finding: `contractWithStars` is LOSSY, so the RAW graph does not recover the parent

For `o : s.ForestChoiceOccurrence`, writing `γG := o.γ.1.toResolvedFeynmanGraph` and `B := o.B.1 :
ResolvedAdmissibleSubgraph γG`, the contracted source graph `B.contractWithStars (D.starOf γG B)` is
(`ResolvedAdmissibleSubgraph.contractWithStars`, all `rfl`):

```text
vertices      = (γG.vertices \ B.vertices) ∪ B.starVertices starOf
internalEdges = (γG.internalEdges - B.internalEdges).map (B.retargetEdge starOf)   -- complement edges only
externalLegs  = γG.externalLegs.map (B.retargetExternalLeg starOf)
```

So the contraction **discards** `B.vertices` (replaced by fresh stars), **discards** `B.internalEdges` (only
the complement `γG.internalEdges - B.internalEdges` survives), and **collapses** any complement-edge / leg
endpoint lying inside a `B`-component to that component's star (`retargetVertex = starOf` there).  Hence the
raw `γG` is genuinely NOT recoverable from `contractedSourceGraph` alone — two parents differing only inside
`B` (extra fully-contracted internal vertices/edges) yield the same contracted graph.  `parent_graph_inj` is
therefore **not a pure-graph consequence**; it is TRUE only via the id-bearing data the contraction preserves.

## What IS preserved: the id-bearing legs/edges (the recovery key)

`retargetEdge` / `retargetExternalLeg` are **identity-preserving** (`edgeId` / `legId` kept; only endpoints /
`attachedTo` move).  So the contracted graph's `externalLegs` are exactly `γG.externalLegs` with ids intact —
and since the forest components of `s` are DISJOINT id-bearing subgraphs of `G`, the surviving leg/edge ids
trace back to the unique parent component.  This is the real content, and it is intrinsically an id-level
(not raw-graph) fact.

## Re-scope: factor `parent_graph_inj` through a graph-level KEY

We isolate the recovery as a graph-level function `parentKey : ResolvedFeynmanGraph → K` (the caller picks the
id-bearing key — e.g. the leg-id multiset) together with `parentKey_inj` (the key determines the parent's
intrinsic graph).  Then `parent_graph_inj` is `congrArg parentKey` composed with `parentKey_inj` — the key
being a function of the graph makes contracted-graph equality give key equality for free.  This records the
correct dependency: the recovery flows through the preserved ids, not the lossy raw graph.

Per the HALT, `parentKey_inj` is NOT proved (the genuine id-traceability, fielded); nothing is forced and no
facade is introduced; `retarget` / support-9 untouched.

Landed:

* `ForestChoiceOccurrence.contractedSourceGraph_externalLegs` / `_internalEdges` / `_vertices` — the `rfl`
  unfoldings pinning exactly what the contraction preserves (id-bearing legs/edges) vs discards (`B.vertices`,
  `B.internalEdges`);
* `ResolvedParentKeyRecoverySupply D G s K` — `parentKey` + `parentKey_inj`;
* `.toParentGraphInjectivitySupply` — body-19's supply via `congrArg parentKey`.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

section Unfoldings

variable {s : ResolvedCoassocSplitChoice D G}

/-- **R-6c-body-20 — the contracted source graph keeps the parent's external legs (ids intact, endpoints
retargeted).**  The id-bearing data the recovery relies on. -/
theorem ResolvedCoassocSplitChoice.ForestChoiceOccurrence.contractedSourceGraph_externalLegs
    (o : s.ForestChoiceOccurrence) :
    o.contractedSourceGraph.externalLegs =
      o.γ.1.toResolvedFeynmanGraph.externalLegs.map
        (o.B.1.retargetExternalLeg (D.starOf o.γ.1.toResolvedFeynmanGraph o.B.1)) := rfl

/-- **R-6c-body-20 — the contracted source graph keeps only the COMPLEMENT edges (the parent's `B`-internal
edges are discarded).**  Witnesses the loss on the edge side. -/
theorem ResolvedCoassocSplitChoice.ForestChoiceOccurrence.contractedSourceGraph_internalEdges
    (o : s.ForestChoiceOccurrence) :
    o.contractedSourceGraph.internalEdges =
      o.B.1.complementEdges.map
        (o.B.1.retargetEdge (D.starOf o.γ.1.toResolvedFeynmanGraph o.B.1)) := rfl

/-- **R-6c-body-20 — the contracted source graph's vertices: surviving parent vertices plus fresh stars (the
`B`-internal vertices are discarded).**  Witnesses the loss on the vertex side. -/
theorem ResolvedCoassocSplitChoice.ForestChoiceOccurrence.contractedSourceGraph_vertices
    (o : s.ForestChoiceOccurrence) :
    o.contractedSourceGraph.vertices =
      (o.γ.1.toResolvedFeynmanGraph.vertices \ o.B.1.vertices) ∪
        o.B.1.starVertices (D.starOf o.γ.1.toResolvedFeynmanGraph o.B.1) := rfl

end Unfoldings

/-- **R-6c-body-20 — the parent-key recovery supply.**  The recovery of the parent's intrinsic graph from the
contracted source graph, factored through a graph-level id-bearing key `parentKey` (the caller supplies the
key and its parent-determining property; the RAW graph is insufficient — see the scout finding). -/
structure ResolvedParentKeyRecoverySupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph) (s : ResolvedCoassocSplitChoice D G) (K : Type*) where
  /-- The id-bearing key extracted from a bare graph (the contraction-preserved data). -/
  parentKey : ResolvedFeynmanGraph → K
  /-- The key of the contracted source graph determines the parent's intrinsic graph. -/
  parentKey_inj : ∀ o₁ o₂ : s.ForestChoiceOccurrence,
    parentKey o₁.contractedSourceGraph = parentKey o₂.contractedSourceGraph →
    o₁.γ.1.toResolvedFeynmanGraph = o₂.γ.1.toResolvedFeynmanGraph

/-- **R-6c-body-20 — body-19's parent-graph-injectivity supply from the parent-key recovery.**  `parentKey`
is a function of the graph, so contracted-graph equality gives key equality by `congrArg`. -/
def ResolvedParentKeyRecoverySupply.toParentGraphInjectivitySupply
    {s : ResolvedCoassocSplitChoice D G} {K : Type*}
    (P : ResolvedParentKeyRecoverySupply D G s K) :
    ResolvedParentGraphInjectivitySupply D G s where
  parent_graph_inj := fun o₁ o₂ h => P.parentKey_inj o₁ o₂ (congrArg P.parentKey h)

end GaugeGeometry.QFT.Combinatorial
