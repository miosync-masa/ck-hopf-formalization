import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocOccurrenceInjectivityBody

/-!
# R-6c-body-19 — parent injectivity reduced to parent-GRAPH injectivity

Nineteenth genuine-body step, cutting the de-contraction-uniqueness kernel `parent_inj` (body-7) down to its
genuine core.  `parent_inj` asks that contracted-source-graph equality forces the parent COMPONENTS equal
(`o₁.γ = o₂.γ`, an equality of `{x : ResolvedFeynmanSubgraph G // x ∈ s.1.1.elements}`).

Because a resolved subgraph is determined by its intrinsic graph (`ResolvedFeynmanSubgraph.ext`: the three data
fields `vertices` / `internalEdges` / `externalLegs`, the support Props being proof-irrelevant), the subtype
equality `o₁.γ = o₂.γ` follows from just the intrinsic-GRAPH equality `o₁.γ.1.toResolvedFeynmanGraph =
o₂.γ.1.toResolvedFeynmanGraph` — the true kernel being "the contracted source graph determines the parent's
intrinsic graph" (the resolved de-contraction uniqueness).

This isolates that kernel as `parent_graph_inj`; the adapter is the same id-bearing `ext` + `Subtype.ext`
pattern as leaf-8 (`product_survivorInj_of_concreteSurvivor`).

Per the HALT, `parent_graph_inj` is NOT proved (the genuine de-contraction geometry, fielded); `retarget` /
support-9 untouched.

Landed:

* `ResolvedParentGraphInjectivitySupply D G s` — `parent_graph_inj` (contracted-graph eq ⇒ parent intrinsic
  graph eq);
* `.toOccurrenceParentInjectivitySupply` — the body-7 `parent_inj` supply (via `ResolvedFeynmanSubgraph.ext`
  on the three `congrArg` projections + `Subtype.ext`).

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-body-19 — the parent-graph-injectivity supply.**  Contracted-source-graph equality recovers the
parent component's INTRINSIC GRAPH — the genuine resolved de-contraction uniqueness kernel. -/
structure ResolvedParentGraphInjectivitySupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph) (s : ResolvedCoassocSplitChoice D G) where
  /-- Contracted-source-graph equality forces the parents' intrinsic graphs equal. -/
  parent_graph_inj : ∀ o₁ o₂ : s.ForestChoiceOccurrence,
    o₁.contractedSourceGraph = o₂.contractedSourceGraph →
    o₁.γ.1.toResolvedFeynmanGraph = o₂.γ.1.toResolvedFeynmanGraph

/-- **R-6c-body-19 — the body-7 parent-injectivity supply from parent-graph injectivity.**  A resolved
subgraph is determined by its intrinsic graph, so the intrinsic-graph equality upgrades to the subtype
equality `o₁.γ = o₂.γ`. -/
def ResolvedParentGraphInjectivitySupply.toOccurrenceParentInjectivitySupply
    {s : ResolvedCoassocSplitChoice D G}
    (P : ResolvedParentGraphInjectivitySupply D G s) :
    ResolvedOccurrenceParentInjectivitySupply D G s where
  parent_inj := fun o₁ o₂ hcg => by
    have hG := P.parent_graph_inj o₁ o₂ hcg
    apply Subtype.ext
    exact ResolvedFeynmanSubgraph.ext
      (congrArg (·.vertices) hG) (congrArg (·.internalEdges) hG) (congrArg (·.externalLegs) hG)

end GaugeGeometry.QFT.Combinatorial
