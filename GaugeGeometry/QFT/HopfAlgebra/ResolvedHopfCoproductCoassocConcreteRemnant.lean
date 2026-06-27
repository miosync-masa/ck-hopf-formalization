import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRemnantClassData

/-!
# R-6c-heart-6a-5c-4c — the concrete remnant component via graph re-embedding

The remnant component is the contracted source forest `o.contractedSourceGraph` **re-embedded** as a
subgraph of the quotient graph `selectedOuterContractGraph s` — same intrinsic data, new ambient.  So
`remnantGraph_eq` is `rfl` (the re-embedding keeps the graph), and the remnant route reduces to the three
**support containments** (`vertices ⊆`, `internalEdges ≤`, `externalLegs ≤` of the quotient graph), the
graph's own well-formedness (`edges_supported` / `legs_supported`), and connected-divergence.

Unlike `ResolvedFeynmanSubgraph.reembed` (6a-1, which re-embeds a *subgraph* and inherits its support),
this re-embeds a bare *graph*, so its endpoint-support facts are supplied.

Per the HALT, the support containments and CD are **not** proved — this only constructs the component and
proves `remnantGraph_eq` (= `rfl`).

Landed:

* `ResolvedFeynmanGraph.reembedAsSubgraph` (+ `_toResolvedFeynmanGraph` = `rfl`) — a graph re-embedded as a
  subgraph;
* `ResolvedConcreteRemnantReembedSupply D G s` — the support containments + well-formedness + CD;
* `.remnantComponent` / `.remnantGraph_eq` (= `rfl`) / `.toRemnantClassEqSupply` — the concrete remnant,
  feeding `remnantGen`.

No facade, no flat term, no `forgetHopf`.  The support containments and CD (the genuine de-contraction
data) are the remaining work.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

/-- **R-6c-heart-6a-5c-4c — re-embed a graph as a subgraph.**  Reinterpret a resolved graph `H` as a
subgraph of `K` (same data), given the containments and `H`'s own endpoint support. -/
def ResolvedFeynmanGraph.reembedAsSubgraph (H K : ResolvedFeynmanGraph)
    (hV : H.vertices ⊆ K.vertices) (hE : H.internalEdges ≤ K.internalEdges)
    (hL : H.externalLegs ≤ K.externalLegs)
    (hes : ∀ e ∈ H.internalEdges, e.source ∈ H.vertices ∧ e.target ∈ H.vertices)
    (hls : ∀ ℓ ∈ H.externalLegs, ℓ.attachedTo ∈ H.vertices) : ResolvedFeynmanSubgraph K where
  vertices := H.vertices
  internalEdges := H.internalEdges
  externalLegs := H.externalLegs
  vertices_subset := hV
  internalEdges_le := hE
  externalLegs_le := hL
  edges_supported := hes
  legs_supported := hls

@[simp] theorem ResolvedFeynmanGraph.reembedAsSubgraph_toResolvedFeynmanGraph (H K : ResolvedFeynmanGraph)
    (hV : H.vertices ⊆ K.vertices) (hE : H.internalEdges ≤ K.internalEdges)
    (hL : H.externalLegs ≤ K.externalLegs)
    (hes : ∀ e ∈ H.internalEdges, e.source ∈ H.vertices ∧ e.target ∈ H.vertices)
    (hls : ∀ ℓ ∈ H.externalLegs, ℓ.attachedTo ∈ H.vertices) :
    (H.reembedAsSubgraph K hV hE hL hes hls).toResolvedFeynmanGraph = H := rfl

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-6a-5c-4c — the concrete remnant re-embedding supply.**  For each forest-choice
occurrence, the three support containments of the contracted source forest into the quotient graph, the
graph's endpoint well-formedness, and the re-embedded component's connected-divergence. -/
structure ResolvedConcreteRemnantReembedSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph) (s : ResolvedCoassocSplitChoice D G) where
  /-- The contracted source forest's vertices sit in the quotient graph. -/
  remnant_vertices : ∀ o : s.ForestChoiceOccurrence,
    o.contractedSourceGraph.vertices ⊆ s.selectedOuterContractGraph.vertices
  /-- The contracted source forest's internal edges sit in the quotient graph. -/
  remnant_edges : ∀ o : s.ForestChoiceOccurrence,
    o.contractedSourceGraph.internalEdges ≤ s.selectedOuterContractGraph.internalEdges
  /-- The contracted source forest's external legs sit in the quotient graph. -/
  remnant_legs : ∀ o : s.ForestChoiceOccurrence,
    o.contractedSourceGraph.externalLegs ≤ s.selectedOuterContractGraph.externalLegs
  /-- The contracted source forest's edges are endpoint-supported. -/
  remnant_edges_supported : ∀ o : s.ForestChoiceOccurrence, ∀ e ∈ o.contractedSourceGraph.internalEdges,
    e.source ∈ o.contractedSourceGraph.vertices ∧ e.target ∈ o.contractedSourceGraph.vertices
  /-- The contracted source forest's legs are attachment-supported. -/
  remnant_legs_supported : ∀ o : s.ForestChoiceOccurrence, ∀ ℓ ∈ o.contractedSourceGraph.externalLegs,
    ℓ.attachedTo ∈ o.contractedSourceGraph.vertices
  /-- The re-embedded remnant component is connected-divergent. -/
  remnantCD : ∀ o : s.ForestChoiceOccurrence,
    (o.contractedSourceGraph.reembedAsSubgraph s.selectedOuterContractGraph (remnant_vertices o)
      (remnant_edges o) (remnant_legs o) (remnant_edges_supported o)
      (remnant_legs_supported o)).forget.IsConnectedDivergent

/-- **R-6c-heart-6a-5c-4c — the concrete remnant component.** -/
noncomputable def ResolvedConcreteRemnantReembedSupply.remnantComponent
    {s : ResolvedCoassocSplitChoice D G} (R : ResolvedConcreteRemnantReembedSupply D G s)
    (o : s.ForestChoiceOccurrence) : ResolvedFeynmanSubgraph s.selectedOuterContractGraph :=
  o.contractedSourceGraph.reembedAsSubgraph s.selectedOuterContractGraph (R.remnant_vertices o)
    (R.remnant_edges o) (R.remnant_legs o) (R.remnant_edges_supported o) (R.remnant_legs_supported o)

/-- **R-6c-heart-6a-5c-4c — the remnant component's intrinsic graph is the contracted source forest.**
The re-embedding keeps the graph — `rfl`. -/
theorem ResolvedConcreteRemnantReembedSupply.remnantGraph_eq
    {s : ResolvedCoassocSplitChoice D G} (R : ResolvedConcreteRemnantReembedSupply D G s)
    (o : s.ForestChoiceOccurrence) :
    (R.remnantComponent o).toResolvedFeynmanGraph = o.contractedSourceGraph := rfl

/-- **R-6c-heart-6a-5c-4c — the remnant class-equality supply (hence `remnantGen`).** -/
noncomputable def ResolvedConcreteRemnantReembedSupply.toRemnantClassEqSupply
    {s : ResolvedCoassocSplitChoice D G} (R : ResolvedConcreteRemnantReembedSupply D G s) :
    ResolvedRemnantClassEqSupply D G s where
  remnantComponent := R.remnantComponent
  remnantCD := R.remnantCD
  remnantGraph_eq := R.remnantGraph_eq

end GaugeGeometry.QFT.Combinatorial
