import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocConcreteRemnant
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRemnantSupport

/-!
# R-6c-heart-6a-5c-4e — remnant support-lite supply (self-support auto-filled)

The two `reembedAsSubgraph` self-support obligations are now proved theorems (6a-5c-4d), so the concrete
remnant supply (6a-5c-4c) can take a **thinner** input: just the three genuine de-contraction containments
(`vertices ⊆` / `internalEdges ≤` / `externalLegs ≤` of the quotient graph) plus connected-divergence.

This file is the wrapper: `ResolvedConcreteRemnantReembedLiteSupply` carries only those four, and the
adapter `.toReembedSupply` slots in `remnant_contractedSource_internalEdges_supported` /
`..._externalLegs_supported` automatically, recovering the full `ResolvedConcreteRemnantReembedSupply`.

Per the HALT, the three containments and `remnantCD` are **not** proved — only the self-support is auto.

Landed:

* `ResolvedConcreteRemnantReembedLiteSupply D G s` — the three containments + `remnantCD` (the genuine
  de-contraction data, nothing else);
* `.toReembedSupply` — auto-fill the proved self-support → `ResolvedConcreteRemnantReembedSupply`;
* `.toRemnantClassEqSupply` / `.toRemnantDecontractionSupply` — straight through to `remnantGen`.

No facade, no flat term, no `forgetHopf`.  The three de-contraction containments and `remnantCD` are the
remnant side's only remaining obligations.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-6a-5c-4e — the support-lite remnant supply.**  Only the three de-contraction
containments and connected-divergence; the `reembedAsSubgraph` self-support is supplied automatically by
the 6a-5c-4d theorems. -/
structure ResolvedConcreteRemnantReembedLiteSupply (D : ResolvedCoproductProperForestData)
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
  /-- The re-embedded remnant component is connected-divergent. -/
  remnantCD : ∀ o : s.ForestChoiceOccurrence,
    (o.contractedSourceGraph.reembedAsSubgraph s.selectedOuterContractGraph (remnant_vertices o)
      (remnant_edges o) (remnant_legs o) (remnant_contractedSource_internalEdges_supported o)
      (remnant_contractedSource_externalLegs_supported o)).forget.IsConnectedDivergent

/-- **R-6c-heart-6a-5c-4e — recover the full reembed supply.**  The self-support is the proved
6a-5c-4d theorems; the three containments and CD pass through. -/
def ResolvedConcreteRemnantReembedLiteSupply.toReembedSupply
    {s : ResolvedCoassocSplitChoice D G} (L : ResolvedConcreteRemnantReembedLiteSupply D G s) :
    ResolvedConcreteRemnantReembedSupply D G s where
  remnant_vertices := L.remnant_vertices
  remnant_edges := L.remnant_edges
  remnant_legs := L.remnant_legs
  remnant_edges_supported := fun o => remnant_contractedSource_internalEdges_supported o
  remnant_legs_supported := fun o => remnant_contractedSource_externalLegs_supported o
  remnantCD := L.remnantCD

/-- **R-6c-heart-6a-5c-4e — the remnant class-equality supply (hence `remnantGen`).** -/
noncomputable def ResolvedConcreteRemnantReembedLiteSupply.toRemnantClassEqSupply
    {s : ResolvedCoassocSplitChoice D G} (L : ResolvedConcreteRemnantReembedLiteSupply D G s) :
    ResolvedRemnantClassEqSupply D G s :=
  L.toReembedSupply.toRemnantClassEqSupply

/-- **R-6c-heart-6a-5c-4e — into the de-contraction supply (`remnantGen`, 6a-4b).** -/
noncomputable def ResolvedConcreteRemnantReembedLiteSupply.toRemnantDecontractionSupply
    {s : ResolvedCoassocSplitChoice D G} (L : ResolvedConcreteRemnantReembedLiteSupply D G s) :
    ResolvedRemnantDecontractionSupply D G s :=
  L.toRemnantClassEqSupply.toRemnantDecontractionSupply

end GaugeGeometry.QFT.Combinatorial
