import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSectorForwardConcrete

/-!
# R-6c-heart-6a-10f-2 — sector forward graph alignment (local components → quotient components)

The 5b-2 `survivorComponent` / 6a-5c-4c-style remnant components live over `s.selectedOuterContractGraph`,
while the sector forward maps (6a-10f-1) need components over `resolvedCoassocQuotientGraph (imageOf s)`.
These two graphs coincide (when `(imageOf s).selectedOuter.1 = selectedOuterRawOf s`); this file names that
identification as a connector and transports the local components across it.

So the sector forward maps reduce to **local** components in `selectedOuterContractGraph` (exactly where
`survivorComponent` / `remnantComponent` land) plus the graph alignment — the 5b-2/5b-3 machinery now feeds
`rightForward` / `forestForward` directly.

Per the HALT, `quotientGraph_eq` and the membership are supply fields (not proved); no inverse maps.

Landed:

* `ResolvedSectorForwardGraphAlignment D G imageOf` — the `selectedOuterContractGraph = quotient graph`
  connector;
* `transportSubgraphAlongGraphEq` — the generic subgraph transport along a graph equality;
* `ResolvedSectorForwardFromLocalComponents C` — local components + alignment + membership;
* `.toSectorForwardConcreteSupply` — into 6a-10f-1's forward supply.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

/-- **R-6c-heart-6a-10f-2 — transport a resolved subgraph along a graph equality.** -/
def transportSubgraphAlongGraphEq {H K : ResolvedFeynmanGraph} (h : H = K)
    (δ : ResolvedFeynmanSubgraph H) : ResolvedFeynmanSubgraph K := h ▸ δ

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}
  {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}

/-- **R-6c-heart-6a-10f-2 — the graph identification connector.**  The split choice's contract graph equals
the image's quotient graph. -/
structure ResolvedSectorForwardGraphAlignment (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G) where
  /-- `selectedOuterContractGraph s = resolvedCoassocQuotientGraph (imageOf s)`. -/
  quotientGraph_eq : ∀ s : ResolvedCoassocSplitChoice D G,
    s.selectedOuterContractGraph = resolvedCoassocQuotientGraph (imageOf s)

/-- **R-6c-heart-6a-10f-2 — sector forward maps from local components + alignment.**  The local components
live over `selectedOuterContractGraph` (where `survivorComponent` / `remnantComponent` land); the alignment
transports them to the quotient graph. -/
structure ResolvedSectorForwardFromLocalComponents
    (C : ResolvedCodomainConcreteSupply D G imageOf) where
  /-- The graph identification. -/
  align : ResolvedSectorForwardGraphAlignment D G imageOf
  /-- A right-primitive ↦ its survivor component over `selectedOuterContractGraph`. -/
  rightLocal : ∀ s : ResolvedCoassocSplitChoice D G,
    RightPrimitiveIndex D G s → ResolvedFeynmanSubgraph s.selectedOuterContractGraph
  /-- The transported survivor component lies in the right-survivor forest. -/
  rightLocal_mem : ∀ (s : ResolvedCoassocSplitChoice D G) (i : RightPrimitiveIndex D G s),
    transportSubgraphAlongGraphEq (align.quotientGraph_eq s) (rightLocal s i) ∈ (C.rightForest s).elements
  /-- A forest-choice ↦ its remnant component over `selectedOuterContractGraph`. -/
  forestLocal : ∀ s : ResolvedCoassocSplitChoice D G,
    ForestPrimitiveIndex D G s → ResolvedFeynmanSubgraph s.selectedOuterContractGraph
  /-- The transported remnant component lies in the remnant forest. -/
  forestLocal_mem : ∀ (s : ResolvedCoassocSplitChoice D G) (i : ForestPrimitiveIndex D G s),
    transportSubgraphAlongGraphEq (align.quotientGraph_eq s) (forestLocal s i) ∈ (C.remnantForest s).elements

/-- **R-6c-heart-6a-10f-2 — into 6a-10f-1's forward supply. -/
noncomputable def ResolvedSectorForwardFromLocalComponents.toSectorForwardConcreteSupply
    {C : ResolvedCodomainConcreteSupply D G imageOf}
    (S : ResolvedSectorForwardFromLocalComponents C) : ResolvedSectorForwardConcreteSupply C where
  rightForward := fun s i => transportSubgraphAlongGraphEq (S.align.quotientGraph_eq s) (S.rightLocal s i)
  rightForward_mem := S.rightLocal_mem
  forestForward := fun s i => transportSubgraphAlongGraphEq (S.align.quotientGraph_eq s) (S.forestLocal s i)
  forestForward_mem := S.forestLocal_mem

end GaugeGeometry.QFT.Combinatorial
