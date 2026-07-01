import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCodomainConcrete

/-!
# R-6c-heart-6a-10f-1 — concrete sector forward maps (component + membership)

The right / forest sector forward maps are made concrete-shaped here: each is a **quotient-graph component**
plus its **membership** in the right-survivor / remnant forest.  So `rightToComponent` / `forestToComponent`
become `⟨component, mem⟩`, splitting each forward map into

* the component function `rightForward` / `forestForward` (which the 5b-2 `survivorComponent` /
  6a-5c-4c `remnantComponent` fill — modulo the graph identification `s.selectedOuterContractGraph =
  resolvedCoassocQuotientGraph (imageOf s)`);
* the membership `rightForward_mem` / `forestForward_mem` (the component lies in the right / remnant forest).

Per the HALT, `componentToRight` / `componentToForest` and the inverse laws are NOT built; the component
functions and membership are supply fields (the genuine `survivorComponent` / `remnantComponent` link is the
next step).

Landed:

* `ResolvedSectorForwardConcreteSupply C` — the forward component functions + membership;
* `.rightToComponent` / `.forestToComponent` — the concrete `⟨component, mem⟩` forward maps.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}
  {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}

/-- **R-6c-heart-6a-10f-1 — the sector forward component functions + membership.** -/
structure ResolvedSectorForwardConcreteSupply
    (C : ResolvedCodomainConcreteSupply D G imageOf) where
  /-- A right-primitive ↦ its quotient-graph survivor component. -/
  rightForward : ∀ s : ResolvedCoassocSplitChoice D G,
    RightPrimitiveIndex D G s → ResolvedFeynmanSubgraph (resolvedCoassocQuotientGraph (imageOf s))
  /-- ... which lies in the right-survivor forest. -/
  rightForward_mem : ∀ (s : ResolvedCoassocSplitChoice D G) (i : RightPrimitiveIndex D G s),
    rightForward s i ∈ (C.rightForest s).elements
  /-- A forest-choice ↦ its quotient-graph remnant component. -/
  forestForward : ∀ s : ResolvedCoassocSplitChoice D G,
    ForestPrimitiveIndex D G s → ResolvedFeynmanSubgraph (resolvedCoassocQuotientGraph (imageOf s))
  /-- ... which lies in the remnant forest. -/
  forestForward_mem : ∀ (s : ResolvedCoassocSplitChoice D G) (i : ForestPrimitiveIndex D G s),
    forestForward s i ∈ (C.remnantForest s).elements

/-- **R-6c-heart-6a-10f-1 — the concrete right forward map. -/
def ResolvedSectorForwardConcreteSupply.rightToComponent
    {C : ResolvedCodomainConcreteSupply D G imageOf}
    (M : ResolvedSectorForwardConcreteSupply C) (s : ResolvedCoassocSplitChoice D G) :
    RightPrimitiveIndex D G s → {δ // δ ∈ (C.rightForest s).elements} :=
  fun i => ⟨M.rightForward s i, M.rightForward_mem s i⟩

/-- **R-6c-heart-6a-10f-1 — the concrete forest forward map. -/
def ResolvedSectorForwardConcreteSupply.forestToComponent
    {C : ResolvedCodomainConcreteSupply D G imageOf}
    (M : ResolvedSectorForwardConcreteSupply C) (s : ResolvedCoassocSplitChoice D G) :
    ForestPrimitiveIndex D G s → {δ // δ ∈ (C.remnantForest s).elements} :=
  fun i => ⟨M.forestForward s i, M.forestForward_mem s i⟩

end GaugeGeometry.QFT.Combinatorial
