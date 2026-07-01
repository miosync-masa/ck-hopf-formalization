import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSectorForwardTransport
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSectorIndexBridge

/-!
# R-6c-heart-6a-10f-4 — sector forward assembler (local components → forward maps)

Assembles the sector forward maps from the concrete local components (6a-10f-3, the actual
`survivorComponent` / `remnantComponent`), the graph alignment (6a-10f-2), and the membership facts.  So the
quotient-star **forward** direction reduces entirely to:

* `Local` — the survivor / remnant construction data (`hne` / `hcompl` / remnant supply, 6a-10f-3);
* `Align` — the `selectedOuterContractGraph = quotient graph` connector (6a-10f-2);
* `rightLocal_mem` / `forestLocal_mem` — the transported components lie in the right / remnant forest.

Per the HALT, `rightLocal_mem` / `forestLocal_mem` and `quotientGraph_eq` are supply fields (not proved); no
backward maps / inverse laws.

Landed:

* `ResolvedSectorForwardAssemblerSupply C` — `Local` + `Align` + the two membership facts;
* `.toForwardFromLocalComponents` / `.toSectorForwardConcreteSupply` — the assembled forward supply.

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

/-- **R-6c-heart-6a-10f-4 — the sector forward assembler supply.** -/
structure ResolvedSectorForwardAssemblerSupply
    (C : ResolvedCodomainConcreteSupply D G imageOf) where
  /-- The local survivor / remnant components (6a-10f-3). -/
  Local : ResolvedSectorLocalComponentSupply D G
  /-- The graph identification (6a-10f-2). -/
  Align : ResolvedSectorForwardGraphAlignment D G imageOf
  /-- The transported survivor component lies in the right-survivor forest. -/
  rightLocal_mem : ∀ (s : ResolvedCoassocSplitChoice D G) (r : RightPrimitiveIndex D G s),
    transportSubgraphAlongGraphEq (Align.quotientGraph_eq s) (Local.rightLocal s r)
      ∈ (C.rightForest s).elements
  /-- The transported remnant component lies in the remnant forest. -/
  forestLocal_mem : ∀ (s : ResolvedCoassocSplitChoice D G) (f : ForestPrimitiveIndex D G s),
    transportSubgraphAlongGraphEq (Align.quotientGraph_eq s) (Local.forestLocal s f)
      ∈ (C.remnantForest s).elements

/-- **R-6c-heart-6a-10f-4 — into 6a-10f-2's local-component forward supply. -/
noncomputable def ResolvedSectorForwardAssemblerSupply.toForwardFromLocalComponents
    {C : ResolvedCodomainConcreteSupply D G imageOf}
    (A : ResolvedSectorForwardAssemblerSupply C) :
    ResolvedSectorForwardFromLocalComponents C where
  align := A.Align
  rightLocal := fun s => A.Local.rightLocal s
  rightLocal_mem := A.rightLocal_mem
  forestLocal := fun s => A.Local.forestLocal s
  forestLocal_mem := A.forestLocal_mem

/-- **R-6c-heart-6a-10f-4 — the assembled sector forward concrete supply. -/
noncomputable def ResolvedSectorForwardAssemblerSupply.toSectorForwardConcreteSupply
    {C : ResolvedCodomainConcreteSupply D G imageOf}
    (A : ResolvedSectorForwardAssemblerSupply C) : ResolvedSectorForwardConcreteSupply C :=
  A.toForwardFromLocalComponents.toSectorForwardConcreteSupply

end GaugeGeometry.QFT.Combinatorial
