import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSectorLeafInventory
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSectorForwardAssembler

/-!
# R-6c-leaf-19b — deep sector leaf inventory (Forward split into its construction pieces)

Step 3 of the sector scout (leaf-19 gave the top-level `Forward + Backward + Inverse` split).  The
top-level `Forward` (`ResolvedSectorForwardConcreteSupply`, 4 fields) is itself the image of the DEEPER
`ResolvedSectorForwardAssemblerSupply` (6a-10f-4) under `.toSectorForwardConcreteSupply`, so the Forward
leaf splits further into its genuine construction pieces:

* `Local : ResolvedSectorLocalComponentSupply D G` (6a-10f-3) — the local survivor / remnant components
  (itself `hne` + `hcompl` + `remnant`, `rightLocal := rightSurvivorComponentOf …`, `forestLocal :=
  remnantComponent …`);
* `Align : ResolvedSectorForwardGraphAlignment D G imageOf` (6a-10f-2) — the graph identification
  (`quotientGraph_eq`);
* `rightLocal_mem` / `forestLocal_mem` — the transported components land in the right / remnant forests.

This file records the deep split as one record and reconstructs the assembler.

Per the HALT, no concrete proofs; Perm / Retarget / backward-map bodies untouched.

Landed:

* `ResolvedSectorDeepLeafSupply C` — deep `Forward` (assembler) + `Backward` + `Inverse`;
* `.toAssembler : ResolvedSectorEquivAssemblerSupply C`;
* `.toLeafSupply : ResolvedSectorLeafSupply C` (into the leaf-19 top-level inventory).

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

/-- **R-6c-leaf-19b — the deep sector leaf inventory.**  The `Forward` half is the deeper forward assembler
(Local components + graph alignment + the two membership facts), so its construction pieces are exposed. -/
structure ResolvedSectorDeepLeafSupply (C : ResolvedCodomainConcreteSupply D G imageOf) where
  /-- The deep forward assembler (6a-10f-4): `Local` + `Align` + `rightLocal_mem` + `forestLocal_mem`. -/
  Forward : ResolvedSectorForwardAssemblerSupply C
  /-- The backward maps. -/
  Backward : ResolvedSectorBackwardSupply C
  /-- The four inverse laws over the assembled concrete forward. -/
  Inverse : ResolvedSectorInverseLawSupply Forward.toSectorForwardConcreteSupply Backward

/-- **R-6c-leaf-19b — into the leaf-19 top-level inventory (concrete forward). -/
noncomputable def ResolvedSectorDeepLeafSupply.toLeafSupply
    {C : ResolvedCodomainConcreteSupply D G imageOf}
    (S : ResolvedSectorDeepLeafSupply C) : ResolvedSectorLeafSupply C where
  Forward := S.Forward.toSectorForwardConcreteSupply
  Backward := S.Backward
  Inverse := S.Inverse

/-- **R-6c-leaf-19b — reconstruct the full sector-equiv assembler from the deep inventory. -/
noncomputable def ResolvedSectorDeepLeafSupply.toAssembler
    {C : ResolvedCodomainConcreteSupply D G imageOf}
    (S : ResolvedSectorDeepLeafSupply C) : ResolvedSectorEquivAssemblerSupply C :=
  S.toLeafSupply.toAssembler

end GaugeGeometry.QFT.Combinatorial
