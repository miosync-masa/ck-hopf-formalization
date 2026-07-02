import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSectorIndexBridge
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocElementNonempty
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightSurvivorDisjoint
import GaugeGeometry.QFT.HopfAlgebra.ResolvedSurvivorEmbedComplement

/-!
# R-6c-leaf-27 — Sector local components from the shared nonemptiness + remnant re-embed

Twenty-second leaf-body discharge — the Forward foundation.  `ResolvedSectorLocalComponentSupply` (6a-10f-3)
has three fields:

* `hne` — each right component is nonempty → discharged from the shared `ResolvedInputOuterElementNonemptySupply`
  (leaf-11, `.toSurvivorNonempty`);
* `hcompl` — each right component's edges lie in the selected-outer complement → DISCHARGED from `hne`:
  a nonempty right-primitive is vertex-disjoint from the selected-outer forest
  (`isRightPrimitive_disjoint_vertices_selectedOuterRaw`), hence edge-disjoint
  (`internalEdges_le_complementEdges_of_disjoint`);
* `remnant` — the per-split-choice remnant re-embed supply (6a-5c-4c) → a field.

So the Local construction data collapses to `Nonempty + Remnant`: `rightLocal := rightSurvivorComponentOf`
(both `hne`/`hcompl` from `Nonempty`) and `forestLocal := remnantComponent` (from `Remnant`).

Per the HALT, `remnant` (containment/CD re-embed) stays a field; `rightLocal_mem` / `forestLocal_mem` untouched.

Landed:

* `ResolvedSectorLocalConcreteSupply D G` — `Nonempty` + `Remnant`;
* `.toSectorLocalComponentSupply` — with `hne` / `hcompl` derived, `remnant` from the field.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-leaf-27 — the concrete sector-local construction data.**  The shared component nonemptiness + the
per-split-choice remnant re-embed; `hne` / `hcompl` are both derived from `Nonempty`. -/
structure ResolvedSectorLocalConcreteSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph) where
  /-- The shared input-outer element nonemptiness (leaf-11). -/
  Nonempty : ResolvedInputOuterElementNonemptySupply D G
  /-- The per-split-choice remnant re-embed supply (6a-5c-4c). -/
  Remnant : ∀ s : ResolvedCoassocSplitChoice D G, ResolvedConcreteRemnantReembedSupply D G s

/-- **R-6c-leaf-27 — into the sector local-component supply.**  `hne` = the survivor nonemptiness shape;
`hcompl` = the edge-complement bound from vertex disjointness of a nonempty right-primitive; `remnant` = the field. -/
def ResolvedSectorLocalConcreteSupply.toSectorLocalComponentSupply
    (L : ResolvedSectorLocalConcreteSupply D G) : ResolvedSectorLocalComponentSupply D G where
  hne := L.Nonempty.toSurvivorNonempty
  hcompl := fun s γ => internalEdges_le_complementEdges_of_disjoint _ _
    (s.isRightPrimitive_disjoint_vertices_selectedOuterRaw (Finset.mem_filter.mp γ.2).2
      (L.Nonempty.toSurvivorNonempty s γ))
  remnant := L.Remnant

end GaugeGeometry.QFT.Combinatorial
