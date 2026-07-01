import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocQuotientStarIndexNormal
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightSurvivorDisjoint
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocConcreteRemnant

/-!
# R-6c-heart-6a-10f-3 — sector index bridges to the local survivor / remnant components

The domain sector indices (`RightPrimitiveIndex` / `ForestPrimitiveIndex`, 6a-10a) are bridged to the
indices the existing 5b machinery expects, so the local components over `selectedOuterContractGraph` are
built directly:

* `RightPrimitiveIndex.toRightComponent` — a right-primitive one-stage star IS a right component
  (`∈ s.rightComponents`), feeding 6a-3a `rightSurvivorComponentOf`;
* `ForestPrimitiveIndex.toOccurrence` — a forest-choice one-stage star IS a `ForestChoiceOccurrence`
  (its `B` chosen from `isForest`'s existential), feeding 6a-5c-4c `remnantComponent`.

Then `rightLocal` / `forestLocal` are the actual survivor / remnant components (over
`selectedOuterContractGraph`, ready for 6a-10f-2's alignment transport), modulo the survivor nonemptiness /
edge-bound (`hne` / `hcompl`) and the remnant reembed supply.

Per the HALT, `hne` / `hcompl` / the remnant supply are fields (not proved), no membership in
`rightForest` / `remnantForest`, no inverse maps.

Landed:

* `RightPrimitiveIndex.toRightComponent` / `ForestPrimitiveIndex.toOccurrence` — the index bridges;
* `ResolvedSectorLocalComponentSupply D G imageOf` — survivor args + remnant supply;
* `.rightLocal` / `.forestLocal` — the local survivor / remnant components.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-6a-10f-3 — a right-primitive one-stage star is a right component. -/
def RightPrimitiveIndex.toRightComponent {s : ResolvedCoassocSplitChoice D G}
    (r : RightPrimitiveIndex D G s) :
    {x : {y : ResolvedFeynmanSubgraph G // y ∈ s.1.1.elements} // x ∈ s.rightComponents} :=
  ⟨r.i.toComponent, by
    simp only [ResolvedCoassocSplitChoice.rightComponents, Finset.mem_filter, Finset.mem_attach,
      true_and]
    exact r.hR⟩

/-- **R-6c-heart-6a-10f-3 — a forest-choice one-stage star is a forest-choice occurrence. -/
noncomputable def ForestPrimitiveIndex.toOccurrence {s : ResolvedCoassocSplitChoice D G}
    (f : ForestPrimitiveIndex D G s) : s.ForestChoiceOccurrence :=
  ⟨f.i.toComponent, Classical.choose f.hF, Classical.choose_spec f.hF⟩

variable {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}

/-- **R-6c-heart-6a-10f-3 — the local-component construction data.**  The survivor nonemptiness / edge bound
and the remnant reembed supply. -/
structure ResolvedSectorLocalComponentSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph) where
  /-- Each right component is nonempty. -/
  hne : ∀ (s : ResolvedCoassocSplitChoice D G)
    (γ : {x : {y : ResolvedFeynmanSubgraph G // y ∈ s.1.1.elements} // x ∈ s.rightComponents}),
    γ.1.1.vertices.Nonempty
  /-- Each right component's edges lie in the selected-outer complement. -/
  hcompl : ∀ (s : ResolvedCoassocSplitChoice D G)
    (γ : {x : {y : ResolvedFeynmanSubgraph G // y ∈ s.1.1.elements} // x ∈ s.rightComponents}),
    γ.1.1.internalEdges
      ≤ ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).complementEdges
  /-- The remnant reembed supply per split choice. -/
  remnant : ∀ s : ResolvedCoassocSplitChoice D G, ResolvedConcreteRemnantReembedSupply D G s

/-- **R-6c-heart-6a-10f-3 — the local survivor component. -/
noncomputable def ResolvedSectorLocalComponentSupply.rightLocal
    (L : ResolvedSectorLocalComponentSupply D G) (s : ResolvedCoassocSplitChoice D G)
    (r : RightPrimitiveIndex D G s) : ResolvedFeynmanSubgraph s.selectedOuterContractGraph :=
  rightSurvivorComponentOf s (L.hne s) (L.hcompl s) r.toRightComponent

/-- **R-6c-heart-6a-10f-3 — the local remnant component. -/
noncomputable def ResolvedSectorLocalComponentSupply.forestLocal
    (L : ResolvedSectorLocalComponentSupply D G) (s : ResolvedCoassocSplitChoice D G)
    (f : ForestPrimitiveIndex D G s) : ResolvedFeynmanSubgraph s.selectedOuterContractGraph :=
  (L.remnant s).remnantComponent f.toOccurrence

end GaugeGeometry.QFT.Combinatorial
