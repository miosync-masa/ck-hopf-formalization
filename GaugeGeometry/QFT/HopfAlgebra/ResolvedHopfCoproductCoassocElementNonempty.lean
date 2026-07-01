import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocProductDisjointConcrete
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocConcreteSurvivor

/-!
# R-6c-leaf-11 — the shared input-outer element nonemptiness supply

Leaf-8 (survivor) and leaf-10 (`hLP`) both needed the *same* fact — that every input-outer component (element
of `s.1.1.elements`) has nonempty vertices — under two different subtype shapes.  There is no
`IsConnectedDivergent → vertices.Nonempty` lemma in this development, so nonemptiness is a genuine supplied
fact; this file isolates it ONCE and adapts it to both consumers.

Landed:

* `ResolvedInputOuterElementNonemptySupply D G` — `component_nonempty` (one field);
* `.toSurvivorNonempty` — the `rightComponentNonempty` shape (`resolvedConcreteRightSurvivorSupply`, 6a-3c);
* `.toHLPNonempty` — the `hLP` shape (`product_hLP_of_elements_nonempty`, leaf-10);
* `.toConcreteRightSurvivorSupply` / `.hLP` — the two consumers wired from the single field.

Per the HALT, `component_nonempty` is NOT proved (no `IsConnectedDivergent → Nonempty` available); no
`hPD` / `hDisj`; no RIGHT leaves.

So the "nonempty leaf" now lives in one place: proving `component_nonempty` once discharges both consumers.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-leaf-11 — the input-outer element nonemptiness supply.**  Every input-outer component has nonempty
vertices — the single fact behind the survivor and `hLP` nonemptiness hypotheses. -/
structure ResolvedInputOuterElementNonemptySupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph) where
  /-- Every input-outer component (element of `s.1.1.elements`) has nonempty vertices. -/
  component_nonempty : ∀ (s : ResolvedCoassocSplitChoice D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ s.1.1.elements}), γ.1.vertices.Nonempty

/-- **R-6c-leaf-11 — the survivor nonemptiness shape (`rightComponentNonempty`). -/
theorem ResolvedInputOuterElementNonemptySupply.toSurvivorNonempty
    (N : ResolvedInputOuterElementNonemptySupply D G) :
    ∀ (s : ResolvedCoassocSplitChoice D G)
      (γ : {x : {y : ResolvedFeynmanSubgraph G // y ∈ s.1.1.elements} // x ∈ s.rightComponents}),
      γ.1.1.vertices.Nonempty :=
  fun s γ => N.component_nonempty s γ.1

/-- **R-6c-leaf-11 — the `hLP` nonemptiness shape. -/
theorem ResolvedInputOuterElementNonemptySupply.toHLPNonempty
    (N : ResolvedInputOuterElementNonemptySupply D G) :
    ∀ (s : ResolvedCoassocSplitChoice D G), ∀ δ ∈ s.1.1.elements, δ.vertices.Nonempty :=
  fun s δ hδ => N.component_nonempty s ⟨δ, hδ⟩

/-- **R-6c-leaf-11 — the concrete right-survivor supply from the single nonemptiness field. -/
noncomputable def ResolvedInputOuterElementNonemptySupply.toConcreteRightSurvivorSupply
    (N : ResolvedInputOuterElementNonemptySupply D G) : ResolvedRightSurvivorSupply D G :=
  resolvedConcreteRightSurvivorSupply D G N.toSurvivorNonempty

/-- **R-6c-leaf-11 — the Product `hLP` leaf from the single nonemptiness field. -/
theorem ResolvedInputOuterElementNonemptySupply.hLP
    (N : ResolvedInputOuterElementNonemptySupply D G) :
    ∀ s : ResolvedCoassocSplitChoice D G,
      Disjoint ((resolvedConcreteLeftSelectionSupply D G).leftOf s).elements
        ((resolvedPromotedOfSupply D G).promotedOf s).elements :=
  fun s => product_hLP_of_elements_nonempty N.toHLPNonempty s

end GaugeGeometry.QFT.Combinatorial
