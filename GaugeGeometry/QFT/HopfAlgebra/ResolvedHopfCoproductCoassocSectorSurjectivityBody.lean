import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSectorBackwardMaps
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSectorForwardLeaf

/-!
# R-6c-body-3 — Sector forward surjectivity from the forest element shapes + index surjectivity

Third genuine-body step.  `ResolvedSectorBackwardFromImageSupply.right_surj` / `forest_surj` (leaf-31, behind
the backward maps) — that the forward maps cover the Codomain forests — are proved from the forest element
shapes (leaf-29/30: the forests are the `ofElements`-images over the component `attach` finsets) PLUS the
index surjectivities (every component index comes from an input-outer primitive index).

For `δ ∈ (C.rightForest s).elements`: the element shape gives `δ = transport (rightSurvivorComponentOf … γ)`
for some `γ ∈ rightComponents.attach`; the index surjectivity gives `r` with `r.toRightComponent = γ`; then
`rightForward s r = transport (Local.rightLocal s r) = transport (rightSurvivorComponentOf … γ) = δ`.  The
forest side is identical through `forestComponentOccurrence` / `f.toOccurrence`.

Per the HALT, the element shapes and the index surjectivities are supply fields; injectivity / inverse laws
untouched.

Landed:

* `ResolvedSectorSurjectivityConnector C A` — the two element shapes + the two index surjectivities;
* `.toSectorBackwardFromImageSupply` — the leaf-31 surjectivity supply for `A.toSectorForwardConcreteSupply`.

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

open scoped Classical

/-- **R-6c-body-3 — the sector surjectivity connector.**  The forest element shapes + the component-index
surjectivities. -/
structure ResolvedSectorSurjectivityConnector (C : ResolvedCodomainConcreteSupply D G imageOf)
    (A : ResolvedSectorForwardAssemblerSupply C) where
  /-- The right forest is the image of the transported local survivor components. -/
  right_elements_eq : ∀ s : ResolvedCoassocSplitChoice D G,
    (C.rightForest s).elements =
      s.rightComponents.attach.image (fun γ =>
        transportSubgraphAlongGraphEq (A.Align.quotientGraph_eq s)
          (rightSurvivorComponentOf s (A.Local.hne s) (A.Local.hcompl s) γ))
  /-- The remnant forest is the image of the transported remnant components. -/
  remnant_elements_eq : ∀ s : ResolvedCoassocSplitChoice D G,
    (C.remnantForest s).elements =
      s.forestComponents.attach.image (fun γ =>
        transportSubgraphAlongGraphEq (A.Align.quotientGraph_eq s)
          ((A.Local.remnant s).remnantComponent (s.forestComponentOccurrence γ)))
  /-- Every right component comes from a right-primitive index. -/
  right_index_surj : ∀ (s : ResolvedCoassocSplitChoice D G)
    (γ : {x : {y : ResolvedFeynmanSubgraph G // y ∈ s.1.1.elements} // x ∈ s.rightComponents}),
    ∃ r : RightPrimitiveIndex D G s, r.toRightComponent = γ
  /-- Every forest component's occurrence comes from a forest-primitive index. -/
  forest_index_surj : ∀ (s : ResolvedCoassocSplitChoice D G)
    (γ : {x : {y : ResolvedFeynmanSubgraph G // y ∈ s.1.1.elements} // x ∈ s.forestComponents}),
    ∃ f : ForestPrimitiveIndex D G s, f.toOccurrence = s.forestComponentOccurrence γ

/-- **R-6c-body-3 — the leaf-31 surjectivity supply from the element shapes + index surjectivities. -/
noncomputable def ResolvedSectorSurjectivityConnector.toSectorBackwardFromImageSupply
    {C : ResolvedCodomainConcreteSupply D G imageOf}
    {A : ResolvedSectorForwardAssemblerSupply C}
    (S : ResolvedSectorSurjectivityConnector C A) :
    ResolvedSectorBackwardFromImageSupply C A.toSectorForwardConcreteSupply where
  right_surj := fun s δ => by
    obtain ⟨x, hx⟩ := δ
    rw [S.right_elements_eq s] at hx
    obtain ⟨γ, _, hγδ⟩ := Finset.mem_image.mp hx
    obtain ⟨r, hr⟩ := S.right_index_surj s γ
    refine ⟨r, Subtype.ext ?_⟩
    show transportSubgraphAlongGraphEq (A.Align.quotientGraph_eq s) (A.Local.rightLocal s r) = x
    rw [ResolvedSectorLocalComponentSupply.rightLocal, hr]
    exact hγδ
  forest_surj := fun s δ => by
    obtain ⟨x, hx⟩ := δ
    rw [S.remnant_elements_eq s] at hx
    obtain ⟨γ, _, hγδ⟩ := Finset.mem_image.mp hx
    obtain ⟨f, hf⟩ := S.forest_index_surj s γ
    refine ⟨f, Subtype.ext ?_⟩
    show transportSubgraphAlongGraphEq (A.Align.quotientGraph_eq s) (A.Local.forestLocal s f) = x
    rw [ResolvedSectorLocalComponentSupply.forestLocal, hf]
    exact hγδ

end GaugeGeometry.QFT.Combinatorial
