import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSectorForwardTransport

/-!
# R-6c-body-15 — Sector element shapes from the Product forest elements (via transport)

Fifteenth genuine-body step, on the Sector element shapes (body-5 / leaf-29/30).  When the Codomain forests are
the TRANSPORTED Product forests (body-12), the Sector element shape `(C.rightForest s).elements = image of
transported components` follows from the *untransported* Product forest elements `(R.rightSurvivorForest
s).elements = image of components` — transport commutes with the image.

The key is `elements_transport`: `(h ▸ A).elements = A.elements.image (transport h)` (`subst h`, then
`Finset.image_id'`).  Then, given `(R.rightSurvivorForest s).elements = attach.image (fn s)`, the transported
forest's elements are `attach.image (transport ∘ fn s)` (`elements_transport` + `Finset.image_image`), which is
the Sector element shape.

Per the HALT, the Product forest elements (`(R.rightSurvivorForest s).elements = image …`) are the hypotheses
(genuine 5b-2/5b-3 facts, `rightSurvivorForest_elements` / `remnantForest_elements`); `parent_inj` / Sector
inverse laws untouched.

Landed:

* `elements_transport` — transport commutes with `.elements` (as an image);
* `right_forest_elements_transport` / `remnant_forest_elements_transport` — the transported forest elements as
  the image of the transported component function (the Sector element shapes).

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

set_option linter.unusedSectionVars false in
/-- **R-6c-body-15 — transport commutes with `.elements` (as an image). -/
theorem elements_transport {H K : ResolvedFeynmanGraph} (h : H = K) (A : ResolvedAdmissibleSubgraph H) :
    (h ▸ A).elements = A.elements.image (transportSubgraphAlongGraphEq h) := by
  subst h; exact (Finset.image_id').symm

variable {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}
  {R : ResolvedRightSurvivorSupply D G} {M : ResolvedRemnantComponentSupply D G}

/-- **R-6c-body-15 — the transported right-survivor forest elements as the image of the transported component
function (the Sector `rightForest_elements_eq` shape). -/
theorem right_forest_elements_transport
    (Align : ResolvedSectorForwardGraphAlignment D G imageOf)
    (fn : (s : ResolvedCoassocSplitChoice D G) →
      {x : {y : ResolvedFeynmanSubgraph G // y ∈ s.1.1.elements} // x ∈ s.rightComponents} →
        ResolvedFeynmanSubgraph s.selectedOuterContractGraph)
    (hR : ∀ s : ResolvedCoassocSplitChoice D G,
      (R.rightSurvivorForest s).elements = s.rightComponents.attach.image (fn s))
    (s : ResolvedCoassocSplitChoice D G) :
    (Align.quotientGraph_eq s ▸ R.rightSurvivorForest s).elements
      = s.rightComponents.attach.image
          (fun γ => transportSubgraphAlongGraphEq (Align.quotientGraph_eq s) (fn s γ)) := by
  rw [elements_transport, hR s, Finset.image_image]; rfl

/-- **R-6c-body-15 — the transported remnant forest elements as the image of the transported component function
(the Sector `remnantForest_elements_eq` shape). -/
theorem remnant_forest_elements_transport
    (Align : ResolvedSectorForwardGraphAlignment D G imageOf)
    (fn : (s : ResolvedCoassocSplitChoice D G) →
      {x : {y : ResolvedFeynmanSubgraph G // y ∈ s.1.1.elements} // x ∈ s.forestComponents} →
        ResolvedFeynmanSubgraph s.selectedOuterContractGraph)
    (hM : ∀ s : ResolvedCoassocSplitChoice D G,
      (M.remnantForest s).elements = s.forestComponents.attach.image (fn s))
    (s : ResolvedCoassocSplitChoice D G) :
    (Align.quotientGraph_eq s ▸ M.remnantForest s).elements
      = s.forestComponents.attach.image
          (fun γ => transportSubgraphAlongGraphEq (Align.quotientGraph_eq s) (fn s γ)) := by
  rw [elements_transport, hM s, Finset.image_image]; rfl

end GaugeGeometry.QFT.Combinatorial
