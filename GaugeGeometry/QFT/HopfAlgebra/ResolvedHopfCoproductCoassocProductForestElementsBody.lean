import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSectorElementShapesBody

/-!
# R-6c-body-16 — Product forest element shapes discharge the body-15 transport hypotheses

Sixteenth genuine-body step, closing the last free hypotheses of body-15.  Body-15 reduced the Sector element
shapes to the *untransported* Product forest elements `(R.rightSurvivorForest s).elements = attach.image (fn s)`
(the parametric `hR` / `hM`).  Those are exactly the existing `@[simp]` facts 5b-2 / 5b-3:

```text
ResolvedRightSurvivorSupply.rightSurvivorForest_elements :
  (R.rightSurvivorForest s).elements = s.rightComponents.attach.image (R.survivorComponent s)          -- rfl

ResolvedRemnantComponentSupply.remnantForest_elements :
  (R.remnantForest s).elements =
    s.forestComponents.attach.image (fun γ => R.remnantComponent s (s.forestComponentOccurrence γ))     -- rfl
```

Both hold by `rfl` (the forests are *defined* as `ofElements` of these images), so no `occurrence_match`
connector is needed on the remnant side — the remnant forest is built over `forestComponentOccurrence` already.

Feeding these into body-15's `right_forest_elements_transport` / `remnant_forest_elements_transport` (with
`fn := R.survivorComponent` / `fn := fun γ => M.remnantComponent s (s.forestComponentOccurrence γ)`) gives the
FULLY CONCRETE transported Sector element shapes — no free `fn` / `hR` / `hM` remaining.

Per the HALT, `parent_inj` / the Sector inverse laws are untouched.

Landed:

* `right_forest_elements_transport_concrete` — the transported right-survivor forest elements as the image of
  the transported `R.survivorComponent`;
* `remnant_forest_elements_transport_concrete` — the transported remnant forest elements as the image of the
  transported `M.remnantComponent ∘ forestComponentOccurrence`.

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
  {R : ResolvedRightSurvivorSupply D G} {M : ResolvedRemnantComponentSupply D G}

set_option linter.unusedSectionVars false in
/-- **R-6c-body-16 — the concrete transported right-survivor forest elements.**  Body-15's transport shape with
`hR` discharged by the 5b-2 `rightSurvivorForest_elements` (`rfl`); `fn := R.survivorComponent`. -/
theorem right_forest_elements_transport_concrete
    (Align : ResolvedSectorForwardGraphAlignment D G imageOf)
    (s : ResolvedCoassocSplitChoice D G) :
    (Align.quotientGraph_eq s ▸ R.rightSurvivorForest s).elements
      = s.rightComponents.attach.image
          (fun γ => transportSubgraphAlongGraphEq (Align.quotientGraph_eq s) (R.survivorComponent s γ)) :=
  right_forest_elements_transport Align (R.survivorComponent)
    (fun s => R.rightSurvivorForest_elements s) s

set_option linter.unusedSectionVars false in
/-- **R-6c-body-16 — the concrete transported remnant forest elements.**  Body-15's transport shape with `hM`
discharged by the 5b-3 `remnantForest_elements` (`rfl`); `fn := fun γ => M.remnantComponent s
(s.forestComponentOccurrence γ)`.  No `occurrence_match` needed — the remnant forest is built over
`forestComponentOccurrence`. -/
theorem remnant_forest_elements_transport_concrete
    (Align : ResolvedSectorForwardGraphAlignment D G imageOf)
    (s : ResolvedCoassocSplitChoice D G) :
    (Align.quotientGraph_eq s ▸ M.remnantForest s).elements
      = s.forestComponents.attach.image
          (fun γ => transportSubgraphAlongGraphEq (Align.quotientGraph_eq s)
            (M.remnantComponent s (s.forestComponentOccurrence γ))) :=
  remnant_forest_elements_transport Align
    (fun s γ => M.remnantComponent s (s.forestComponentOccurrence γ))
    (fun s => M.remnantForest_elements s) s

end GaugeGeometry.QFT.Combinatorial
