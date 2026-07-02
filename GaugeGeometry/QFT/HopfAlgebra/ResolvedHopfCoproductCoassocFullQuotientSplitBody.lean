import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocQuotientForestElementsBody
import GaugeGeometry.QFT.HopfAlgebra.ResolvedActualSigmaCover

/-!
# R-6c-body-17 — the full-quotient `toImage` split (`elements = remnant ∪ right`, `rfl`)

Seventeenth genuine-body step, closing body-14's last supply field.  The full-quotient image
`ResolvedFullQuotientForestImageData.toImage` is *defined* with `elements := remnantComponents ∪
rightComponents`, so the union split is a `rfl` `@[simp]` lemma already present in the σ-cover file:

```text
ResolvedFullQuotientForestImageData.toImage_elements :
  F.toImage.elements = F.remnantComponents ∪ F.rightComponents := rfl
```

Body-14's `toImage_split` asks the SAME union but (a) about the abstract `(imageOf s).quotientForest` and
(b) with the components being the *transported* Product forests (body-12's construction).  So the union
combinatorics is fully discharged by `toImage_elements` (`rfl`); what remains — per the HALT — is fielded
separately as two atomic identifications:

* `quotientForest_union` — `(imageOf s).quotientForest.elements = remnantComponents s ∪ rightComponents s`
  (the `imageOf ↔ fullQuotient` identification; for a quotient forest CONSTRUCTED as a `.toImage` this is
  exactly `toImage_elements`, hence `rfl`);
* `remnant_components_eq` / `right_components_eq` — the components ARE the transported Product remnant / right
  forests (`Align.quotientGraph_eq s ▸ M.remnantForest s` / `… R.rightSurvivorForest s`).

Given those, body-14's `toImage_split` is a three-`rw` composition — the union split contributes nothing new.

Per the HALT, `parent_inj` is untouched and `fullQuotient` is not refactored; the `imageOf ↔ toImage`
identification is fielded, not proved.

Landed:

* `fullQuotient_toImage_split` — the stated target (`toImage.elements = remnant ∪ right`), `= toImage_elements`;
* `ResolvedFullQuotientSplitConnector D G imageOf R M` — `Align` + the two component finsets + the union
  identification + the two component identities + `untransported_disjoint`;
* `.toQuotientForestElementsConnector` — the body-14 connector (`toImage_split` via the three `rw`).

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

/-- **R-6c-body-17 — the full-quotient `toImage` union split** (the stated target).  The full-quotient image
is defined as `remnantComponents ∪ rightComponents`, so this is `ResolvedFullQuotientForestImageData.toImage_elements`
(`rfl`). -/
theorem fullQuotient_toImage_split {G : ResolvedFeynmanGraph} {D : ResolvedSigmaCoverData G}
    (F : ResolvedFullQuotientForestImageData D) :
    F.toImage.elements = F.remnantComponents ∪ F.rightComponents :=
  F.toImage_elements

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}
  {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}

/-- **R-6c-body-17 — the full-quotient split connector.**  The alignment + the quotient forest's two
component finsets + the `imageOf ↔ union` identification (`= toImage_elements` for a `.toImage`-built quotient
forest) + the two transported-forest component identities + the untransported disjointness. -/
structure ResolvedFullQuotientSplitConnector (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G)
    (R : ResolvedRightSurvivorSupply D G) (M : ResolvedRemnantComponentSupply D G) where
  /-- The graph alignment `selectedOuterContractGraph = quotient graph`. -/
  Align : ResolvedSectorForwardGraphAlignment D G imageOf
  /-- The star-touching remnant components of the quotient forest (over the quotient graph). -/
  remnantComponents : ∀ s : ResolvedCoassocSplitChoice D G,
    Finset (ResolvedFeynmanSubgraph (resolvedCoassocQuotientGraph (imageOf s)))
  /-- The star-avoiding right-survivor components of the quotient forest (over the quotient graph). -/
  rightComponents : ∀ s : ResolvedCoassocSplitChoice D G,
    Finset (ResolvedFeynmanSubgraph (resolvedCoassocQuotientGraph (imageOf s)))
  /-- The quotient forest is the union of its components (= `toImage_elements`, `rfl` for a `.toImage`). -/
  quotientForest_union : ∀ s : ResolvedCoassocSplitChoice D G,
    (imageOf s).quotientForest.elements = remnantComponents s ∪ rightComponents s
  /-- The remnant components ARE the transported Product remnant forest. -/
  remnant_components_eq : ∀ s : ResolvedCoassocSplitChoice D G,
    remnantComponents s = (Align.quotientGraph_eq s ▸ M.remnantForest s).elements
  /-- The right components ARE the transported Product right-survivor forest. -/
  right_components_eq : ∀ s : ResolvedCoassocSplitChoice D G,
    rightComponents s = (Align.quotientGraph_eq s ▸ R.rightSurvivorForest s).elements
  /-- The untransported right / remnant forests are element-disjoint (= Product `hDisj`). -/
  untransported_disjoint : ∀ s : ResolvedCoassocSplitChoice D G,
    Disjoint (R.rightSurvivorForest s).elements (M.remnantForest s).elements

variable {R : ResolvedRightSurvivorSupply D G} {M : ResolvedRemnantComponentSupply D G}

/-- **R-6c-body-17 — the body-14 quotient-forest-elements connector.**  `toImage_split` is the union split
(`toImage_elements`) composed with the two component identities. -/
def ResolvedFullQuotientSplitConnector.toQuotientForestElementsConnector
    (S : ResolvedFullQuotientSplitConnector D G imageOf R M) :
    ResolvedQuotientForestElementsConnector D G imageOf R M where
  Align := S.Align
  toImage_split := fun s => by
    rw [S.quotientForest_union s]
    exact congrArg₂ (· ∪ ·) (S.remnant_components_eq s) (S.right_components_eq s)
  untransported_disjoint := S.untransported_disjoint

end GaugeGeometry.QFT.Combinatorial
