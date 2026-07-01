import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocProductGrandSupply

/-!
# R-6c-leaf-4 — Product disjointness leaves grouped (`hCross` from the quotient-forest cross supply)

Fourth leaf-discharge step.  The four disjointness leaves of `ResolvedProductEqGrandSupply` (6a-11b) are
grouped into ONE record, and `hCross` is connected to the already-built quotient-forest cross supply:

* `hPD` — promoted-component pairwise disjointness (forest region);
* `hLP` — left / promoted `Finset`-disjointness (selected-outer union);
* `hCross` — remnant vs right-survivor cross-disjointness (union proof for `hQuot`);
* `hDisj` — remnant / right-survivor element `Finset`-disjointness.

`hCross` is exactly `ResolvedQuotientForestCrossSupply.cross` with the two forests swapped and `Disjoint.symm`
— so it flows from the existing cross machinery (5b-3d).  `hPD` / `hLP` / `hDisj` stay as fields (the genuine
forest-region and `Finset`-disjointness content).

Per the HALT, `hPD` / `hLP` / `hDisj` are NOT proved; no injections.

Landed:

* `ResolvedProductDisjointSupply D G R M` — `hPD` + `hLP` + `hCross` + `hDisj` (exact grand leaf types);
* `hCross_of_quotientForestCross` — `hCross` for `(X.survivor, X.remnant)` from a cross supply.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-leaf-4 — the Product disjointness supply.**  Groups the four `ResolvedProductEqGrandSupply`
disjointness leaves at their exact leaf types. -/
structure ResolvedProductDisjointSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (R : ResolvedRightSurvivorSupply D G) (M : ResolvedRemnantComponentSupply D G) where
  /-- Promoted-component pairwise disjointness (forest region). -/
  hPD : ∀ s : ResolvedCoassocSplitChoice D G,
    (↑(s.1.1.elements.attach) : Set {x : ResolvedFeynmanSubgraph G // x ∈ s.1.1.elements}).PairwiseDisjoint
      s.promotedComponentElements
  /-- Left / promoted disjointness. -/
  hLP : ∀ s : ResolvedCoassocSplitChoice D G,
    Disjoint ((resolvedConcreteLeftSelectionSupply D G).leftOf s).elements
      ((resolvedPromotedOfSupply D G).promotedOf s).elements
  /-- Cross-disjointness of remnants and right-survivors. -/
  hCross : ∀ (s : ResolvedCoassocSplitChoice D G),
    ∀ γ ∈ (M.remnantForest s).elements, ∀ δ ∈ (R.rightSurvivorForest s).elements,
      γ ≠ δ → γ.Disjoint δ
  /-- Element-level disjointness of remnants and right-survivors. -/
  hDisj : ∀ s : ResolvedCoassocSplitChoice D G,
    Disjoint (M.remnantForest s).elements (R.rightSurvivorForest s).elements

/-- **R-6c-leaf-4 — `hCross` from the quotient-forest cross supply (5b-3d).**  The cross supply's `cross`
(survivor vs remnant) is the same fact with the forests swapped; `Disjoint.symm` re-orients it to the
grand `hCross` shape (remnant vs survivor) for `R := X.survivor`, `M := X.remnant`. -/
theorem hCross_of_quotientForestCross (X : ResolvedQuotientForestCrossSupply D G) :
    ∀ (s : ResolvedCoassocSplitChoice D G),
      ∀ γ ∈ (X.remnant.remnantForest s).elements, ∀ δ ∈ (X.survivor.rightSurvivorForest s).elements,
        γ ≠ δ → γ.Disjoint δ := by
  intro s γ hγ δ hδ hne
  exact (X.cross s δ hδ γ hγ (Ne.symm hne)).symm

end GaugeGeometry.QFT.Combinatorial
