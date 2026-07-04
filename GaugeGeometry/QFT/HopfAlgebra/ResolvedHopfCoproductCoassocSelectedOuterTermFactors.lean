import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocQuotientForestConstructor
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocLeftFactor

/-!
# R-6c-body-107 — selectedOuter left-factor: `∏ leftFactor = leftTerm(selectedOuterOf)` reduced to one lemma

Hundred-and-seventh genuine-body step, discharging the LEFT geometric identity of the outer-mixing map now that
the forward map is `A_target = selectedOuterOf q = leftOf q ∪ promotedOf q` (body-105).  Both `mixed_left_eq` and
`forest_left_eq` (`∏ localLeftFactor = leftTerm A_target`) collapse to ONE reduction lemma, powered by the
already-proved `resolvedForestLeftTerm_union`.

## The reduction (PROVED)

`resolved_selectedOuter_left_factor_eq`: for any split choice `q` and image supply `S`,

```text
∏_γ localLeftFactor (p γ) = leftTerm (S.selectedOuterOf q)
```

follows from just two map-specific facts:

* `left_factor_product`: `∏_γ localLeftFactor (p γ) = leftTerm (leftOf q) * leftTerm (promotedOf q)` — the LHS
  splits into the left-primitive contributions (`leftOf`) and the promoted-forest contributions (`promotedOf`),
  with the right-primitive `1`s dropping (the component partition);
* `hdisj`: `Disjoint (leftOf q).elements (promotedOf q).elements` — the left and promoted component sets are
  disjoint.

The proof: `(D.supply G).leftTerm (selectedOuterOf q) = resolvedForestLeftTerm (leftOf q ∪ promotedOf q)` is
`rfl` (`selectedOuterOf.1` IS the union), and `resolvedForestLeftTerm_union` (`LeftFactor` 62) splits it as
`leftTerm (leftOf q) * leftTerm (promotedOf q)` — matching `left_factor_product`.

## What remains for the left identity

The left factor is now ENTIRELY reduced to `left_factor_product` (the LHS component partition into left / promoted
/ right-drop) and `hdisj` (component-set disjointness) — both map-specific facts about `leftOf` / `promotedOf`.
`left_factor_product` itself splits (via body-103's `resolved_prod_bif_eq_filter` + factor evaluations) into the
left-primitive components giving `leftTerm (leftOf)` and the forest components giving `leftTerm (promotedOf)` —
the `leftOf` / `promotedOf` component-set correspondences.

Per the HALT: the union split is proved (`resolvedForestLeftTerm_union` is the engine); the left factor equality
is reduced to `left_factor_product` + `hdisj`; the RIGHT factor (`B`) and the quotient generator identity are
NOT entered; no promote-supply component construction discharged.

Landed:

* `resolved_selectedOuter_left_factor_eq` — the left geometric identity from `left_factor_product` + `hdisj`
  (PROVED); discharges both `mixed_left_eq` and `forest_left_eq`.

Toolkit body (like body-103), no new supply.  No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- **R-6c-body-107 — the left geometric identity, reduced to one union split.**  `∏ localLeftFactor = leftTerm
(selectedOuterOf q)` from the LHS component partition (`left_factor_product`) and the left/promoted disjointness
(`hdisj`), via `resolvedForestLeftTerm_union`.  Discharges both `mixed_left_eq` and `forest_left_eq`. -/
theorem resolved_selectedOuter_left_factor_eq
    (S : ResolvedCoassocSelectedOuterImageSupply D G) (q : ForestBlockDomType D G)
    (left_factor_product :
      (∏ γ ∈ (q.1.1.elements.attach).attach,
          localLeftFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2))
        = resolvedForestLeftTerm (S.leftSelection.leftOf q) * resolvedForestLeftTerm (S.promotedOf q))
    (hdisj : Disjoint (S.leftSelection.leftOf q).elements (S.promotedOf q).elements) :
    (∏ γ ∈ (q.1.1.elements.attach).attach,
        localLeftFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2))
      = (D.supply G).leftTerm (S.selectedOuterOf q) := by
  rw [left_factor_product, show (D.supply G).leftTerm (S.selectedOuterOf q)
      = resolvedForestLeftTerm ((S.leftSelection.leftOf q).union (S.promotedOf q) (S.cross q)) from rfl,
    resolvedForestLeftTerm_union (S.leftSelection.leftOf q) (S.promotedOf q) (S.cross q) hdisj]

end GaugeGeometry.QFT.Combinatorial
