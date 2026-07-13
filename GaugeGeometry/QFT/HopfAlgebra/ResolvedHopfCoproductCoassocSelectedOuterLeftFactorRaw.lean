import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocLocalLeftFactorProduct
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocLeftFactor

/-!
# R-6c-body-258 — raw-keyed selected-outer left factor: the last migration boundary crossed (PROVED)

Two-hundred-and-fifty-eighth genuine-body step — the raw-keyed left-factor identity that removes the **last** total
selected-outer supply from the summand-agreement term path.  Body-257's audit found the only place the retired total
root still entered the factor equalities is the left-factor helper
`resolved_selectedOuter_left_factor_eq_of_parts` (`LocalLeftFactorProduct.lean:104`), whose *argument type* bundles the
total `S : ResolvedCoassocSelectedOuterImageSupply` (its proof uses only raw `leftOf` / `promotedOf`).  This body
supplies the **re-keyed variant**: the left-factor product equals `resolvedForestLeftTerm (leftOf.union promotedOf)`,
stated over raw admissible subgraphs, with **no `S` / `Forward` in its type**.

## The raw-keyed lemma

```lean
resolved_selectedOuter_left_factor_eq_of_parts_raw
    (q) (leftOf promotedOf : ResolvedAdmissibleSubgraph G) (cross) (hdisj)
    (left_primitive_factor : ∏_{¬isRight} localLeftFactor = resolvedForestLeftTerm leftOf)
    (promoted_factor       : ∏_{isRight}  localLeftFactor = resolvedForestLeftTerm promotedOf) :
    ∏ localLeftFactor = resolvedForestLeftTerm (leftOf.union promotedOf cross)
```

proved verbatim in the shape of the `S`-free right-factor lemma
`resolved_quotientForest_right_factor_eq_of_parts` (`QuotientForestTermFactors.lean:118`):
`resolvedForestLeftTerm_union` + the two branch factors + `mul_comm` + `Finset.prod_filter_mul_prod_filter_not`.

Fed `leftOf / promotedOf / cross := (resolvedConcreteForestPromoteSupply D G).{leftOf, promotedOf, cross} q`, the union
is `selectedOuterRawOf q` by `rfl` (`Promote.lean:61`), and the output `resolvedForestLeftTerm (selectedOuterRawOf q)`
is defeq to `(D.supply G).leftTerm (fwdMapFilteredValue F V q).1` (`leftTerm A = resolvedForestLeftTerm A.1`,
`Supply.lean:153`; `fwdMapFilteredValue_outer_fst` is `rfl`) — i.e. exactly the `hL` the generic factor-eqs theorem
(`resolved_splitChoice_summand_agree_of_factor_eqs`, `ForestCarryingBlock.lean:68`) needs, `Forward`-free.

## The residual (body-259)

This crosses the last migration boundary at the **left-factor** level; the canonical `summand_agree_value` discharge
(body-259) now composes this raw `hL`, the `S`-free `hR` (`resolved_quotientForest_right_factor_eq_of_parts`), and
`hQ := V.quot_eq` through the generic theorem — with no `ResolvedConcreteSummandBundleSupply` in any declaration type.

Per the HALT: only the raw-keyed left-factor identity is proved (no `S` / `Forward` in its type); the full
`summand_agree_value` assembly is body-259.  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-258 — the raw-keyed selected-outer left factor.**  The left-factor product over the split choice `q`
equals `resolvedForestLeftTerm (leftOf.union promotedOf)`, stated over raw admissible subgraphs — no total selected
image supply, no `Forward`.  Re-keying of `resolved_selectedOuter_left_factor_eq_of_parts` (the last term-path boundary). -/
theorem resolved_selectedOuter_left_factor_eq_of_parts_raw (q : ForestBlockDomType D G)
    (leftOf promotedOf : ResolvedAdmissibleSubgraph G)
    (cross : ∀ γ ∈ leftOf.elements, ∀ δ ∈ promotedOf.elements, γ ≠ δ → γ.Disjoint δ)
    (hdisj : Disjoint leftOf.elements promotedOf.elements)
    (left_primitive_factor :
      (∏ γ ∈ (q.1.1.elements.attach).attach.filter (fun γ => ¬ (q.2 γ.1 γ.2).isRight),
          localLeftFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2))
        = resolvedForestLeftTerm leftOf)
    (promoted_factor :
      (∏ γ ∈ (q.1.1.elements.attach).attach.filter (fun γ => (q.2 γ.1 γ.2).isRight),
          localLeftFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2))
        = resolvedForestLeftTerm promotedOf) :
    (∏ γ ∈ (q.1.1.elements.attach).attach,
        localLeftFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2))
      = resolvedForestLeftTerm (leftOf.union promotedOf cross) := by
  rw [resolvedForestLeftTerm_union leftOf promotedOf cross hdisj,
    ← left_primitive_factor, ← promoted_factor, mul_comm, Finset.prod_filter_mul_prod_filter_not]

end GaugeGeometry.QFT.Combinatorial
