import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSelectedOuterTermFactors

/-!
# R-6c-body-108 — local left-factor product: the LEFT identity fully reduced to two selection correspondences

Hundred-and-eighth genuine-body step, closing the left geometric identity's LHS.  Body-107 reduced `∏
localLeftFactor = leftTerm(selectedOuterOf q)` to `left_factor_product` (`= leftTerm(leftOf q) * leftTerm(promotedOf
q)`) plus disjointness.  This body PROVES `left_factor_product` from a clean two-way partition of the component
product — so the ENTIRE left identity now rests on just two map-specific selection correspondences plus
disjointness.

## The partition (PROVED)

`resolved_local_left_factor_product`: partitioning the component product by `(p γ).isRight` (forest choice vs
primitive) and applying `Finset.prod_filter_mul_prod_filter_not`,

```text
∏_γ localLeftFactor (p γ) = leftTerm (leftOf q) * leftTerm (promotedOf q)
```

follows from:

* `left_primitive_factor`: `∏_{γ : ¬(p γ).isRight} localLeftFactor (p γ) = leftTerm (leftOf q)` — the
  primitive (`inl`) components' contributions (right-primitives are `localLeftFactor = 1` and drop inside) equal
  the left-selected forest's left term;
* `promoted_factor`: `∏_{γ : (p γ).isRight} localLeftFactor (p γ) = leftTerm (promotedOf q)` — the forest
  (`inr`) components' contributions (`localLeftFactor (inr Bᵧ) = leftTerm Bᵧ`) equal the promoted forest's left
  term.

Both are in the uniform `localLeftFactor` form (no `Sum`-value extraction), so the partition is just
`prod_filter_mul_prod_filter_not` + `mul_comm`.

## The full left identity (PROVED, chaining body-107)

`resolved_selectedOuter_left_factor_eq_of_parts`: from `left_primitive_factor` + `promoted_factor` + `hdisj`,

```text
∏_γ localLeftFactor (p γ) = leftTerm (selectedOuterOf q)
```

— chaining `resolved_local_left_factor_product` into body-107's `resolved_selectedOuter_left_factor_eq`.  This
discharges BOTH `mixed_left_eq` and `forest_left_eq`.

## What remains for the left identity

The three residual facts are all map-specific and about the SELECTION (`leftSelected` / `promotedOf`), not the
tensor algebra:

* `left_primitive_factor` — the left-selected component set matches the `inl`-primitive choices (`leftOf =
  filterElements leftSelected`, so this is a `Finset.prod` reindex once `leftSelected γ ↔ p γ = inl true`);
* `promoted_factor` — the promoted forest's components flatten the forest-choice sub-forests `Bᵧ`;
* `hdisj` — the left / promoted component sets are disjoint.

Per the HALT: the LHS partition is proved (`prod_filter_mul_prod_filter_not`); `promoted_factor` (the forest
flattening) is isolated as a field; the RIGHT factor (`B`) and quotient generator identity are NOT entered.

Landed:

* `resolved_local_left_factor_product` — `∏ localLeftFactor = leftTerm(leftOf) * leftTerm(promotedOf)` from the
  two selection correspondences (PROVED);
* `resolved_selectedOuter_left_factor_eq_of_parts` — the full left identity from the two correspondences +
  `hdisj` (PROVED); discharges `mixed_left_eq` and `forest_left_eq`.

Toolkit body (like body-103/107), no new supply.  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-108 — the local left-factor product.**  `∏ localLeftFactor = leftTerm(leftOf) *
leftTerm(promotedOf)` from the primitive (`¬isRight`) and forest (`isRight`) selection correspondences, via a
`isRight`-partition. -/
theorem resolved_local_left_factor_product
    (S : ResolvedCoassocSelectedOuterImageSupply D G) (q : ForestBlockDomType D G)
    (left_primitive_factor :
      (∏ γ ∈ (q.1.1.elements.attach).attach.filter (fun γ => ¬ (q.2 γ.1 γ.2).isRight),
          localLeftFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2))
        = resolvedForestLeftTerm (S.leftSelection.leftOf q))
    (promoted_factor :
      (∏ γ ∈ (q.1.1.elements.attach).attach.filter (fun γ => (q.2 γ.1 γ.2).isRight),
          localLeftFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2))
        = resolvedForestLeftTerm (S.promotedOf q)) :
    (∏ γ ∈ (q.1.1.elements.attach).attach,
        localLeftFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2))
      = resolvedForestLeftTerm (S.leftSelection.leftOf q) * resolvedForestLeftTerm (S.promotedOf q) := by
  rw [← left_primitive_factor, ← promoted_factor, mul_comm,
    Finset.prod_filter_mul_prod_filter_not]

/-- **R-6c-body-108 — the full left geometric identity from the two selection correspondences.**  `∏
localLeftFactor = leftTerm(selectedOuterOf q)` from `left_primitive_factor` + `promoted_factor` + `hdisj`
(chaining body-107).  Discharges both `mixed_left_eq` and `forest_left_eq`. -/
theorem resolved_selectedOuter_left_factor_eq_of_parts
    (S : ResolvedCoassocSelectedOuterImageSupply D G) (q : ForestBlockDomType D G)
    (left_primitive_factor :
      (∏ γ ∈ (q.1.1.elements.attach).attach.filter (fun γ => ¬ (q.2 γ.1 γ.2).isRight),
          localLeftFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2))
        = resolvedForestLeftTerm (S.leftSelection.leftOf q))
    (promoted_factor :
      (∏ γ ∈ (q.1.1.elements.attach).attach.filter (fun γ => (q.2 γ.1 γ.2).isRight),
          localLeftFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2))
        = resolvedForestLeftTerm (S.promotedOf q))
    (hdisj : Disjoint (S.leftSelection.leftOf q).elements (S.promotedOf q).elements) :
    (∏ γ ∈ (q.1.1.elements.attach).attach,
        localLeftFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2))
      = (D.supply G).leftTerm (S.selectedOuterOf q) :=
  resolved_selectedOuter_left_factor_eq S q
    (resolved_local_left_factor_product S q left_primitive_factor promoted_factor) hdisj

end GaugeGeometry.QFT.Combinatorial
