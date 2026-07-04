import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocOuterMixingAssembly
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocPromotedOf
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocLeftSelectConcrete

/-!
# R-6c-body-117 — left-primitive factor: the selection↔choice correspondence (pattern for all four products)

Hundred-and-seventeenth genuine-body step, opening the first of the four remaining factor products,
`left_primitive_factor` (`∏_{¬isRight} localLeftFactor(p γ) = leftTerm(leftOf q)`).  The key structural facts —
the concrete left-selection predicate IS the `inl true` component choice, and `leftOf`'s components are exactly
the `inl-true`-filtered input components — are PROVED here (all definitional/`rfl`).  They fix the
component-set correspondence behind ALL four factor products; the residual is the double-`attach` reindex plus
the right-primitive drop-out (body-103).

## The correspondence (PROVED)

For a split choice `q` (`= ResolvedCoassocSplitChoice D G`):

* `resolved_choiceAt_eq_choice`: `q.2 γ.1 γ.2 = choiceAt q γ.1` — the choice function at a component IS the
  `choiceAt` accessor (proof-irrelevance of the `attach` membership; `choiceAt q γ := q.2 γ (mem_attach)`);
* `resolved_leftSelectedConcrete_iff`: `leftSelectedConcrete q γ ↔ ∃ hγ, choiceAt q ⟨γ, hγ⟩ = Sum.inl true` —
  the concrete left-selection predicate is exactly "the component's choice is `inl true`" (`Iff.rfl`);
* `resolved_leftOf_elements_eq`: `(leftOf q).elements = q.1.1.elements.filter (leftSelectedConcrete q)` — `leftOf`
  cuts out the left-primitive components (`filterElements`, `rfl`).

So `leftOf`'s components are precisely `{γ ∈ A'.elements : p γ = inl true}`, and `leftTerm(leftOf) = ∏ X` over
them (body-103).

## The reduction of `left_primitive_factor`

With the correspondence, `left_primitive_factor` reduces to:

1. RIGHT-PRIMITIVE DROP-OUT: over the `¬isRight` filter, `localLeftFactor(inl b) = bif b then X else 1`, so the
   `inl false` (right-primitive) factors are `1` and drop (`resolved_prod_bif_eq_filter`, body-103), leaving `∏`
   over the `inl true` components;
2. DOUBLE-`attach` REINDEX: `∏` over `(A'.elements.attach).attach.filter (p · = inl true)` of `X(component gen)`
   `=` `∏` over `(A'.elements.filter (leftSelectedConcrete)).attach = (leftOf).elements.attach` of `X(component
   gen)` — a `Finset.prod` reindex over the correspondence, with the generators matching
   (`localLeftFactor(inl true) = X(γ.toResolvedHopfGen)` and `resolvedComponentGen γ = γ.toResolvedHopfGen`).

## The pattern for all four products

This selection↔choice correspondence is the common shape of all four factor leaves:

* `left_primitive_factor` — `leftOf` = `inl true` components (this body);
* `promoted_factor` — `promotedOf` = the promoted sub-forests of the `inr` (forest) components;
* `right_primitive_factor` — `rightSurvivor` = the `inl false` (right-primitive) components' quotient images;
* `remnant_factor` — `remnant` = the `inr` (forest) components' remnant images.

Each reduces to its component-set correspondence (proved/`rfl` here for `leftOf`) plus the same double-`attach`
reindex; the reindex and the promoted/quotient image identifications are the residual (per-component sector
forward maps).

Per the HALT: the promoted factor product is NOT entered; the `leftOf` component-set correspondence is PROVED
(`rfl`); the residual reindex is isolated; no sector forward map is constructed.

Landed:

* `resolved_choiceAt_eq_choice` / `resolved_leftSelectedConcrete_iff` / `resolved_leftOf_elements_eq` — the
  selection↔choice correspondence (PROVED, definitional).

Toolkit/scout body (like body-103/107–112), no new supply.  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-117 — the choice function at a component is the `choiceAt` accessor.** -/
theorem resolved_choiceAt_eq_choice (q : ResolvedCoassocSplitChoice D G)
    (γ : {x : {y : ResolvedFeynmanSubgraph G // y ∈ q.1.1.elements} // x ∈ q.1.1.elements.attach}) :
    q.2 γ.1 γ.2 = ResolvedCoassocSplitChoice.choiceAt q γ.1 := by
  rw [ResolvedCoassocSplitChoice.choiceAt]

/-- **R-6c-body-117 — the concrete left-selection predicate is the `inl true` choice.** -/
theorem resolved_leftSelectedConcrete_iff (q : ResolvedCoassocSplitChoice D G)
    (γ : ResolvedFeynmanSubgraph G) :
    ResolvedCoassocSplitChoice.leftSelectedConcrete q γ
      ↔ ∃ hγ : γ ∈ q.1.1.elements, ResolvedCoassocSplitChoice.choiceAt q ⟨γ, hγ⟩ = Sum.inl true :=
  Iff.rfl

/-- **R-6c-body-117 — `leftOf`'s components are the left-primitive (`inl true`) input components.** -/
theorem resolved_leftOf_elements_eq (q : ResolvedCoassocSplitChoice D G) :
    ((resolvedConcreteLeftSelectionSupply D G).leftOf q).elements
      = q.1.1.elements.filter (fun γ => ResolvedCoassocSplitChoice.leftSelectedConcrete q γ) :=
  rfl

end GaugeGeometry.QFT.Combinatorial
