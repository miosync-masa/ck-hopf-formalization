import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocLeftInner

/-!
# R-6c-2d-2b — the left inner expansion vessel (component-choice expansion)

R-6c-2d-2a reduced the left tail of an outer forest summand to a *product over components* of the
component coproducts: `Δᵣ(leftTerm A) = ∏ γ, gen (componentGen γ)`, where each factor
`gen (componentGen γ) = primitive γ + forestSum γ` is a **sum**.  Expanding that product-of-sums is a
genuine combinatorial expansion — a sum over **component choices** (per component: a primitive leg or
a nontrivial subforest), the resolved analogue of the flat `forestComponentChoiceSigma` (used here
only as a *template*, never reused).

Rather than implement the dependent product-of-sums carrier inline (a known sink), R-6c-2d-2b first
fixes the **type** of the result: the left tail of a forest summand splits as a primitive **leak**
(the all-primitive component choice) plus a **choice sum** (the choices with ≥ 1 nontrivial
subforest).  Both are supplied data; the split is the obligation.  This separates the remaining R-6c
work into

* *constructing* the component-choice expansion data (the heavy product-of-sums, R-6c-2d-2b-impl), and
* *regrouping* `choiceSum` into the global `branchSum` via the σ-cover (R-6c-2d-2c / 2d-4).

Landed:

* `ResolvedComponentChoiceExpansion D A` — the vessel: `primitiveLeak`, `choiceSum`, and the
  `expansion` obligation `coassocLeftTail D (leftTerm A ⊗ rightTerm A) = primitiveLeak + choiceSum`;
* `coassocLeftTail_forestSummand_of_componentChoiceExpansion` — the accessor delivering the split.

No facade, no flat term, no `forgetHopf`, no per-`A` equality (the final reindex stays global).
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable (D : ResolvedCoproductProperForestData)

/-- **R-6c-2d-2b — the left inner (component-choice) expansion vessel.**  For one outer forest
summand `A`, the left tail `coassocLeftTail D (leftTerm A ⊗ rightTerm A)` splits as a primitive
**leak** (the all-primitive component choice) plus a **choice sum** (the nontrivial subforest
choices).  Both pieces are supplied data in `ResolvedHopfH3`; the `expansion` field is the obligation.
Constructing an instance is the product-of-sums expansion (the resolved replay of the flat component
choice sigma); this vessel pins its *shape* so the rest of R-6c can treat it as an interface. -/
structure ResolvedComponentChoiceExpansion {G : ResolvedFeynmanGraph}
    (A : {A : ResolvedAdmissibleSubgraph G // A ∈ D.carrier G}) where
  /-- The all-primitive (leak) part of the left inner expansion. -/
  primitiveLeak : ResolvedHopfH3
  /-- The nontrivial component-choice sum (the branch-side inner terms for this outer forest). -/
  choiceSum : ResolvedHopfH3
  /-- **The obligation**: the left tail of the forest summand splits as `primitiveLeak + choiceSum`. -/
  expansion : D.coassocLeftTail ((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A)
    = primitiveLeak + choiceSum

/-- The split delivered by a component-choice expansion vessel. -/
theorem coassocLeftTail_forestSummand_of_componentChoiceExpansion {G : ResolvedFeynmanGraph}
    {A : {A : ResolvedAdmissibleSubgraph G // A ∈ D.carrier G}}
    (E : ResolvedComponentChoiceExpansion D A) :
    D.coassocLeftTail ((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A)
      = E.primitiveLeak + E.choiceSum :=
  E.expansion

end GaugeGeometry.QFT.Combinatorial
