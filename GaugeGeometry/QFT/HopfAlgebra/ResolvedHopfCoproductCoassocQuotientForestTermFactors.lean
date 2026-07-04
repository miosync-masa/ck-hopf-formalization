import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocLocalLeftFactorProduct
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocLeftFactor

/-!
# R-6c-body-109 — quotient-forest right factor: the RIGHT identity reduced, symmetric to the LEFT

Hundred-and-ninth genuine-body step, the RIGHT-factor analogue of body-107/108.  The target quotient forest `B =
quotientForestOf q` decomposes as `rightSurvivorForest ∪ remnantForest` (the quotient image is "right survivors ⊔
remnant"), and `∏ localRightFactor(p γ) = leftTerm B` reduces — exactly as the LEFT side did — to two selection
correspondences plus a union split, powered again by `resolvedForestLeftTerm_union`.

## The mirror

`localRightFactor` is the LEFT mirror:

* `inl true ↦ 1` — a left primitive DISAPPEARS on the quotient side (drops);
* `inl false ↦ X γ` — a right primitive is a RIGHT SURVIVOR (its own component survives into the quotient);
* `inr Bᵧ ↦ rightTerm Bᵧ` — a forest choice leaves a REMNANT (the contracted sub-forest's quotient).

So the `isRight`-partition splits `∏ localRightFactor` into the right-survivor part (`¬isRight`, the `inl`
primitives with `inl true ↦ 1` dropping) and the remnant part (`isRight`, the forest choices), matching
`leftTerm(rightSurvivorForest)` and `leftTerm(remnantForest)`.

## The reductions (PROVED)

* `resolved_local_right_factor_product`: `∏ localRightFactor = leftTerm(rightSurvivor) * leftTerm(remnant)`
  from `right_primitive_factor` (`∏_{¬isRight} localRightFactor = leftTerm rightSurvivor`) and `remnant_factor`
  (`∏_{isRight} localRightFactor = leftTerm remnant`), via `prod_filter_mul_prod_filter_not` + `mul_comm`;
* `resolved_quotientForest_right_factor_eq_of_parts`: `∏ localRightFactor = leftTerm B` from those two plus the
  quotient union decomposition `union_eq : B.1 = rightSurvivor ∪ remnant` and disjointness `hdisj`, via
  `resolvedForestLeftTerm_union`.  Discharges BOTH `mixed_right_eq` and `forest_right_eq`.

(Unlike the LEFT side, where `selectedOuterOf.1 = leftOf ∪ promotedOf` was `rfl`, the quotient decomposition
`union_eq` is a fielded fact about the abstract `quotientForestOf` — the "right survivors ⊔ remnant" structure of
the de-contraction image.)

## Symmetry achieved

The two summand product identities are now symmetric:

| side | outer/quotient forest | union split |
|---|---|---|
| LEFT (`∏ leftFactor`) | `selectedOuterOf = leftOf ∪ promotedOf` | body-107/108 |
| RIGHT (`∏ rightFactor`) | `quotientForestOf = rightSurvivor ∪ remnant` | body-109 |

What remains for the summand agreement: the four selection correspondences (`left_primitive` / `promoted` /
`right_primitive` / `remnant`), the two disjointnesses, the quotient union decomposition, and the contract-twice
generator identity (`rightTerm A' = rightTerm B`).

Per the HALT: the RIGHT product algebra + union split are proved; the right-survivor / remnant correspondences
are isolated as fields; the contract-twice quotient generator identity is NOT entered.

Landed:

* `resolved_local_right_factor_product` — `∏ localRightFactor = leftTerm(rightSurvivor) * leftTerm(remnant)`
  (PROVED);
* `resolved_quotientForest_right_factor_eq_of_parts` — `∏ localRightFactor = leftTerm B` (PROVED); discharges
  `mixed_right_eq` and `forest_right_eq`.

Toolkit body (like body-103/107/108), no new supply.  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-109 — the local right-factor product.**  `∏ localRightFactor = leftTerm(rightSurvivor) *
leftTerm(remnant)` from the right-survivor (`¬isRight`) and remnant (`isRight`) correspondences, via an
`isRight`-partition. -/
theorem resolved_local_right_factor_product (q : ForestBlockDomType D G)
    (rightSurvivor remnant : ResolvedAdmissibleSubgraph G)
    (right_primitive_factor :
      (∏ γ ∈ (q.1.1.elements.attach).attach.filter (fun γ => ¬ (q.2 γ.1 γ.2).isRight),
          localRightFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2))
        = resolvedForestLeftTerm rightSurvivor)
    (remnant_factor :
      (∏ γ ∈ (q.1.1.elements.attach).attach.filter (fun γ => (q.2 γ.1 γ.2).isRight),
          localRightFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2))
        = resolvedForestLeftTerm remnant) :
    (∏ γ ∈ (q.1.1.elements.attach).attach,
        localRightFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2))
      = resolvedForestLeftTerm rightSurvivor * resolvedForestLeftTerm remnant := by
  rw [← right_primitive_factor, ← remnant_factor, mul_comm,
    Finset.prod_filter_mul_prod_filter_not]

/-- **R-6c-body-109 — the full right geometric identity from the two quotient-side correspondences.**  `∏
localRightFactor = leftTerm B` from `right_primitive_factor` + `remnant_factor` + the quotient union
decomposition `union_eq` + `hdisj`, via `resolvedForestLeftTerm_union`.  Discharges both `mixed_right_eq` and
`forest_right_eq`. -/
theorem resolved_quotientForest_right_factor_eq_of_parts (q : ForestBlockDomType D G)
    (H : ResolvedFeynmanGraph) (B : (D.supply H).ForestIdx)
    (rightSurvivor remnant : ResolvedAdmissibleSubgraph H)
    (hcross : ∀ γ ∈ rightSurvivor.elements, ∀ δ ∈ remnant.elements, γ ≠ δ → γ.Disjoint δ)
    (union_eq : B.1 = rightSurvivor.union remnant hcross)
    (hdisj : Disjoint rightSurvivor.elements remnant.elements)
    (right_primitive_factor :
      (∏ γ ∈ (q.1.1.elements.attach).attach.filter (fun γ => ¬ (q.2 γ.1 γ.2).isRight),
          localRightFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2))
        = resolvedForestLeftTerm rightSurvivor)
    (remnant_factor :
      (∏ γ ∈ (q.1.1.elements.attach).attach.filter (fun γ => (q.2 γ.1 γ.2).isRight),
          localRightFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2))
        = resolvedForestLeftTerm remnant) :
    (∏ γ ∈ (q.1.1.elements.attach).attach,
        localRightFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2))
      = (D.supply H).leftTerm B := by
  rw [show (D.supply H).leftTerm B = resolvedForestLeftTerm B.1 from rfl, union_eq,
    resolvedForestLeftTerm_union rightSurvivor remnant hcross hdisj,
    ← right_primitive_factor, ← remnant_factor, mul_comm, Finset.prod_filter_mul_prod_filter_not]

end GaugeGeometry.QFT.Combinatorial
