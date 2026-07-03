import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocBranchFiberBody
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSplitChoice

/-!
# R-6c-body-61 — Branch fiber agreement body: LEFT expansion reduced to a pure inner cover

Sixty-first genuine-body step, a SCOUT of body-59's `branch_fiber_agree` — the LEFT (branch) per-`A`
expansion, one of the two remaining OUTPUT-reindex leaves (body-60).  It reduces to an ALREADY-PROVED tensor
identity plus a pure combinatorial inner cover.

## The tensor/linearity content is already discharged

The codebase proves `coassocLeftTail_eq_splitChoiceTermSum` (in `…CoassocSplitChoice`):

```text
D.coassocLeftTail (leftTerm A ⊗ rightTerm A)
  = ∑ p ∈ (A.1.elements.attach).pi (fun γ => D.localChoiceCarrier γ.graph),
      D.resolvedSplitChoiceTerm ⟨A, p⟩
```

i.e. the LEFT tail of the outer forest `A` is the sum of split-choice terms over ALL component-choice
functions `p` with base outer `A` (the pi carrier) — exactly the "local inner choice sum for fixed `A`", with
the associator / `tmul` linearity already inside it (`coassocLeftTail` is an `AlgHom`, its
`…_resolvedForestLeftTerm_choiceSum` derivation does the `map_sum` / `sum_tmul` work).

## What remains is a pure inner cover (fielded)

body-59's `branch_fiber_agree` LHS is the branch outer summand
`assoc((leftTerm A ⊗ rightTerm A) ⊗ 1) + coassocLeftTail (leftTerm A ⊗ rightTerm A)`.  Rewriting the tail by
the theorem above turns it into

```text
assoc((leftTerm A ⊗ rightTerm A) ⊗ 1) + ∑ p ∈ piCarrier A, resolvedSplitChoiceTerm ⟨A, p⟩
```

so `branch_fiber_agree` is left to match this against body-59's fibered RHS

```text
(∑ q ∈ F.forestCarrier with q.1.1 = A, splitTerm q.1) + (∑ q ∈ F.mixedCarrier with q.1.1 = A, splitTerm q.1).
```

That residual equality is a PURE `ResolvedHopfH3` sum identity — no tensor manipulation: it says the pi-choice
carrier (plus the `assoc(⊗1)` boundary term) reindexes onto `F`'s discriminator-split base-outer-`A` fibers.
This is the genuine LEFT inner cover; it is FIELDED here as `ResolvedBranchFiberCoverSupply.branch_cover`.

## Result

`branch_fiber_agree` = `coassocLeftTail_eq_splitChoiceTermSum` (PROVED tensor/linearity) ∘ `branch_cover`
(FIELDED pure inner cover).  So the LEFT OUTPUT leaf is now the single combinatorial field `branch_cover`, with
all tensor content discharged by the existing theorem.

Per the HALT, the inner cover bijection is NOT proved (it is the `branch_cover` field); no image side touched;
tensor content handled only via the pre-existing `coassocLeftTail_eq_splitChoiceTermSum`.

Landed:

* `ResolvedBranchFiberCoverSupply F` — the pure inner cover (pi-choice + boundary ↔ `F`'s base-outer fibers);
* `ResolvedBranchFiberCoverSupply.toBranchFiberAgreementSupply` — body-59's agreement, tail rewritten.

No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-61 — the LEFT inner cover.**  With the tail expanded to the pi-choice sum (by
`coassocLeftTail_eq_splitChoiceTermSum`), the branch outer summand equals `F`'s base-outer-`A` fibered
split-term sum.  Pure `ResolvedHopfH3` sum identity — the genuine LEFT inner cover, no tensor content. -/
structure ResolvedBranchFiberCoverSupply (F : ResolvedCoassocGrandFullSupply D G) where
  /-- The associator boundary term plus the full pi-choice sum reindexes onto `F`'s base-outer-`A` fibers. -/
  branch_cover : ∀ A ∈ (D.supply G).forestCarrier,
    ((Algebra.TensorProduct.assoc ℚ ℚ ℚ ResolvedHopfH ResolvedHopfH ResolvedHopfH).toAlgHom
          (((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A) ⊗ₜ[ℚ] (1 : ResolvedHopfH))
        + ∑ p ∈ (A.1.elements.attach).pi (fun γ => D.localChoiceCarrier (γ.1.toResolvedFeynmanGraph)),
            D.resolvedSplitChoiceTerm (⟨A, p⟩ : ResolvedCoassocSplitChoice D G))
      = (∑ q ∈ F.forestCarrier with resolvedBranchForestFiber F q = A, D.resolvedSplitChoiceTerm q.1)
        + (∑ q ∈ F.mixedCarrier with resolvedBranchMixedFiber F q = A, D.resolvedSplitChoiceTerm q.1)

/-- **R-6c-body-61 — body-59's branch agreement from the inner cover.**  Rewrite the LEFT tail by the proved
`coassocLeftTail_eq_splitChoiceTermSum`, then apply the fielded cover. -/
def ResolvedBranchFiberCoverSupply.toBranchFiberAgreementSupply
    {F : ResolvedCoassocGrandFullSupply D G} (S : ResolvedBranchFiberCoverSupply F) :
    ResolvedBranchFiberAgreementSupply F where
  branch_fiber_agree := fun A hA => by
    rw [D.coassocLeftTail_eq_splitChoiceTermSum A]
    exact S.branch_cover A hA

end GaugeGeometry.QFT.Combinatorial
