import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecoveredQuotientRoundTrip

/-!
# R-6c-body-203 — forward-quotient HEq scout: reduced to a `ForestIdx` element `HEq`

Two-hundred-and-third genuine-body step, a scout of the last round-trip leaf `forward_quotient_heq` (body-165).
The audit found the ambient transport is already proved and the `HEq` reduces — via a reusable `ForestIdx` helper —
to a `HEq` of the underlying component Finsets; it proved the helper and the reduction, isolating the element
identity as the one remaining leaf.

## The type mismatch and its (already proved) transport

`forward_quotient_heq : HEq (quotientForest recovered) z.2` compares two `ForestIdx = {B // B ∈ carrier}` over two
*different* contract-with-stars graphs:

```text
LHS ambient   ((imageSupply G).selectedOuterOf recovered).1.contractWithStars (starOf …)
RHS ambient   z.1.1.contractWithStars (starOf G z.1.1)
```

differing only through the outer `(selectedOuterOf recovered).1` vs `z.1.1`.  The transporting equality is the
already-proved `selectedOuter_partition z : (selectedOuterOf recovered).1.elements = z.1.1.elements`
(body-162/190) — the *same* index transport that closed `backward_choice_heq`, on the dual side.

## The reusable helper (PROVED)

`heq_forestIdx` is the `ForestIdx`-over-contract transport: a subgraph equality of the outers plus a `HEq` of the
component Finsets gives the `HEq` of the two `ForestIdx`.  Proof: `cases` the outer equality (the outers are
abstract bound variables here, so this sidesteps the projection-`cases` wall), then `Subtype.ext ∘
ResolvedAdmissibleSubgraph.ext_elements ∘ eq_of_heq`.  This is the `ForestIdx` analogue of body-193's
`heq_of_index_eq` — the flat-`Coassoc` `Sigma_snd_heq_of_eq` pattern as a clean Resolved lemma.

## The reduction (PROVED)

`ResolvedForwardQuotientHEqDecompositionSupply D S Region` fields the reused `selectedOuter_partition` (the ambient
transport) and the reduced leaf `quotient_elements_heq` — the `HEq` of the recovered quotient's components with `B`'s
components.  Then `.forward_quotient_heq` is **proved** by `heq_forestIdx`; `.toRecoveredQuotientRoundTripSupply`
produces body-165's supply — so the forward-quotient `HEq` reduces to the component identity `quotient_elements_heq`.

## What remains (the fresh residual, body-204)

`quotient_elements_heq` reduces (after the ambient transport) to the survivor/remnant element reconstruction:
`(quotientForest recovered).1 = rightSurvivorForest ⊔ remnantForest` (body-129 `union_eq`) on the left, and `z.2`'s
components split by the star into `rightDomain ∪ forestDomain` (`Finset.filter_union_filter_neg_eq`) on the right —
leaving `(rightSurvivorForest recovered).elements = rightDomain z` and `(remnantForest recovered).elements =
forestDomain z` as the two genuinely fresh survivor/remnant identities (the dual of the backward-choice de-contraction
kernel, bodies 125/126/156/183).

Per the HALT: the survivor/remnant reconstruction is not entered; `quotient_elements_heq` is fielded; only the helper
and the ambient reduction are proved.

Landed:

* `heq_forestIdx` — the reusable `ForestIdx`-over-contract `HEq` transport (PROVED);
* `ResolvedForwardQuotientHEqDecompositionSupply D S Region` — the ambient transport + the reduced element `HEq`;
* `.forward_quotient_heq` — body-165's leaf (PROVED from the reduction);
* `.toRecoveredQuotientRoundTripSupply` — body-165's supply.

Scout / toolkit body (like body-193).  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-203 — the `ForestIdx`-over-contract `HEq` transport.**  A subgraph equality of the outers plus a
`HEq` of the component Finsets gives the `HEq` of the two `ForestIdx`.  `cases` the outer equality (abstract bound
variables, so no projection wall), then `Subtype.ext ∘ ext_elements ∘ eq_of_heq`. -/
theorem heq_forestIdx {G : ResolvedFeynmanGraph} {A₁ A₂ : ResolvedAdmissibleSubgraph G}
    (B₁ : (D.supply (A₁.contractWithStars (D.starOf G A₁))).ForestIdx)
    (B₂ : (D.supply (A₂.contractWithStars (D.starOf G A₂))).ForestIdx)
    (houter : A₁ = A₂)
    (helem : HEq B₁.1.elements B₂.1.elements) :
    HEq B₁ B₂ := by
  cases houter
  exact heq_of_eq (Subtype.ext (ResolvedAdmissibleSubgraph.ext_elements (eq_of_heq helem)))

/-- **R-6c-body-203 — the forward-quotient HEq decomposition supply.**  The reused ambient transport
`selectedOuter_partition` (body-162/190) and the reduced element `HEq` `quotient_elements_heq`. -/
structure ResolvedForwardQuotientHEqDecompositionSupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) (Region : ResolvedRegionChoiceRoundTripSupply D S) where
  /-- Body-162/190: the recovered selected outer has exactly `A`'s components (the ambient transport). -/
  selectedOuter_partition : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    ((S.Forward.imageSupply G).selectedOuterOf
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).1.elements
      = z.1.1.elements
  /-- The reduced leaf: the recovered quotient forest's components are `B`'s components (heterogeneous). -/
  quotient_elements_heq : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    HEq (S.quotientForest
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).1.elements
      z.2.1.elements

namespace ResolvedForwardQuotientHEqDecompositionSupply

variable {S : ResolvedConcreteSummandBundleSupply D} {Region : ResolvedRegionChoiceRoundTripSupply D S}

/-- **R-6c-body-203 — body-165's `forward_quotient_heq` from the reduction.** -/
theorem forward_quotient_heq (F : ResolvedForwardQuotientHEqDecompositionSupply D S Region)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) :
    HEq (S.quotientForest
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)) z.2 :=
  heq_forestIdx _ z.2
    (ResolvedAdmissibleSubgraph.ext_elements (F.selectedOuter_partition z))
    (F.quotient_elements_heq z)

/-- **R-6c-body-203 — body-165's recovered-quotient round-trip supply from the decomposition.** -/
def toRecoveredQuotientRoundTripSupply (F : ResolvedForwardQuotientHEqDecompositionSupply D S Region) :
    ResolvedRecoveredQuotientRoundTripSupply D S Region where
  forward_quotient_heq := fun {G} z => F.forward_quotient_heq z

end ResolvedForwardQuotientHEqDecompositionSupply

end GaugeGeometry.QFT.Combinatorial
