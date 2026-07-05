import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRoundTripComponentPartition

/-!
# R-6c-body-165 — recovered quotient round-trip: the forward-quotient `HEq` as a named region leaf

Hundred-and-sixty-fifth genuine-body step, the last of the four round-trip obligations.  The heterogeneous
`forward_quotient : HEq (quotientForest ⟨unionOuter z, recoverChoice z⟩) z.2` — "the recovered quotient forest is
`B`" — is pinned to its own named leaf, with its region-wise meaning documented.  With bodies 162/163/164 this
completes the localisation of all four round-trips.

## The `HEq` and its region meaning

`quotientForest ⟨unionOuter z, recoverChoice z⟩` is the quotient sub-forest of the recovered split choice (over the
recovered selected outer's contract graph), while `z.2 = B` is the original quotient forest (over `A`'s contract
graph); the two live over different (but equal, by body-162's `selectedOuter_partition`) contract graphs, so the
round-trip is a `HEq`.  Under the outer identification it is the reconstruction of `B` from the region tags:

* the `rightRecovered` components (`inl false`) reconstruct `B`'s star-avoiding survivor components;
* the `forestRecovered` components (`inr Bᵧ`) reconstruct `B`'s star-touching remnant components;
* the `leftResidual` components (`inl true`) do not contribute to the quotient forest;

so `quotientForest (recovered split) = survivor ⊔ remnant = B`.  This is the forward direction of the summand
bundle's `union_eq` (`B = rightSurvivor ⊔ remnant`, body-129) read on the recovered choice.  The full
componentwise reduction is the dependent `HEq` transport across the contract-graph equality, fielded here as the
single `forward_quotient_heq`.

## The leaf

`ResolvedRecoveredQuotientRoundTripSupply D S Region` fields the single `forward_quotient_heq`;
`.forward_quotient` re-exports it — body-160's `forward_quotient`.  So all four round-trip obligations are now
named / local:

| round-trip | body | form |
|---|---|---|
| forward outer (A-reconstruction) | 162 | `leftOf ⊔ promotedOf = A` element partition |
| backward outer (A'-recovery) | 163 | region union partition (via `union_eq`) |
| backward choice (p-recovery) | 164 | region-tag `HEq` leaf |
| forward quotient (B-reconstruction) | 165 | region-tag `HEq` leaf (this) |

The round-trip proof-shape is closed; the residual is the region partition / sector / base geometry.

Per the HALT: the `componentToRight` / `componentToForest` sector inverse laws are not entered; the dependent `HEq`
transport is kept as the named leaf `forward_quotient_heq`; its region-wise meaning is documented.

Landed:

* `ResolvedRecoveredQuotientRoundTripSupply D S Region` — the forward-quotient `HEq` leaf;
* `.forward_quotient` — body-160's forward-quotient round-trip.

Toolkit body (like body-164).  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-165 — the recovered-quotient round-trip supply.**  The forward-quotient `HEq` — the recovered
quotient forest of a split choice is `B` (survivor ⊔ remnant from the region tags), as a single named leaf. -/
structure ResolvedRecoveredQuotientRoundTripSupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) (Region : ResolvedRegionChoiceRoundTripSupply D S) where
  /-- B-reconstruction: the recovered quotient forest of the recovered split choice is `B` (heterogeneous). -/
  forward_quotient_heq : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    HEq (S.quotientForest
      (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)) z.2

/-- **R-6c-body-165 — body-160's forward-quotient round-trip from the leaf.** -/
theorem ResolvedRecoveredQuotientRoundTripSupply.forward_quotient
    {S : ResolvedConcreteSummandBundleSupply D} {Region : ResolvedRegionChoiceRoundTripSupply D S}
    (P : ResolvedRecoveredQuotientRoundTripSupply D S Region) {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType D G) :
    HEq (S.quotientForest
      (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)) z.2 :=
  P.forward_quotient_heq z

end GaugeGeometry.QFT.Combinatorial
