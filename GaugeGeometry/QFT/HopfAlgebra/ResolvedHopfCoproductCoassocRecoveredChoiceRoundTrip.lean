import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRoundTripComponentPartition

/-!
# R-6c-body-164 — recovered choice round-trip: the backward-choice `HEq` as a named region leaf

Hundred-and-sixty-fourth genuine-body step, isolating body-160's backward-choice round-trip.  The heterogeneous
`backward_choice : HEq (recoverChoice (fwdMap q)) q.2` — "the reconstructed choice of a forward image is the
original choice" — is pinned to its own named leaf, separated from the quotient round-trip, with its region-wise
meaning documented.  This leaves `forward_quotient` as the last heterogeneous round-trip.

## The `HEq` and its region meaning

`recoverChoice (fwdMap q)` is a choice function on the components of `unionOuter (fwdMap q)` (`= A'` by body-163's
`recoveredOuter_partition` at the element level), while `q.2` is a choice on `A' = q.1`'s components; the two live
over different (but equal) outer forests, so the round-trip is a `HEq`.  Under the outer identification, it is the
component-wise agreement — each region's `recoverChoice` tag matches the original `q.2`:

* a `leftResidual` component (`inl true`) matches `q`'s left-primitive choice;
* a `rightRecovered` component (`inl false`) matches `q`'s right-primitive choice;
* a `forestRecovered` component (`inr Bᵧ`) matches `q`'s forest choice.

This is exactly the region tagging (bodies 146/152) read back on the forward image: the tags of the reconstructed
choice are the region-priority tags, and on a forward image those coincide with `q`'s original component choices.
The full componentwise reduction is the dependent `HEq` transport across the outer equality (the region-priority
`recoverChoice` vs `q.2`), fielded here as the single `backward_choice_heq`.

## The leaf

`ResolvedRecoveredChoiceRoundTripSupply D S Region` fields the single `backward_choice_heq`; `.backward_choice`
re-exports it — body-160's `backward_choice`.  So the backward-choice round-trip is now a named leaf with its
region meaning fixed, and the only remaining heterogeneous round-trip is `forward_quotient` (B-reconstruction).

Per the HALT: the `componentToRight` / `componentToForest` sector inverse laws are not entered; the dependent `HEq`
transport is kept as the named leaf `backward_choice_heq`; its region-wise meaning is documented.

Landed:

* `ResolvedRecoveredChoiceRoundTripSupply D S Region` — the backward-choice `HEq` leaf;
* `.backward_choice` — body-160's backward-choice round-trip.

Toolkit body (like body-162/163).  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-164 — the recovered-choice round-trip supply.**  The backward-choice `HEq` — the reconstructed
choice of a forward image is the original choice (region tags read back), as a single named leaf. -/
structure ResolvedRecoveredChoiceRoundTripSupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) (Region : ResolvedRegionChoiceRoundTripSupply D S) where
  /-- p-recovery: the reconstruction's choice of a forward image is the original choice (heterogeneous). -/
  backward_choice_heq : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G),
    HEq (Region.recoverChoice (fwdMap S q)) q.2

/-- **R-6c-body-164 — body-160's backward-choice round-trip from the leaf.** -/
theorem ResolvedRecoveredChoiceRoundTripSupply.backward_choice
    {S : ResolvedConcreteSummandBundleSupply D} {Region : ResolvedRegionChoiceRoundTripSupply D S}
    (P : ResolvedRecoveredChoiceRoundTripSupply D S Region) {G : ResolvedFeynmanGraph}
    (q : ForestBlockDomType D G) :
    HEq (Region.recoverChoice (fwdMap S q)) q.2 :=
  P.backward_choice_heq q

end GaugeGeometry.QFT.Combinatorial
