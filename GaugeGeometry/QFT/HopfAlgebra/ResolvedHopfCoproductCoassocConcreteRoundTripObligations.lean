import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRegionRoundTripReduction

/-!
# R-6c-body-154 — concrete round-trip obligations: the two `Sigma` round-trips as four named region facts

Hundred-and-fifty-fourth genuine-body step, fixing the specification of the backward map's two round-trips.  Body-147
reduced the four branch forward/backward specs to two whole-split-choice round-trips via `Sigma.ext`; those in turn
are four `Sigma`-component obligations (`forward_outer` / `forward_quotient` / `backward_outer` / `backward_choice`).
This body isolates those four into a standalone obligation record, with each obligation's **region meaning** named,
so the region geometry to discharge next is exact.

## The four obligations (region meaning)

`ResolvedConcreteRoundTripObligationSupply D S Region` fields, against the concrete union region-choice supply
(body-146/152/153):

* `forward_outer` — `selectedOuterOf ⟨unionOuter z, recoverChoice z⟩ = z.1` — **`A` is reconstructed**: the
  left-selected (`leftResidual`, `inl true`) and promoted (`forestRecovered`, `inr`) parts of the recovered choice
  reassemble the target outer `A`; the right-primitive part (`rightRecovered`, `inl false`) does not contribute to
  the selected outer;
* `forward_quotient` — `HEq (quotientForest ⟨unionOuter z, recoverChoice z⟩) z.2` — **`B` is reconstructed**: the
  survivor part (`rightRecovered`) gives `B`'s star-avoiding components and the remnant part (`forestRecovered`)
  its star-touching components;
* `backward_outer` — `unionOuter (fwdMap q) = q.1` — **`A'` is recovered**: the three regions of the forward image
  recover the original outer forest `q.1` component-by-component;
* `backward_choice` — `HEq (recoverChoice (fwdMap q)) q.2` — **`p` is recovered**: each region's tag matches the
  original choice (`inl true` / `inl false` / `inr Bᵧ`).

## The adapter

`.toRegionRoundTripReductionSupply` combines the `Region` supply with these four obligations to produce body-147's
`ResolvedRegionRoundTripReductionSupply` — and hence, through body-147 → 144 → 141 → 139, the whole index/cover
bijection.  So the two `Sigma` round-trips are no longer opaque: they are exactly the "A-reconstruction",
"B-reconstruction", "A'-recovery" and "p-recovery" facts, each local to the three concrete regions.

Per the HALT: no region fact is proved; the four obligations are named with their region meaning and separated into
their own record; no sector-map construction is entered.

Landed:

* `ResolvedConcreteRoundTripObligationSupply D S Region` — the four `Sigma`-component round-trip obligations;
* `.toRegionRoundTripReductionSupply` — body-147's reduction supply (→ the bijection).

Toolkit body (like body-153).  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-154 — the concrete round-trip obligation supply.**  The four `Sigma`-component round-trips against
a fixed region-choice supply `Region`: `A`-reconstruction (`forward_outer`), `B`-reconstruction (`forward_quotient`),
`A'`-recovery (`backward_outer`), `p`-recovery (`backward_choice`). -/
structure ResolvedConcreteRoundTripObligationSupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) (Region : ResolvedRegionChoiceRoundTripSupply D S) where
  /-- `A`-reconstruction: the recovered selected outer is the target outer `A`. -/
  forward_outer : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    (S.Forward.imageSupply G).selectedOuterOf
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G) = z.1
  /-- `B`-reconstruction: the recovered quotient forest is `B` (heterogeneous). -/
  forward_quotient : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    HEq (S.quotientForest
      (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)) z.2
  /-- `A'`-recovery: the reconstruction's outer of a forward image is the original outer. -/
  backward_outer : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G),
    Region.Union.unionOuter (fwdMap S q) = q.1
  /-- `p`-recovery: the reconstruction's choice of a forward image is the original choice (heterogeneous). -/
  backward_choice : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G),
    HEq (Region.recoverChoice (fwdMap S q)) q.2

/-- **R-6c-body-154 — body-147's round-trip reduction supply from the region supply + the four obligations.** -/
def ResolvedConcreteRoundTripObligationSupply.toRegionRoundTripReductionSupply
    {S : ResolvedConcreteSummandBundleSupply D} {Region : ResolvedRegionChoiceRoundTripSupply D S}
    (O : ResolvedConcreteRoundTripObligationSupply D S Region) :
    ResolvedRegionRoundTripReductionSupply D S where
  Region := Region
  forward_outer := fun {G} z => O.forward_outer z
  forward_quotient := fun {G} z => O.forward_quotient z
  backward_outer := fun {G} q => O.backward_outer q
  backward_choice := fun {G} q => O.backward_choice q

end GaugeGeometry.QFT.Combinatorial
