import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSelectedOuterRegionAssembly

/-!
# R-6c-body-175 — promoted region round-trip: the de-contraction leaf, carved out of the tag facts

Hundred-and-seventy-fifth genuine-body step, carving body-174's asymmetry into the type.  Body-174 proved
`leftOf_recovered_eq` from pure tag facts but had to *field* `promotedOf_recovered_eq`, because the promoted region
is de-contracted, not a filter.  This body isolates that fielded fact as its **own named geometry leaf** —
`ResolvedPromotedRegionRoundTripSupply` — so the forward-outer residual now reads, structurally, as one
promotion/de-contraction round-trip plus one coverage partition, not "two anonymous fields of an assembly supply".

## This is NOT a tag lemma

`recoverChoice_leftOf_eq` (body-174) matched `leftOf` to `leftResidual` because both are the *original* components
tagged `inl true`.  The promoted side is different in kind:

* `promotedOf recovered .elements = recovered.promotedElements` — the **de-contracted** promoted forest, the
  `biUnion` over the forest-tagged components `γ` of `(promote γ.1 Bᵧ).elements` (the sub-forest `Bᵧ` promoted back
  into `G`);
* `forestRecovered z .elements = (forestDomain z).attach.image (componentToForest z)` — the forest-choice
  **parents**, the `componentToForest` images of the star-touching remnant components of the quotient `B`.

Their equality is the **promotion / de-contraction sector round-trip**:

```text
forestRecovered parents  ↔  promotedOf (de-contracted forest choices)
```

driven by `componentToForest` / `ForestPrimitiveIndex.toOccurrence` and the `promote` machinery — the backward
mirror of the forward remnant construction.  It is exactly the kind of fact the tag argument could never reach.

## The leaf (fielded) and the flow to body-174

`ResolvedPromotedRegionRoundTripSupply D S Region` fields the single equality `promoted_region_eq`.
`.toSelectedOuterRegionAssemblySupply` takes it together with the coverage partition `target_outer_partition` and
produces body-174's `ResolvedSelectedOuterRegionAssemblySupply` — so the two forward-outer residuals are now
explicitly the two *different* obligations:

1. `promoted_region_eq` — the promotion / de-contraction round-trip (this leaf);
2. `target_outer_partition` — the target coverage `leftResidual ∪ forestRecovered = A` (the star-touch / remnant
   characterisation).

A natural finer split (deferred) is to route both sides through a common
`promotedElementsFromForestRecovered z` — `promotedOf = that` and `forestRecovered = that` — but the single named
leaf is enough to record the asymmetry here.

Per the HALT: the `componentToForest` inverse body is not entered; `target_outer_partition` is untouched; the
promotion round-trip is isolated as an independent geometry leaf, kept apart from the tag proof.

Landed:

* `ResolvedPromotedRegionRoundTripSupply D S Region` — the promotion / de-contraction round-trip leaf;
* `.toSelectedOuterRegionAssemblySupply` — body-174's supply from this leaf + the coverage partition.

Toolkit body (like body-174).  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-175 — the promoted region round-trip leaf.**  The single de-contraction equality: the promoted
forest of the recovered choice equals the forest-recovered region.  This is the promotion / de-contraction sector
round-trip (`componentToForest` / `promote`), **not** a tag lemma. -/
structure ResolvedPromotedRegionRoundTripSupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) (Region : ResolvedRegionChoiceRoundTripSupply D S) where
  /-- The promoted forest (de-contracted forest choices) is the forest-recovered region (the `componentToForest`
  parents) — the promotion / de-contraction round-trip. -/
  promoted_region_eq : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    ((S.Forward.imageSupply G).promotedOf
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).elements
      = (Region.Union.forestRecovered z).elements

namespace ResolvedPromotedRegionRoundTripSupply

variable {S : ResolvedConcreteSummandBundleSupply D} {Region : ResolvedRegionChoiceRoundTripSupply D S}

/-- **R-6c-body-175 — body-174's assembly supply from the promotion leaf + the coverage partition.**  The two
forward-outer residuals kept explicitly separate: this promotion round-trip and the target coverage. -/
def toSelectedOuterRegionAssemblySupply (P : ResolvedPromotedRegionRoundTripSupply D S Region)
    (target_outer_partition : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
      (γ : ResolvedFeynmanSubgraph G),
      (γ ∈ (Region.Union.leftResidual z).elements ∨ γ ∈ (Region.Union.forestRecovered z).elements)
        ↔ γ ∈ z.1.1.elements) :
    ResolvedSelectedOuterRegionAssemblySupply D S Region where
  promotedOf_recovered_eq := fun {G} z => P.promoted_region_eq z
  target_outer_partition := fun {G} z γ => target_outer_partition z γ

end ResolvedPromotedRegionRoundTripSupply

end GaugeGeometry.QFT.Combinatorial
