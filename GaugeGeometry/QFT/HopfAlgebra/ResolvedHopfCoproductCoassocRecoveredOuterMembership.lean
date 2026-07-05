import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocOuterUnionRegionsConcrete

/-!
# R-6c-body-159 — recovered outer carrier membership: the carrier-closure leaf for `A'`

Hundred-and-fifty-ninth genuine-body step, isolating the last hidden obstruction of the region construction: the
carrier membership of the recovered outer forest.  Body-153's `recoveredOuter_mem` — that the assembled
`(leftResidual ∪ rightRecovered) ∪ forestRecovered` lies in `D.carrier G` — is pinned to a single named leaf,
parallel to `selectedOuter_mem` (body-128).

## Why it is a carrier-closure leaf

The recovered outer `A' = (leftResidual ∪ rightRecovered) ∪ forestRecovered` is a proper, pairwise-disjoint,
divergent admissible forest built from the three regions (their `CD` and disjointness are established by bodies
156/157/158).  For a **canonical** carrier — the complete `properDisjointAdmissibleDivergentSubgraphs` — any such
forest is a member, so `recovered_outer_mem` is a theorem there.  For an **abstract** parametric `D.carrier` there
is no sub-forest / union closure (the carrier fields are `carrier` / `starOf` / `hCD` / `carrier_mapPerm` /
`star_mapPerm` only — body-137), so `recovered_outer_mem` is a genuine additional primitive — exactly the same
status as `selectedOuter_mem` (body-128, the selected outer `leftOf ∪ promotedOf`'s carrier membership).  This is
the last carrier-closure obligation of the outer-mixing bijection.

## The leaf

`ResolvedRecoveredOuterCarrierSupply D S leftResidual rightRecovered forestRecovered hcross_lr hcross_lrf` fields
the single membership

```text
recovered_outer_mem : ((leftResidual z).union rightRecovered) .union forestRecovered ∈ D.carrier G
```

and `.toRecoveredOuterMem` re-exports it — the exact `recoveredOuter_mem` field of body-153's
`ResolvedOuterUnionRegionsConcreteSupply`.  So the union's carrier membership is no longer buried inside the region
construction; it is a named leaf, and the region construction's residual is cleanly: the element partition /
round-trips, the pairwise disjointnesses, and this carrier closure.

Per the HALT: the carrier closure is not proved for abstract `D` (the canonical route via
`properDisjointAdmissibleDivergentSubgraphs` is named); it is kept as an exact leaf like `selectedOuter_mem`.

Landed:

* `ResolvedRecoveredOuterCarrierSupply D S …` — the single carrier-membership leaf;
* `.toRecoveredOuterMem` — body-153's `recoveredOuter_mem`.

Toolkit body (like body-137).  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-159 — the recovered-outer carrier-membership leaf.**  The single fact that the assembled recovered
outer forest lies in `D.carrier G` — the carrier-closure leaf for the outer-mixing bijection, parallel to
`selectedOuter_mem` (body-128). -/
structure ResolvedRecoveredOuterCarrierSupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D)
    (leftResidual rightRecovered forestRecovered :
      ∀ {G : ResolvedFeynmanGraph}, ForestBlockCodType D G → ResolvedAdmissibleSubgraph G)
    (hcross_lr : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
      ∀ γ ∈ (leftResidual z).elements, ∀ δ ∈ (rightRecovered z).elements, γ ≠ δ → γ.Disjoint δ)
    (hcross_lrf : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
      ∀ γ ∈ ((leftResidual z).union (rightRecovered z) (hcross_lr z)).elements,
      ∀ δ ∈ (forestRecovered z).elements, γ ≠ δ → γ.Disjoint δ) where
  /-- The assembled recovered outer forest lies in the carrier (the carrier-closure leaf). -/
  recovered_outer_mem : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    ((leftResidual z).union (rightRecovered z) (hcross_lr z)).union (forestRecovered z) (hcross_lrf z)
      ∈ D.carrier G

/-- **R-6c-body-159 — body-153's `recoveredOuter_mem` from the carrier leaf.** -/
theorem ResolvedRecoveredOuterCarrierSupply.toRecoveredOuterMem
    {S : ResolvedConcreteSummandBundleSupply D}
    {leftResidual rightRecovered forestRecovered :
      ∀ {G : ResolvedFeynmanGraph}, ForestBlockCodType D G → ResolvedAdmissibleSubgraph G}
    {hcross_lr : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
      ∀ γ ∈ (leftResidual z).elements, ∀ δ ∈ (rightRecovered z).elements, γ ≠ δ → γ.Disjoint δ}
    {hcross_lrf : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
      ∀ γ ∈ ((leftResidual z).union (rightRecovered z) (hcross_lr z)).elements,
      ∀ δ ∈ (forestRecovered z).elements, γ ≠ δ → γ.Disjoint δ}
    (C : ResolvedRecoveredOuterCarrierSupply D S leftResidual rightRecovered forestRecovered
      hcross_lr hcross_lrf)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) :
    ((leftResidual z).union (rightRecovered z) (hcross_lr z)).union (forestRecovered z) (hcross_lrf z)
      ∈ D.carrier G :=
  C.recovered_outer_mem z

end GaugeGeometry.QFT.Combinatorial
