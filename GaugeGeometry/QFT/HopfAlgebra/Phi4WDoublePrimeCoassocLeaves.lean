import GaugeGeometry.QFT.HopfAlgebra.Phi4WDoublePrimeCoproduct

/-!
# QFT-R1-body-593 — family W″ live-domain coassoc leaf ownership

The abstract W″ Δᵣ-coassoc terminus (bodies 440–556) is stated modulo three "measure" leaves that LOOK
like external φ⁴ physics:

```text
old Measure.cd_nonempty                over-broad: demands nonempty vertices of EVERY CD subgraph
old E.cd_positiveInternalEdges         over-broad: false for an arbitrary φ⁴ CD subgraph
old Measure.contract_preserves_CD      over-broad: demands CD preservation for EVERY admissible forest
```

But the ACTUAL coassoc domain is not "every CD subgraph" — it is the **live W″ carrier member**.  On that
domain all three collapse to structure the carrier already carries: the first two follow from
`IsProperForest` (which every carrier member satisfies), and the third is exactly the carrier supply's own
`hCD`.  So this body issues the minimal leaf owner keyed to the LIVE carrier, deriving the leaf facts with
**zero new physics or geometry**.

This does NOT yet declare "Measure/E GONE from the final coassoc" — that requires checking, during the
family re-key, that every consumer genuinely holds live carrier membership.  This body only establishes the
ownership: the leaves were never external φ⁴ physics; they were carrier-membership facts wearing an
over-broad API.

## Contents

* `ResolvedFamilyWDoublePrimeCoassocLeafSupply D Inv R` — a `Prop` structure (≤ 1 new structure) with two
  fields: `carrier_isProperForest` (every carrier member is a proper forest) and `contract_CD` (the
  canonical-star contraction of a carrier member is family-connected-divergent).
* Derived leaf facts: `component_isNonempty` / `component_vertices_card_pos` / `component_vertices_nonempty`
  / `component_internalEdges_card_pos` / `contract_isConnectedDivergentFor`.
* `phi4WDoublePrimeCoassocLeafSupply` — the φ⁴ inhabitant, from `mem_resolvedLegSaturatedIndexFor`
  (properness) + `phi4WDoublePrimeCanonicalSupply.hCD` (contraction CD).  Nothing else.

Per the HALT: the old `ResolvedMeasureLeafSupply` / `ResolvedConnectedDivergentPositiveInternalEdgesSupply`
are NOT inhabited; no nonempty/positive claim about an arbitrary CD graph; no split choice / selectedOuter /
closure / alpha / coassoc; no target-membership circular derivation of properness; no flat descent; ≤ 1 new
`structure`, zero `class` / `instance`; zero forbidden divergence classes.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

/-! ## The live-domain leaf supply (one new `Prop` structure) -/

/-- **body-593 — the family W″ live-domain coassoc leaf supply.**  Keyed to the live carrier of a full
family supply `R`: every carrier member is a proper forest, and its canonical-star contraction is
family-connected-divergent.  These are precisely the (previously over-broad) "measure" leaves, restricted
to the actual coassoc domain — the live W″ carrier. -/
structure ResolvedFamilyWDoublePrimeCoassocLeafSupply
    (D : DivergenceMeasureFamily) (Inv : PermInvariantDivergenceMeasureFamily D)
    (R : ResolvedCanonicalCarrierProperSupplyFor D Inv) : Prop where
  /-- Every live carrier member is a proper forest. -/
  carrier_isProperForest :
    ∀ {G : ResolvedFeynmanGraph} {A : @ResolvedAdmissibleSubgraph D G},
      A ∈ (R.index G).carrier → @ResolvedAdmissibleSubgraph.IsProperForest D G A
  /-- The canonical-star contraction of a live carrier member is family-connected-divergent. -/
  contract_CD :
    ∀ {G : ResolvedFeynmanGraph} {A : @ResolvedAdmissibleSubgraph D G}
      (_hA : A ∈ (R.index G).carrier),
      ResolvedFeynmanGraphClass.IsConnectedDivergentFor D Inv
        (@ResolvedAdmissibleSubgraph.contractWithStars D G A (R.starOf G A)).toResolvedClass

namespace ResolvedFamilyWDoublePrimeCoassocLeafSupply

variable {D : DivergenceMeasureFamily} {Inv : PermInvariantDivergenceMeasureFamily D}
  {R : ResolvedCanonicalCarrierProperSupplyFor D Inv}

/-! ## Derived leaf facts (from `carrier_isProperForest` / `contract_CD`, zero new physics) -/

/-- **body-593 — old `Measure.cd_nonempty`, on the live domain.**  Every component of a live carrier member
is vertex-nonempty — from `HasNonemptyComponents` (an `IsProperForest` conjunct), NOT from a measure leaf. -/
theorem component_isNonempty (S : ResolvedFamilyWDoublePrimeCoassocLeafSupply D Inv R)
    {G : ResolvedFeynmanGraph} {A : @ResolvedAdmissibleSubgraph D G}
    (hA : A ∈ (R.index G).carrier)
    {γ : ResolvedFeynmanSubgraph G} (hγ : γ ∈ @ResolvedAdmissibleSubgraph.elements D G A) :
    γ.IsNonempty :=
  (@ResolvedAdmissibleSubgraph.hasNonemptyComponents_of_isProperForest D G A
    (S.carrier_isProperForest hA)) γ hγ

/-- **body-593 — component vertex `card > 0`** (`IsNonempty` unfolds to `0 < vertexCount = vertices.card`). -/
theorem component_vertices_card_pos (S : ResolvedFamilyWDoublePrimeCoassocLeafSupply D Inv R)
    {G : ResolvedFeynmanGraph} {A : @ResolvedAdmissibleSubgraph D G}
    (hA : A ∈ (R.index G).carrier)
    {γ : ResolvedFeynmanSubgraph G} (hγ : γ ∈ @ResolvedAdmissibleSubgraph.elements D G A) :
    0 < γ.vertices.card :=
  S.component_isNonempty hA hγ

/-- **body-593 — component vertices `Nonempty`.** -/
theorem component_vertices_nonempty (S : ResolvedFamilyWDoublePrimeCoassocLeafSupply D Inv R)
    {G : ResolvedFeynmanGraph} {A : @ResolvedAdmissibleSubgraph D G}
    (hA : A ∈ (R.index G).carrier)
    {γ : ResolvedFeynmanSubgraph G} (hγ : γ ∈ @ResolvedAdmissibleSubgraph.elements D G A) :
    γ.vertices.Nonempty :=
  Finset.card_pos.mp (S.component_vertices_card_pos hA hγ)

/-- **body-593 — old `E.cd_positiveInternalEdges`, on the live domain.**  Every component of a live carrier
member has `0 < internalEdges.card` — from `HasPositiveInternalEdgesComponents` (an `IsProperForest`
conjunct), NOT from a measure leaf. -/
theorem component_internalEdges_card_pos (S : ResolvedFamilyWDoublePrimeCoassocLeafSupply D Inv R)
    {G : ResolvedFeynmanGraph} {A : @ResolvedAdmissibleSubgraph D G}
    (hA : A ∈ (R.index G).carrier)
    {γ : ResolvedFeynmanSubgraph G} (hγ : γ ∈ @ResolvedAdmissibleSubgraph.elements D G A) :
    0 < γ.internalEdges.card :=
  (@ResolvedAdmissibleSubgraph.hasPositiveInternalEdgesComponents_of_isProperForest D G A
    (S.carrier_isProperForest hA)) γ hγ

/-- **body-593 — old `Measure.contract_preserves_CD`, on the live domain.**  The canonical-star contraction
of a live carrier member is family-connected-divergent — supplied by the carrier's own `hCD` (`contract_CD`
field), NOT by a measure leaf. -/
theorem contract_isConnectedDivergentFor (S : ResolvedFamilyWDoublePrimeCoassocLeafSupply D Inv R)
    {G : ResolvedFeynmanGraph} {A : @ResolvedAdmissibleSubgraph D G}
    (hA : A ∈ (R.index G).carrier) :
    ResolvedFeynmanGraphClass.IsConnectedDivergentFor D Inv
      (@ResolvedAdmissibleSubgraph.contractWithStars D G A (R.starOf G A)).toResolvedClass :=
  S.contract_CD hA

end ResolvedFamilyWDoublePrimeCoassocLeafSupply

/-! ## The φ⁴ inhabitant -/

/-- **body-593 — φ⁴ inhabits the live-domain leaf supply.**  `carrier_isProperForest` is the
`IsProperForest` conjunct of `mem_resolvedLegSaturatedIndexFor`; `contract_CD` is exactly
`phi4WDoublePrimeCanonicalSupply.hCD`.  No new physics, no new geometry — the "measure" leaves were carrier
membership all along. -/
theorem phi4WDoublePrimeCoassocLeafSupply :
    ResolvedFamilyWDoublePrimeCoassocLeafSupply phi4DivergenceMeasureFamily
      phi4PermInvariantDivergenceMeasureFamily phi4WDoublePrimeCanonicalSupply where
  carrier_isProperForest := by
    intro G A hA
    have hA' : A ∈ resolvedLegSaturatedIndexFor phi4DivergenceMeasureFamily
        phi4PermInvariantDivergenceMeasureFamily G := hA
    exact ((mem_resolvedLegSaturatedIndexFor phi4DivergenceMeasureFamily
      phi4PermInvariantDivergenceMeasureFamily G A).mp hA').2.2.2.2.1
  contract_CD := by
    intro G A hA
    exact phi4WDoublePrimeCanonicalSupply.hCD G A hA

end GaugeGeometry.QFT.Combinatorial
