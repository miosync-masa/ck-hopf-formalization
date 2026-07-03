import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocPureChoicePartition

/-!
# R-6c-body-96 — outer_nonempty adapter: the exact primitive is `carrier_isProperForest`

Ninety-sixth genuine-body step, pinning down body-95's `outer_nonempty` obligation.  The scout conclusion: it is
NOT suppliable from the measure leaf `cd_nonempty` / `component_nonempty`, and it IS exactly the natural carrier
property "every carrier forest is a proper forest" — which the canonical carrier satisfies by construction.

## Why `cd_nonempty` / `component_nonempty` do NOT suffice

`ResolvedInputOuterElementNonemptySupply.component_nonempty` (from `cd_nonempty`, body-1) says every component
`γ ∈ A.elements` has nonempty VERTICES.  That is a statement about each existing component — it says NOTHING
about whether `A.elements` has any component at all.  `outer_nonempty` needs `A.elements.Nonempty` (≥ 1
component), a strictly different fact.  Nor does the abstract `ResolvedCoproductProperForestData` force it: its
fields are `carrier` (an arbitrary `Finset`), `starOf`, `hCD` (the CONTRACTION is CD — and `contractWithStars ∅
= G` is CD, so `hCD` holds even for an empty forest), `carrier_mapPerm`, `star_mapPerm`.  None implies a carrier
element has a component.  So `outer_nonempty` is a genuine additional primitive.

## The exact primitive: `carrier_isProperForest`

`IsProperForest A = A.IsNonempty ∧ … ` with `A.IsNonempty = A.elements.Nonempty` (its FIRST conjunct,
`isNonempty_of_isProperForest`).  So the tightest natural primitive is `carrier_isProperForest : ∀ A ∈ carrier
G, A.IsProperForest` — "the carrier consists of proper forests" — from which `outer_nonempty` is immediate.  This
is the DEFINING property of a forest carrier, and the canonical carrier provides it: for a lift of a flat proper
forest, `ofFlatForest_isProperForest` (`ResolvedPayloadModel`) proves `IsProperForest`.  So `outer_nonempty` is
FREE for the canonical construction and only abstract `D` fields it here.

## The scaffold

`ResolvedForestCarrierProperSupply` fields `carrier_isProperForest` + the genuine `forest_block` + a
representative lift; `.toForestBlockSupply` discharges `outer_nonempty` (via `isNonempty_of_isProperForest`),
recovering body-95's supply; `.coassoc_gen` chains body-95/94/93/92/91/90/88.

Per the HALT: `component_nonempty` is confirmed NOT to imply forest-element nonemptiness; the exact primitive is
isolated as `carrier_isProperForest` (canonical-provable); `forest_block` is NOT entered; no star/retarget.

Landed:

* `ResolvedForestCarrierProperSupply D` — `carrier_isProperForest` + `forest_block` + representative lift;
* `.toForestBlockSupply` / `.coassoc_gen` — to body-95/94/93/92/91/90/88.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData}

set_option linter.unusedSectionVars false

/-- **R-6c-body-96 — the proper-forest carrier supply.**  `carrier_isProperForest` (the natural carrier
property "every carrier forest is a proper forest", provided by the canonical carrier via
`ofFlatForest_isProperForest`) + the genuine `forest_block` + a representative lift.  This is the tightest
isolation of body-95's `outer_nonempty`: it needs nothing about the divergence measure, only that the carrier
consists of proper forests. -/
structure ResolvedForestCarrierProperSupply (D : ResolvedCoproductProperForestData) where
  /-- Every carrier forest is a proper forest (canonical-provable; the exact `outer_nonempty` primitive). -/
  carrier_isProperForest : ∀ (G : ResolvedFeynmanGraph) (A : ResolvedAdmissibleSubgraph G),
    A ∈ D.carrier G → A.IsProperForest
  /-- The genuine nested-forest bijection: the forest block = the quotient-forest double sum. -/
  forest_block : ∀ (G : ResolvedFeynmanGraph),
      (∑ A ∈ (D.supply G).forestCarrier,
          ∑ p ∈ forestChoiceCarrier A,
            D.resolvedSplitChoiceTerm (⟨A, p⟩ : ResolvedCoassocSplitChoice D G))
        = ∑ A ∈ (D.supply G).forestCarrier,
            ∑ B ∈ (D.supply (A.1.contractWithStars (D.starOf G A.1))).forestCarrier,
              (D.supply G).leftTerm A ⊗ₜ[ℚ]
                ((D.supply (A.1.contractWithStars (D.starOf G A.1))).leftTerm B
                  ⊗ₜ[ℚ] (D.supply (A.1.contractWithStars (D.starOf G A.1))).rightTerm B)
  /-- A representative graph for each generator. -/
  rep : ResolvedHopfGen → ResolvedFeynmanGraph
  /-- The representative is connected-divergent. -/
  repCD : ∀ x : ResolvedHopfGen, (rep x).forget.toClass.IsConnectedDivergent
  /-- The representative's generator IS `x`. -/
  rep_gen : ∀ x : ResolvedHopfGen, x = (rep x).toResolvedHopfGen (repCD x)

/-- **R-6c-body-96 — body-95's forest-block supply from the proper-forest carrier.**  `outer_nonempty` is the
first conjunct of `IsProperForest` (`isNonempty_of_isProperForest`, `= elements.Nonempty`). -/
def ResolvedForestCarrierProperSupply.toForestBlockSupply
    (S : ResolvedForestCarrierProperSupply D) : ResolvedForestBlockSupply D where
  outer_nonempty := fun G A _ =>
    ResolvedAdmissibleSubgraph.isNonempty_of_isProperForest (S.carrier_isProperForest G A.1 A.2)
  forest_block := S.forest_block
  rep := S.rep
  repCD := S.repCD
  rep_gen := S.rep_gen

/-- **R-6c-body-96 — `coassoc_gen` from the proper-forest carrier** (via body-95/94/93/92/91/90/88). -/
theorem ResolvedForestCarrierProperSupply.coassoc_gen
    (S : ResolvedForestCarrierProperSupply D) (x : ResolvedHopfGen) :
    D.coassocLeft (MvPolynomial.X x) = D.coassocRight (MvPolynomial.X x) :=
  S.toForestBlockSupply.coassoc_gen x

end GaugeGeometry.QFT.Combinatorial
