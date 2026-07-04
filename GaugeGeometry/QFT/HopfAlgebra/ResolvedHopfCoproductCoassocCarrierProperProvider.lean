import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocOuterNonemptyAdapter

/-!
# R-6c-body-137 — carrier-proper provider: `carrier_isProperForest` pinned as a base leaf

Hundred-and-thirty-seventh genuine-body step, a small base-side bank before the backward-reconstruction boss.  The
`carrier_isProperForest` obligation that recurs across the coassoc chain (bodies 96/113/130/131) is pinned to a
single named provider, with its exact status fixed: an **irreducible field for abstract `D`**, and a **theorem for
the canonical carrier** (via `ofFlatForest_isProperForest`).

## Why it is a field for abstract `D`

`ResolvedCoproductProperForestData` has fields `carrier` / `starOf` / `hCD` / `carrier_mapPerm` / `star_mapPerm` —
there is **no** proper-forest constraint on `carrier`.  So the carrier of a parametric `D` need not consist of
proper forests, and `carrier_isProperForest : ∀ G A, A ∈ D.carrier G → A.IsProperForest` is a genuine additional
primitive (the "ProperForest" in the data name is the intended discipline, not an enforced field).  It is the exact
`outer_nonempty` primitive (body-96): `IsProperForest A` has `A.elements.Nonempty` as its first conjunct
(`isNonempty_of_isProperForest`).

## Why it is a theorem for the canonical carrier

For the canonical payload carrier the carrier forests are `ofFlatForest`-lifts of the flat proper-forest index
`forestCoproductProperForestIndex`, and `ofFlatForest_isProperForest` (`ResolvedPayloadModel`) **proves**
`(ofFlatForest A hDisj).IsProperForest` (nonemptiness / positive-edges via carrier round-trips, complement
positivity via `internalEdges_le` + cardinality).  So a canonical `D` discharges `carrier_isProperForest` outright;
the abstract provider below is the field that a canonical instance fills by that theorem.

Per the HALT: the canonical `D` object is not built here (it is a whole payload model, remote from this file); the
provider is the theorem statement + adapters, with the canonical route named.  No measure / nonemptiness content is
mixed in — this is `carrier_isProperForest` only.

Landed:

* `ResolvedCarrierProperProvider D` — the single `carrier_isProperForest` leaf;
* `.toForestCarrierProperSupply` — into body-96's `ResolvedForestCarrierProperSupply` (→ `coassoc_gen`), given the
  genuine `forest_block` + the representative lift.

Toolkit body (like body-96), one base provider.  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-137 — the carrier-proper provider.**  The single base leaf `carrier_isProperForest` — the carrier
consists of proper forests.  Fielded for abstract `D`; provable (`ofFlatForest_isProperForest`) for the canonical
payload carrier. -/
structure ResolvedCarrierProperProvider (D : ResolvedCoproductProperForestData) where
  /-- Every carrier forest is a proper forest (the exact `outer_nonempty` primitive, body-96). -/
  carrier_isProperForest : ∀ (G : ResolvedFeynmanGraph) (A : ResolvedAdmissibleSubgraph G),
    A ∈ D.carrier G → A.IsProperForest

/-- **R-6c-body-137 — body-96's proper-forest carrier supply from the provider** (given the genuine forest
bijection and the representative lift).  Feeds `coassoc_gen` via body-96/95/…/88. -/
def ResolvedCarrierProperProvider.toForestCarrierProperSupply (P : ResolvedCarrierProperProvider D)
    (forest_block : ∀ (G : ResolvedFeynmanGraph),
      (∑ A ∈ (D.supply G).forestCarrier,
          ∑ p ∈ forestChoiceCarrier A,
            D.resolvedSplitChoiceTerm (⟨A, p⟩ : ResolvedCoassocSplitChoice D G))
        = ∑ A ∈ (D.supply G).forestCarrier,
            ∑ B ∈ (D.supply (A.1.contractWithStars (D.starOf G A.1))).forestCarrier,
              (D.supply G).leftTerm A ⊗ₜ[ℚ]
                ((D.supply (A.1.contractWithStars (D.starOf G A.1))).leftTerm B
                  ⊗ₜ[ℚ] (D.supply (A.1.contractWithStars (D.starOf G A.1))).rightTerm B))
    (rep : ResolvedHopfGen → ResolvedFeynmanGraph)
    (repCD : ∀ x : ResolvedHopfGen, (rep x).forget.toClass.IsConnectedDivergent)
    (rep_gen : ∀ x : ResolvedHopfGen, x = (rep x).toResolvedHopfGen (repCD x)) :
    ResolvedForestCarrierProperSupply D where
  carrier_isProperForest := P.carrier_isProperForest
  forest_block := forest_block
  rep := rep
  repCD := repCD
  rep_gen := rep_gen

end GaugeGeometry.QFT.Combinatorial
