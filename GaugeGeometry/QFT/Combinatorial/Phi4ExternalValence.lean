import GaugeGeometry.QFT.Combinatorial.ExternalBoundaryContraction

/-!
# QFT-R1-body-561 — the φ⁴ superficial-degree numerical kernel (instance-free)

The correct numerical core of the `φ⁴₄` superficial degree, built as **plain functions** — no
`DivergenceMeasure` instance is created (that is body-562).

## The boundary correction — `rigidify before quotient`, again

For an *arbitrary* subgraph `γ ⊆ G` the physical number of external lines of `γ` is **not**
`γ.externalLegCount` (the ambient external legs already attached to `γ`); it is

```text
Eγ = γ.externalLegCount + γ.boundaryEdgeCount
```

where `boundaryEdges` are the ambient *internal* edges cut by `∂γ` (exactly one endpoint inside `γ`),
each contributing one induced external line.  `SubGraph.lean` states this directly: `externalLegCount`
is "the number of ambient external legs attached to the subgraph", while `boundaryEdges` "play the role
of additional external legs of `γ` induced by the ambient graph".

Body-559 is therefore correct as stated: it preserved the external boundary **of the ambient `G` and of
the quotient `G/γ`** — both *full graphs*, whose induced boundary is empty (Step 2 below).  A φ⁴ measure
on an *arbitrary* subgraph must add the induced boundary; forgetting the cut edges before counting
external lines is the same trap as forgetting to rigidify before quotienting.  Two bodies into the QFT
phase, the same principle recurs.

## Contents

* Step 1 `physicalExternalLegCount` — `externalLegCount + boundaryEdgeCount`.
* Step 2 self-normalization — a full self-subgraph has no complement edges, hence no boundary edges, so
  its physical valence is just `G.externalLegs.card`.  Shallow multiset algebra (`tsub_self`,
  `filter_zero`), no membership / injectivity argument.
* Step 3 `phi4SuperficialDegree := 4 - Eγ` (in `ℤ`) with its self-normalization and a nonnegativity
  decision lemma.
* Step 4 single-contraction invariance **on full graphs**: `ωφ4(G/γ) = ωφ4(G)`, via body-559's
  `contract_externalLegCount_eq_ambient`.
* Step 5 forest analogue, via body-559's `contractWithStars_externalLegCount_eq_ambient`.

Per the HALT: no `DivergenceMeasure` instance is defined/instantiated (Steps 4–5 only *assume* the
`[∀ G, DivergenceMeasure G]` binder that body-559's count lemmas carry — an assumption, not an
instance); ZERO new `class`/`structure`/`instance`; `IsDivergencePreservedByContract` is unused;
`γ.externalLegCount` alone is **never** called `Eγ`; no arbitrary nested-subgraph contraction invariance
is claimed (only the full-graph equality); no quartic-vertex relation is re-proved; the
coproduct/coassociativity/final theorem are not edited; 1PI/connectedness/properness are unused;
`boundaryEdges` multiplicity is not collapsed to membership-only; the HopfAlgebra layer is not imported.
-/

namespace GaugeGeometry.QFT.Combinatorial

set_option linter.unusedSectionVars false

-- Steps 1–3 are genuinely measure-free (the `[∀ G, DivergenceMeasure G]` binder is introduced only
-- below, right before Steps 4–5, which reuse body-559's count lemmas).
variable {G : FeynmanGraph}

/-! ## Step 1 — the physical external valence of a subgraph -/

/-- **R-6c-QFT-R1-body-561 — physical external valence `Eγ`.**  The ambient external legs attached to
`γ` *plus* the ambient internal edges cut by `∂γ` (each a one-endpoint-inside boundary edge, hence one
induced external line).  This — not `externalLegCount` alone — is the `φ⁴` external-line count of a
subgraph. -/
def FeynmanSubgraph.physicalExternalLegCount {G : FeynmanGraph} (γ : FeynmanSubgraph G) : Nat :=
  γ.externalLegCount + γ.boundaryEdgeCount

/-! ## Step 2 — self-subgraph boundary normalization -/

/-- A full self-subgraph has no complement edges: `G.internalEdges - G.internalEdges = 0`. -/
theorem FeynmanSubgraph.self_complementEdges (hWF : G.WellFormed) :
    (FeynmanSubgraph.self G hWF).complementEdges = 0 := by
  unfold FeynmanSubgraph.complementEdges
  show G.internalEdges - G.internalEdges = 0
  exact tsub_self _

/-- Hence a full self-subgraph has no boundary-crossing edges. -/
theorem FeynmanSubgraph.self_boundaryEdges (hWF : G.WellFormed) :
    (FeynmanSubgraph.self G hWF).boundaryEdges = 0 := by
  unfold FeynmanSubgraph.boundaryEdges
  rw [FeynmanSubgraph.self_complementEdges hWF, Multiset.filter_zero]

/-- Boundary-edge count of a full self-subgraph is `0`. -/
theorem FeynmanSubgraph.self_boundaryEdgeCount (hWF : G.WellFormed) :
    (FeynmanSubgraph.self G hWF).boundaryEdgeCount = 0 := by
  unfold FeynmanSubgraph.boundaryEdgeCount
  rw [FeynmanSubgraph.self_boundaryEdges hWF, Multiset.card_zero]

/-- **R-6c-QFT-R1-body-561 — self physical valence.**  With no induced boundary, the physical external
valence of a full self-subgraph is exactly `G.externalLegs.card`. -/
theorem FeynmanSubgraph.self_physicalExternalLegCount (hWF : G.WellFormed) :
    (FeynmanSubgraph.self G hWF).physicalExternalLegCount = G.externalLegs.card := by
  unfold FeynmanSubgraph.physicalExternalLegCount FeynmanSubgraph.externalLegCount
  rw [FeynmanSubgraph.self_boundaryEdgeCount hWF, Nat.add_zero]
  rfl

/-! ## Step 3 — the φ⁴ superficial degree function -/

/-- **R-6c-QFT-R1-body-561 — φ⁴ superficial degree.**  `ωφ4(γ) = 4 − Eγ` in `ℤ`, with `Eγ` the physical
external valence.  A *pure function*: no `DivergenceMeasure` instance. -/
def FeynmanSubgraph.phi4SuperficialDegree {G : FeynmanGraph} (γ : FeynmanSubgraph G) : Int :=
  4 - (γ.physicalExternalLegCount : Int)

/-- **R-6c-QFT-R1-body-561 — self degree.**  `ωφ4` of a full self-subgraph is `4 − |G.externalLegs|`. -/
theorem FeynmanSubgraph.phi4SuperficialDegree_self (hWF : G.WellFormed) :
    (FeynmanSubgraph.self G hWF).phi4SuperficialDegree = 4 - (G.externalLegs.card : Int) := by
  unfold FeynmanSubgraph.phi4SuperficialDegree
  rw [FeynmanSubgraph.self_physicalExternalLegCount hWF]

/-- **R-6c-QFT-R1-body-561 — divergence decision.**  `γ` is φ⁴-superficially (non-strictly) divergent
iff its physical valence is at most `4`. -/
theorem FeynmanSubgraph.phi4SuperficialDegree_nonneg_iff (γ : FeynmanSubgraph G) :
    0 ≤ γ.phi4SuperficialDegree ↔ γ.physicalExternalLegCount ≤ 4 := by
  unfold FeynmanSubgraph.phi4SuperficialDegree
  omega

/-! ## Step 4 — full-graph contraction invariance of the degree -/

-- Steps 4–5 reuse body-559's count lemmas, which carry an *assumed* `[∀ G, DivergenceMeasure G]`
-- binder; it is assumed here (never defined / instantiated).
variable [∀ G : FeynmanGraph, DivergenceMeasure G]

/-- **R-6c-QFT-R1-body-561 — φ⁴ degree is preserved by single star-contraction on full graphs.**
`ωφ4(G/γ) = ωφ4(G)`, from body-559's external-leg-count preservation.  This is the **full-graph**
equality only — *not* a claim about arbitrary nested subgraphs. -/
theorem FeynmanSubgraph.phi4SuperficialDegree_contract_self_eq
    (hGWF : G.WellFormed) (γ : FeynmanSubgraph G) :
    (FeynmanSubgraph.self γ.contract
        (FeynmanSubgraph.wellFormed_contract hGWF)).phi4SuperficialDegree
      = (FeynmanSubgraph.self G hGWF).phi4SuperficialDegree := by
  rw [FeynmanSubgraph.phi4SuperficialDegree_self, FeynmanSubgraph.phi4SuperficialDegree_self,
      FeynmanSubgraph.contract_externalLegCount_eq_ambient]

/-! ## Step 5 — forest analogue -/

/-- **R-6c-QFT-R1-body-561 — φ⁴ degree is preserved by admissible-forest star-contraction on full
graphs.**  `ωφ4(G/A) = ωφ4(G)`, from body-559's forest external-leg-count preservation.  Full-graph
equality only.  The quotient well-formedness is taken as a hypothesis (contraction well-formedness is
not re-derived here). -/
theorem FeynmanSubgraph.phi4SuperficialDegree_contractWithStars_self_eq
    (hGWF : G.WellFormed) (A : AdmissibleSubgraph G)
    (starOf : FeynmanSubgraph G → VertexId)
    (hQWF : (A.contractWithStars starOf).WellFormed) :
    (FeynmanSubgraph.self (A.contractWithStars starOf) hQWF).phi4SuperficialDegree
      = (FeynmanSubgraph.self G hGWF).phi4SuperficialDegree := by
  rw [FeynmanSubgraph.phi4SuperficialDegree_self, FeynmanSubgraph.phi4SuperficialDegree_self,
      AdmissibleSubgraph.contractWithStars_externalLegCount_eq_ambient]

end GaugeGeometry.QFT.Combinatorial
