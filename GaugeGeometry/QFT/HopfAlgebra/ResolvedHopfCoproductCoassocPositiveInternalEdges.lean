import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocHasNonemptyComponents

/-!
# R-6c-body-238 — `HasPositiveInternalEdgesComponents` for any resolved forest, from `cd_positiveInternalEdges` (PROVED)

Two-hundred-and-thirty-eighth genuine-body step — the second `IsProperForest` conjunct grounded for the membership
certificates (body-232/233), an exact clone of body-236.  Body-237's scout established that
`HasPositiveInternalEdgesComponents A = ∀ γ ∈ A.elements, 0 < γ.internalEdges.card` (`ResolvedSubGraph.lean:631`) is
NOT derivable from `IsConnectedDivergent` (`IsOnePI`'s bridge clause is vacuous on zero edges, `SupportGraph.lean:210`;
`IsDivergent` is `0 ≤ divergenceDegree`, an arbitrary `Int`), so it needs a measure-level supply — the sibling of
`cd_nonempty` (body-1).  With that supply, the conjunct is universal: one proof discharges it for `selectedOuterRawOf s`,
for the region union, and for every future construction.

## The supply and lemma

```lean
structure ResolvedConnectedDivergentPositiveInternalEdgesSupply (G) where
  cd_positiveInternalEdges : ∀ γ, γ.forget.IsConnectedDivergent → 0 < γ.internalEdges.card

hasPositiveInternalEdgesComponents_of_cdPositive
  (P : ResolvedConnectedDivergentPositiveInternalEdgesSupply G) (A : ResolvedAdmissibleSubgraph G) :
  A.HasPositiveInternalEdgesComponents
```

`γ.internalEdges : Multiset ResolvedFeynmanEdge` (`ResolvedSubGraph.lean:27`), so `γ.internalEdges.card` is
`Multiset.card`.  For `γ ∈ A.elements`, `A.isConnectedDivergent γ hγ` (`:138`) gives `γ.forget.IsConnectedDivergent`,
which `cd_positiveInternalEdges` turns into `0 < γ.internalEdges.card` — mirroring
`toInputOuterElementNonemptySupply` (`ComponentNonempty.lean:53`) and body-236 exactly.

Per the HALT: `cd_positiveInternalEdges` is the supplied measure-level obligation (not proved here); only this conjunct
is discharged — no aggregate `internalEdges.card` (#3), no `IsNonempty` (#4), no `complementEdges` (#5), no certificate
is assembled.  No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {G : ResolvedFeynmanGraph}

set_option linter.unusedSectionVars false

/-- **R-6c-body-238 — the CD-positive-internal-edges measure fact.**  Every connected-divergent subgraph has at least
one internal edge — a property of the divergence measure (not derivable from the abstract `DivergenceMeasure`, as
`IsOnePI`'s bridge clause is vacuous on zero edges).  The sibling of `cd_nonempty` (body-1). -/
structure ResolvedConnectedDivergentPositiveInternalEdgesSupply (G : ResolvedFeynmanGraph) where
  /-- A connected-divergent subgraph has a positive internal-edge count. -/
  cd_positiveInternalEdges : ∀ (γ : ResolvedFeynmanSubgraph G),
    γ.forget.IsConnectedDivergent → 0 < γ.internalEdges.card

/-- **R-6c-body-238 — `HasPositiveInternalEdgesComponents` for any resolved forest.**  Every component is
connected-divergent (`isConnectedDivergent` field), so `cd_positiveInternalEdges` gives it a positive internal-edge
count — universal, no piece-specific fact. -/
theorem hasPositiveInternalEdgesComponents_of_cdPositive
    (P : ResolvedConnectedDivergentPositiveInternalEdgesSupply G)
    (A : ResolvedAdmissibleSubgraph G) : A.HasPositiveInternalEdgesComponents := by
  intro γ hγ
  exact P.cd_positiveInternalEdges γ (A.isConnectedDivergent γ hγ)

end GaugeGeometry.QFT.Combinatorial
