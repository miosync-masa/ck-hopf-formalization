import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocComponentNonempty

/-!
# R-6c-body-236 — `HasNonemptyComponents` for any resolved forest, from `cd_nonempty` (PROVED)

Two-hundred-and-thirty-sixth genuine-body step — the first `IsProperForest` conjunct grounded for the membership
certificates (body-232/233).  Body-235's scout ranked `HasNonemptyComponents` as the conjunct that falls first, and
cleanest as a *generic* per-carrier lemma: every component of any `ResolvedAdmissibleSubgraph` is connected-divergent
(the `isConnectedDivergent` structure field), and `cd_nonempty` (body-1's supplied measure fact) turns that into
vertex-nonemptiness.  So the lemma is universal — one proof discharges the conjunct for `selectedOuterRawOf s`, for the
region union, and for every future construction, with no `union` / `mem_union` bookkeeping.

## The lemma

```lean
hasNonemptyComponents_of_cdNonempty
  (N : ResolvedConnectedDivergentNonemptySupply G) (A : ResolvedAdmissibleSubgraph G) :
  A.HasNonemptyComponents
```

`HasNonemptyComponents A = ∀ γ ∈ A.elements, γ.IsNonempty` (`ResolvedSubGraph.lean:159`); `γ.IsNonempty =
0 < γ.vertexCount = 0 < γ.vertices.card` (`:85/:82`).  For `γ ∈ A.elements`, `A.isConnectedDivergent γ hγ`
(`:136`) gives `γ.forget.IsConnectedDivergent`, and `N.cd_nonempty` (`ComponentNonempty.lean:45`) gives
`γ.vertices.Nonempty`, whose `.card_pos` is exactly `0 < γ.vertices.card`.

Per the HALT: only this conjunct is proved — no `IsNonempty`, no positive-internal-edges, no `complementEdges`, no
certificate is assembled.  No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {G : ResolvedFeynmanGraph}

set_option linter.unusedSectionVars false

/-- **R-6c-body-236 — `HasNonemptyComponents` for any resolved forest.**  Every component is connected-divergent
(`isConnectedDivergent` field), so `cd_nonempty` gives it nonempty vertices — universal, no piece-specific fact. -/
theorem hasNonemptyComponents_of_cdNonempty (N : ResolvedConnectedDivergentNonemptySupply G)
    (A : ResolvedAdmissibleSubgraph G) : A.HasNonemptyComponents := by
  intro γ hγ
  exact (N.cd_nonempty γ (A.isConnectedDivergent γ hγ)).card_pos

end GaugeGeometry.QFT.Combinatorial
