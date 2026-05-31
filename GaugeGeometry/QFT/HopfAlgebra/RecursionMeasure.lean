import GaugeGeometry.QFT.HopfAlgebra.ConnectedFeynmanGraph

/-!
# Well-founded recursion measure for the Connes–Kreimer Hopf-algebra construction

This file provides the well-founded relation on `ConnectedFeynmanGraph`
used by `coproductGen` (H4.3) and `antipodeGen` (H6.1), plus a shared
recursion helper.

## Choice of measure: `internalEdgeCount`

We recurse on `internalEdgeCount` (the cardinality of the internal-edge
multiset) rather than `loopNumber.toNat`. The two grading choices are
not equivalent:

* `loopNumber = E - V + 1` (Connes–Kreimer 1998): non-negative on
  *connected* graphs only (Euler inequality `V ≤ E + 1`). Using
  `loopNumber.toNat` as a wf-measure forces a separate proof of
  non-negativity, which threads back through spanning-tree
  combinatorics. That proof is interesting in its own right but is
  *not on the critical path* for the Hopf-algebra construction.

* `internalEdgeCount = E`: trivially non-negative as a `Nat`. Strict
  decrease under contraction follows from H1.9
  (`internalEdgeCount_contract`: `γ.contract.E = (G.I - γ.I).card`)
  via `Multiset.card_sub` whenever `γ` carries at least one internal
  edge.

We adopt `internalEdgeCount`. The Connes–Kreimer loop-number grading
is recovered later as a graded structure on `HopfH` (independent
proposition; not required for the Hopf instance itself).

The "γ has ≥ 1 internal edge" hypothesis is satisfied by the index
set of the coproduct (`properConnectedDivergentSubgraphs`, defined in
H4.1) by construction: physically, divergent 1PI subgraphs with no
internal lines are excluded from the Connes–Kreimer sum.

## Tag map (HOPF_DECOMPOSITION.md)

* `[Def]` `edgeMeasure` — recursion measure
* `[Def]` `graphEdgeWFRel` — H1.WF.2 (analogue, on edge count)
* `[Comb]` `edgeMeasure_contract_lt` — H1.WF.3 (analogue)
* `[Def]` `edgeRecursion` — H1.WF.4 (shared recursor)

H1.WF.5 (Quotient lift to `FeynmanGraphClass`) is deferred to the
H2 file (`HopfGenSubtype.lean`) because it depends on the
`GraphIsomorphism` infrastructure imported there.
-/

namespace GaugeGeometry.QFT.Combinatorial

namespace ConnectedFeynmanGraph

/-- Recursion measure: the number of internal edges of the underlying
graph. Trivially `Nat`-valued, no Euler inequality required. -/
@[reducible] def edgeMeasure (G : ConnectedFeynmanGraph) : Nat :=
  G.toFeynmanGraph.internalEdgeCount

@[simp] theorem edgeMeasure_eq (G : ConnectedFeynmanGraph) :
    G.edgeMeasure = G.toFeynmanGraph.internalEdgeCount := rfl

/--
Well-founded relation on `ConnectedFeynmanGraph` via the
`edgeMeasure : Nat` projection. -/
@[reducible] def graphEdgeWFRel : WellFoundedRelation ConnectedFeynmanGraph :=
  invImage edgeMeasure Nat.lt_wfRel

instance : WellFoundedRelation ConnectedFeynmanGraph := graphEdgeWFRel

/--
**Analogue of H1.WF.3** — `edgeMeasure` strictly decreases under
contraction along a subgraph that carries at least one internal edge.

The proof is direct from H1.9 (`internalEdgeCount_contract`) plus
`Multiset.card_sub`, both established in Sprint A. No spanning-tree
argument is needed.

The `0 < γ.internalEdges.card` hypothesis is the natural Hopf-side
condition: the coproduct sum in H4.1 ranges only over subgraphs with
genuine internal structure.
-/
theorem edgeMeasure_contract_lt
    (G : ConnectedFeynmanGraph)
    (γ : FeynmanSubgraph G.toFeynmanGraph)
    (hConn : γ.IsConnected) (hNe : γ.IsNonempty)
    (hEdges : 0 < γ.internalEdges.card) :
    (G.contract γ hConn hNe).edgeMeasure < G.edgeMeasure := by
  -- Unfold to the underlying graph's `internalEdgeCount`.
  show γ.contract.internalEdgeCount < G.toFeynmanGraph.internalEdgeCount
  -- H1.9 expresses `γ.contract.E` as the cardinality of `G.I - γ.I`.
  rw [FeynmanSubgraph.internalEdgeCount_contract]
  -- `Multiset.card_sub` turns the multiset subtraction into Nat subtraction.
  have hle : γ.internalEdges ≤ G.toFeynmanGraph.internalEdges :=
    γ.internalEdges_le
  rw [Multiset.card_sub hle]
  -- Conclude via `omega` from `0 < γ.internalEdges.card` and
  -- `γ.internalEdges.card ≤ G.internalEdges.card`.
  have hCardLe : γ.internalEdges.card ≤ G.toFeynmanGraph.internalEdges.card :=
    Multiset.card_le_card hle
  show G.toFeynmanGraph.internalEdges.card - γ.internalEdges.card <
    G.toFeynmanGraph.internalEdgeCount
  unfold FeynmanGraph.internalEdgeCount
  omega

/--
**Analogue of H1.WF.4** — Shared recursor for `ConnectedFeynmanGraph`
driven by `edgeMeasure`. Both `coproductGen` (H4.3) and `antipodeGen`
(H6.1) are defined via this single recursion structure to avoid
duplicating `termination_by` clauses.
-/
def edgeRecursion
    {motive : ConnectedFeynmanGraph → Sort*}
    (step : ∀ G, (∀ G', G'.edgeMeasure < G.edgeMeasure → motive G') →
      motive G) :
    ∀ G, motive G :=
  fun G => step G (fun G' _ => edgeRecursion step G')
termination_by G => G.edgeMeasure
decreasing_by
  rename_i hLt
  exact hLt

end ConnectedFeynmanGraph

end GaugeGeometry.QFT.Combinatorial
