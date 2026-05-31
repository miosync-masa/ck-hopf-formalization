import GaugeGeometry.QFT.Combinatorial.FeynmanGraphs
import GaugeGeometry.QFT.Combinatorial.SupportGraph
import GaugeGeometry.QFT.Combinatorial.SubGraph

/-!
# Connected Feynman graphs (subtype)

This file introduces `ConnectedFeynmanGraph`, the subtype of
`FeynmanGraph` carrying a witness of `IsSupportConnected`. It serves as
the carrier on which the Connes–Kreimer Hopf-algebra well-founded
recursion (`coproductGen`, `antipodeGen`) is defined, because:

* `loopNumber : FeynmanGraph → Int` can be negative for disconnected
  forests (`E < V - 1`); on connected graphs it is non-negative
  (Euler inequality `V ≤ E + 1`, deferred as `H1.WF.0`).
* The recursive call inside `coproductGen` lands at `G.contract γ`,
  whose connectivity is supplied by H1.16
  (`IsConnected_contract_of_IsConnected`, `SubGraph.lean:747`).

The combination keeps the wf-recursion's domain closed under the
contraction step.

## Tag map (HOPF_DECOMPOSITION.md)

* `[Def]` `ConnectedFeynmanGraph` — H1.WF.1
* `[Def]` `ConnectedFeynmanGraph.contract` — derived from H1.16

## Convention

We use `IsSupportConnected` (not `IsConnected`) because:

* `FeynmanSubgraph.IsConnected` is itself defined as
  `γ.toFeynmanGraph.IsSupportConnected` (`SubGraph.lean:670`), so the
  whole Hopf chain already speaks support-level connectivity.
* H1.16 is stated for `IsSupportConnected`.
* `IsConnected` (built on `Adjacent`, which counts self-loops) and
  `IsSupportConnected` (built on `SupportAdj`, which does not) are
  inequivalent; the support-level notion is the one downstream lemmas
  expect.
-/

namespace GaugeGeometry.QFT.Combinatorial

namespace FeynmanGraph

/--
The subtype of `FeynmanGraph` carrying a witness of
`IsSupportConnected`. Sprint B' carrier for wf-recursion (H1.WF.1).
-/
def Connected : Type := { G : FeynmanGraph // G.IsSupportConnected }

end FeynmanGraph

/-- Top-level alias for `FeynmanGraph.Connected`, mirroring the
naming pattern of `FeynmanSubgraph` relative to `FeynmanGraph`. -/
abbrev ConnectedFeynmanGraph : Type := FeynmanGraph.Connected

namespace ConnectedFeynmanGraph

/-- The underlying graph of a `ConnectedFeynmanGraph`. -/
@[reducible] def toFeynmanGraph (G : ConnectedFeynmanGraph) : FeynmanGraph := G.val

/-- The connectivity witness packaged in a `ConnectedFeynmanGraph`. -/
theorem isSupportConnected (G : ConnectedFeynmanGraph) :
    G.toFeynmanGraph.IsSupportConnected := G.property

/-- Build a `ConnectedFeynmanGraph` from a graph and a connectivity
witness. -/
@[reducible] def mk' (G : FeynmanGraph) (h : G.IsSupportConnected) :
    ConnectedFeynmanGraph := ⟨G, h⟩

@[simp] theorem toFeynmanGraph_mk' (G : FeynmanGraph)
    (h : G.IsSupportConnected) :
    (mk' G h).toFeynmanGraph = G := rfl

/-! ### Accessors

Re-export the `FeynmanGraph` accessors as `simp` lemmas on the subtype
so that downstream proofs do not need to unfold `.val`/`.toFeynmanGraph`
manually.
-/

@[simp] theorem vertices_eq (G : ConnectedFeynmanGraph) :
    G.toFeynmanGraph.vertices = G.val.vertices := rfl

@[simp] theorem internalEdges_eq (G : ConnectedFeynmanGraph) :
    G.toFeynmanGraph.internalEdges = G.val.internalEdges := rfl

@[simp] theorem externalLegs_eq (G : ConnectedFeynmanGraph) :
    G.toFeynmanGraph.externalLegs = G.val.externalLegs := rfl

@[simp] theorem loopNumber_eq (G : ConnectedFeynmanGraph) :
    G.toFeynmanGraph.loopNumber = G.val.loopNumber := rfl

/-! ### Contraction lifted to the subtype

For the Hopf-algebra recursion we need a `contract` operation that
stays inside `ConnectedFeynmanGraph`. H1.16
(`IsConnected_contract_of_IsConnected`, `SubGraph.lean:747`) supplies
the connectivity of the contracted graph from the connectivity of `G`
and the nonemptiness of `γ`.

Note that `IsSupportConnected.toIsConnected` (`SupportGraph.lean:128`)
shows that `IsSupportConnected` implies the labelled-`IsConnected`,
but the converse can fail; we therefore keep the support-level notion
throughout.
-/

/--
Contract a connected `G` along a nonempty connected subgraph `γ`. The
result is a `ConnectedFeynmanGraph` by H1.16.

The `γ.IsConnected` hypothesis appears in H1.16's signature for
interface-matching with the design note; the actual proof in Sprint A
uses only `G.IsSupportConnected` and `γ.IsNonempty`. We retain it
here for downstream callers (`coproductGen`, `antipodeGen`) that
already have it from `IsConnectedDivergent`.
-/
def contract (G : ConnectedFeynmanGraph)
    (γ : FeynmanSubgraph G.toFeynmanGraph)
    (hγConn : γ.IsConnected) (hγNe : γ.IsNonempty) :
    ConnectedFeynmanGraph :=
  mk' γ.contract
    (FeynmanSubgraph.IsConnected_contract_of_IsConnected
      G.isSupportConnected hγConn hγNe)

@[simp] theorem contract_toFeynmanGraph
    (G : ConnectedFeynmanGraph)
    (γ : FeynmanSubgraph G.toFeynmanGraph)
    (hγConn : γ.IsConnected) (hγNe : γ.IsNonempty) :
    (G.contract γ hγConn hγNe).toFeynmanGraph = γ.contract := rfl

end ConnectedFeynmanGraph

end GaugeGeometry.QFT.Combinatorial
