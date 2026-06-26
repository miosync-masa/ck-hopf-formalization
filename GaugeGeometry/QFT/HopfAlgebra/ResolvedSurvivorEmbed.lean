import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductSupply

/-!
# R-6c-heart-6a-1 — the survivor re-embedding (same-data subgraph + generator equality)

**Scout decision (survivor vs remnant embeddings):**

* **Right survivor** (`choiceAt γ = Sum.inl false`): `γ` is disjoint from the selected outer forest
  (`isRightPrimitive_disjoint_selectedOuterRaw`, 5b-2a), so after contracting the selected outer it
  **survives untouched** — same vertices/edges/legs, retargeted trivially (the retarget is the identity
  off the contracted region).  So the survivor component is just `γ`'s data **re-embedded** into the
  quotient graph; its generator is literally `γ`'s generator (same intrinsic graph).  **Concrete** modulo
  the three support facts (`vertices ⊆`, `internalEdges ≤`, `externalLegs ≤` of the quotient graph),
  which follow from disjointness + the retarget-is-identity-off-`Aout` lemmas.
* **Remnant** (`choiceAt γ = Sum.inr B`): `B` lives *inside* `γ ⊆ A'`, so after contracting `A'` it
  becomes a genuine **de-contraction** remnant (the `localizeRemnantComponent` machinery) — heavier,
  stays a supply for now.

This file lands the survivor engine, valid for **any** target graph `H` (the re-embedding is purely
structural): a subgraph's data, reinterpreted in `H` given the three support facts, has the **same
intrinsic graph and the same resolved generator**.

Landed:

* `ResolvedFeynmanSubgraph.reembed` — `γ`'s data as a subgraph of `H` (support facts supplied);
* `reembed_toResolvedFeynmanGraph` — the intrinsic graph is unchanged (`rfl`);
* `resolvedComponentGen_reembed` — the generator is unchanged (`rfl`, CD proof irrelevant).

No facade, no flat term, no `forgetHopf`, no rep/perm.  The support-fact discharge (from disjointness)
and the remnant de-contraction are the remaining work.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

/-- **R-6c-heart-6a-1 — re-embed a subgraph's data into another graph.**  Given that `γ`'s vertices /
internal edges / external legs already sit inside `H`, reinterpret `γ` as a subgraph of `H` with the
**same data** (the `edges_supported` / `legs_supported` facts are about `γ`'s own vertices, unchanged). -/
def ResolvedFeynmanSubgraph.reembed {G H : ResolvedFeynmanGraph} (γ : ResolvedFeynmanSubgraph G)
    (hv : γ.vertices ⊆ H.vertices) (hi : γ.internalEdges ≤ H.internalEdges)
    (hl : γ.externalLegs ≤ H.externalLegs) : ResolvedFeynmanSubgraph H where
  vertices := γ.vertices
  internalEdges := γ.internalEdges
  externalLegs := γ.externalLegs
  vertices_subset := hv
  internalEdges_le := hi
  externalLegs_le := hl
  edges_supported := γ.edges_supported
  legs_supported := γ.legs_supported

@[simp] theorem ResolvedFeynmanSubgraph.reembed_vertices {G H : ResolvedFeynmanGraph}
    (γ : ResolvedFeynmanSubgraph G) (hv : γ.vertices ⊆ H.vertices)
    (hi : γ.internalEdges ≤ H.internalEdges) (hl : γ.externalLegs ≤ H.externalLegs) :
    (γ.reembed hv hi hl).vertices = γ.vertices := rfl

/-- The re-embedding has the same intrinsic resolved graph (same data). -/
@[simp] theorem ResolvedFeynmanSubgraph.reembed_toResolvedFeynmanGraph {G H : ResolvedFeynmanGraph}
    (γ : ResolvedFeynmanSubgraph G) (hv : γ.vertices ⊆ H.vertices)
    (hi : γ.internalEdges ≤ H.internalEdges) (hl : γ.externalLegs ≤ H.externalLegs) :
    (γ.reembed hv hi hl).toResolvedFeynmanGraph = γ.toResolvedFeynmanGraph := rfl

/-- The re-embedding has the same intrinsic flat graph (the seed for the generator equality). -/
theorem ResolvedFeynmanSubgraph.reembed_forget_toFeynmanGraph {G H : ResolvedFeynmanGraph}
    (γ : ResolvedFeynmanSubgraph G) (hv : γ.vertices ⊆ H.vertices)
    (hi : γ.internalEdges ≤ H.internalEdges) (hl : γ.externalLegs ≤ H.externalLegs) :
    (γ.reembed hv hi hl).forget.toFeynmanGraph = γ.forget.toFeynmanGraph := rfl

/-- **R-6c-heart-6a-1 — re-embedding preserves the component generator.**  The re-embedded subgraph has
the same intrinsic resolved graph, so its generator (the graph's resolved class, CD proof irrelevant) is
`γ`'s generator — the survivor generator equality. -/
theorem resolvedComponentGen_reembed {G H : ResolvedFeynmanGraph} (γ : ResolvedFeynmanSubgraph G)
    (hv : γ.vertices ⊆ H.vertices) (hi : γ.internalEdges ≤ H.internalEdges)
    (hl : γ.externalLegs ≤ H.externalLegs)
    (hCD : (γ.reembed hv hi hl).forget.IsConnectedDivergent)
    (hCD' : γ.forget.IsConnectedDivergent) :
    resolvedComponentGen (γ.reembed hv hi hl) hCD = resolvedComponentGen γ hCD' := rfl

end GaugeGeometry.QFT.Combinatorial
