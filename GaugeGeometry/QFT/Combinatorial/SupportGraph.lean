import GaugeGeometry.QFT.Combinatorial.FeynmanGraphs
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Support graph of a Feynman graph

The *support graph* of a combinatorial Feynman graph `G` is the underlying
`SimpleGraph VertexId` obtained by:

* dropping every self-loop internal edge, and
* collapsing parallel internal edges (i.e. replacing the multiset of internal
  edges by their underlying endpoint pair set).

This is the carrier of topological notions (reachability, connectedness,
spanning tree, connected components) that do **not** depend on multiplicities.
The multigraph content (loop number, superficial divergence, counterterms)
stays on the `FeynmanGraph` side.

In short:

* `FeynmanGraph.toSimpleGraph` is a *supporting functor* for connectivity,
  not the primary semantics of a Feynman graph.
* Multiplicity- and self-loop-sensitive constructions live on
  `FeynmanGraph`; pure topology lives on `FeynmanGraph.toSimpleGraph`.
-/

namespace GaugeGeometry.QFT.Combinatorial

namespace FeynmanGraph

/--
The support adjacency relation on vertices of `G`:
`u` and `v` are support-adjacent iff they are distinct and some internal
edge of `G` has them as its two endpoints (in either orientation).
Self-loops are discarded by the `u ≠ v` clause; parallel edges collapse
because the relation is existential.
-/
def SupportAdj (G : FeynmanGraph) (u v : VertexId) : Prop :=
  u ≠ v ∧ ∃ e ∈ G.internalEdges,
    (e.source = u ∧ e.target = v) ∨ (e.source = v ∧ e.target = u)

theorem SupportAdj.symm {G : FeynmanGraph} {u v : VertexId}
    (h : G.SupportAdj u v) : G.SupportAdj v u := by
  obtain ⟨hne, e, heG, hend⟩ := h
  refine ⟨hne.symm, e, heG, ?_⟩
  rcases hend with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · exact Or.inr ⟨hs, ht⟩
  · exact Or.inl ⟨hs, ht⟩

theorem SupportAdj.irrefl {G : FeynmanGraph} (v : VertexId) :
    ¬ G.SupportAdj v v := by
  intro h
  exact h.1 rfl

/--
The support `SimpleGraph` of `G`: self-loops are dropped and parallel
edges are collapsed. This is the carrier for topological notions
(reachability, connectedness, spanning tree, components).
-/
def toSimpleGraph (G : FeynmanGraph) : SimpleGraph VertexId where
  Adj := G.SupportAdj
  symm := fun _ _ h => h.symm
  loopless := ⟨fun v h => SupportAdj.irrefl v h⟩

@[simp] theorem toSimpleGraph_adj (G : FeynmanGraph) (u v : VertexId) :
    G.toSimpleGraph.Adj u v ↔ G.SupportAdj u v := Iff.rfl

/--
Support-level adjacency implies the labeled multigraph adjacency.
The converse fails in general: a self-loop gives `Adjacent v v` but
not `SupportAdj v v`.
-/
theorem SupportAdj.toAdjacent {G : FeynmanGraph} {u v : VertexId}
    (h : G.SupportAdj u v) : G.Adjacent u v :=
  h.2

/--
Labeled adjacency between *distinct* vertices coincides with support
adjacency. This is the precise sense in which the support graph keeps
all non-self-loop edge information.
-/
theorem adjacent_iff_supportAdj_of_ne {G : FeynmanGraph} {u v : VertexId}
    (hne : u ≠ v) : G.Adjacent u v ↔ G.SupportAdj u v := by
  refine ⟨?_, SupportAdj.toAdjacent⟩
  intro hAdj
  exact ⟨hne, hAdj⟩

/--
Support-level reachability: the reflexive-transitive closure of
`toSimpleGraph.Adj`, repackaged through mathlib's `SimpleGraph.Reachable`.
-/
def SupportReachable (G : FeynmanGraph) (u v : VertexId) : Prop :=
  G.toSimpleGraph.Reachable u v

theorem SupportReachable.refl (G : FeynmanGraph) (v : VertexId) :
    G.SupportReachable v v :=
  SimpleGraph.Reachable.refl _

theorem SupportReachable.symm {G : FeynmanGraph} {u v : VertexId}
    (h : G.SupportReachable u v) : G.SupportReachable v u :=
  SimpleGraph.Reachable.symm h

theorem SupportReachable.trans {G : FeynmanGraph} {u v w : VertexId}
    (h₁ : G.SupportReachable u v) (h₂ : G.SupportReachable v w) :
    G.SupportReachable u w :=
  SimpleGraph.Reachable.trans h₁ h₂

/--
Support-level connectedness of `G`: every pair of vertices lying in
`G.vertices` is support-reachable.

This is intentionally weaker than `SimpleGraph.Connected`, which would
require *every* vertex of the carrier type `VertexId := Nat` to be
reachable, a condition the support graph can never satisfy because
vertices outside `G.vertices` are isolated in `toSimpleGraph`.
-/
def IsSupportConnected (G : FeynmanGraph) : Prop :=
  ∀ ⦃u v⦄, u ∈ G.vertices → v ∈ G.vertices → G.SupportReachable u v

/--
If `G` is support-connected, then it is connected in the labeled sense
(`IsConnected`). The converse can fail because the labeled `Adjacent`
counts self-loops as adjacencies, which do not contribute to
`SupportAdj`.
-/
theorem IsSupportConnected.toIsConnected {G : FeynmanGraph}
    (h : G.IsSupportConnected) : G.IsConnected := by
  intro u v hu hv
  have hR : G.SupportReachable u v := h hu hv
  have hRT : Relation.ReflTransGen G.toSimpleGraph.Adj u v :=
    (SimpleGraph.reachable_iff_reflTransGen _ _).1 hR
  -- Transport `Relation.ReflTransGen G.toSimpleGraph.Adj` into
  -- `Relation.ReflTransGen G.Adjacent` using `SupportAdj.toAdjacent`.
  refine Relation.ReflTransGen.head_induction_on hRT ?_ ?_
  · exact Relation.ReflTransGen.refl
  · intro a b hab _ hbv
    exact Relation.ReflTransGen.head hab.toAdjacent hbv

/-!
### Support-level connected components

We reuse `SimpleGraph.ConnectedComponent` on `toSimpleGraph`. This gives
components over the whole carrier type `VertexId = Nat`; isolated
"ambient" vertices outside `G.vertices` each form their own singleton
component, which is the intended behaviour for the support-level
(topological) view.
-/

/--
The support-level connected component of a vertex in `G`.
Two vertices are in the same component iff they are support-reachable.
-/
abbrev SupportConnectedComponent (G : FeynmanGraph) :=
  G.toSimpleGraph.ConnectedComponent

/-- The support component of a vertex `v`. -/
def supportComponentOf (G : FeynmanGraph) (v : VertexId) :
    G.SupportConnectedComponent :=
  G.toSimpleGraph.connectedComponentMk v

theorem supportComponentOf_eq_iff {G : FeynmanGraph} (u v : VertexId) :
    G.supportComponentOf u = G.supportComponentOf v ↔ G.SupportReachable u v := by
  exact SimpleGraph.ConnectedComponent.eq

/-!
### Bridges

A *bridge* of `G` is an internal edge whose removal disconnects the
support graph. This is the standard one-particle-reducible witness used
by the 1PI predicate (H0.4).
-/

/--
H0.3 — An internal edge `e` of `G` is a **bridge** if it lies in
`G.internalEdges` and erasing one copy of it destroys support
connectedness.

Note: membership in `G.internalEdges` is required so that the
`Multiset.erase` in `eraseInternalEdge` actually removes something.
-/
def IsBridge (G : FeynmanGraph) (e : FeynmanEdge) : Prop :=
  e ∈ G.internalEdges ∧ ¬ (G.eraseInternalEdge e).IsSupportConnected

@[simp] theorem isBridge_def (G : FeynmanGraph) (e : FeynmanEdge) :
    G.IsBridge e ↔
      e ∈ G.internalEdges ∧ ¬ (G.eraseInternalEdge e).IsSupportConnected :=
  Iff.rfl

theorem IsBridge.mem_internalEdges {G : FeynmanGraph} {e : FeynmanEdge}
    (h : G.IsBridge e) : e ∈ G.internalEdges := h.1

theorem IsBridge.not_supportConnected_of_erase
    {G : FeynmanGraph} {e : FeynmanEdge} (h : G.IsBridge e) :
    ¬ (G.eraseInternalEdge e).IsSupportConnected := h.2

/-!
### One-particle-irreducibility (1PI)

A graph is **1PI** if it is support-connected and has no bridge: every
internal edge can be cut without disconnecting the support graph. This
is the index-set predicate of the Connes–Kreimer coproduct.
-/

/--
H0.4 — **1PI predicate**: `G` is support-connected and contains no
bridge.
-/
def IsOnePI (G : FeynmanGraph) : Prop :=
  G.IsSupportConnected ∧ ∀ e ∈ G.internalEdges, ¬ G.IsBridge e

@[simp] theorem isOnePI_def (G : FeynmanGraph) :
    G.IsOnePI ↔
      G.IsSupportConnected ∧ ∀ e ∈ G.internalEdges, ¬ G.IsBridge e :=
  Iff.rfl

/-- H0.5 — Projection: a 1PI graph is support-connected. -/
theorem IsOnePI.isSupportConnected {G : FeynmanGraph} (h : G.IsOnePI) :
    G.IsSupportConnected := h.1

/-- H0.6 — Projection: a 1PI graph has no bridge. -/
theorem IsOnePI.no_bridge {G : FeynmanGraph} (h : G.IsOnePI) :
    ∀ e ∈ G.internalEdges, ¬ G.IsBridge e := h.2

/-!
### Spanning trees on the support graph

A *support spanning tree* of `G` is a `SimpleGraph VertexId` that is
- contained in `G.toSimpleGraph` (it is a subgraph of the support),
- agrees with the support graph on vertex connectivity over `G.vertices`,
- is acyclic.

Because `VertexId = Nat` is the ambient carrier, we do not require the
tree to be connected on the full carrier; instead we require it to
preserve support reachability between vertices in `G.vertices`. This
matches the `IsSupportConnected` convention used throughout this file.
-/

/--
Support-level spanning-subgraph predicate: `T` is a subgraph of
`G.toSimpleGraph` and preserves support reachability between vertices
of `G.vertices`.
-/
structure IsSupportSpanningSubgraph (G : FeynmanGraph) (T : SimpleGraph VertexId)
    : Prop where
  le : T ≤ G.toSimpleGraph
  reachable_of_reachable :
    ∀ ⦃u v⦄, u ∈ G.vertices → v ∈ G.vertices →
      G.toSimpleGraph.Reachable u v → T.Reachable u v

/--
A *support spanning tree* of `G`: a spanning subgraph of `G.toSimpleGraph`
that is acyclic.
-/
structure IsSupportSpanningTree (G : FeynmanGraph) (T : SimpleGraph VertexId)
    : Prop extends IsSupportSpanningSubgraph G T where
  acyclic : T.IsAcyclic

/--
If `T` is a support spanning tree of `G`, then the restriction of `T`-reachability
to vertices of `G.vertices` coincides with support reachability.
-/
theorem IsSupportSpanningTree.reachable_iff
    {G : FeynmanGraph} {T : SimpleGraph VertexId}
    (hT : G.IsSupportSpanningTree T)
    {u v : VertexId} (hu : u ∈ G.vertices) (hv : v ∈ G.vertices) :
    T.Reachable u v ↔ G.SupportReachable u v := by
  refine ⟨fun h => ?_, fun h => hT.toIsSupportSpanningSubgraph.reachable_of_reachable hu hv h⟩
  exact h.mono hT.le

end FeynmanGraph

end GaugeGeometry.QFT.Combinatorial
