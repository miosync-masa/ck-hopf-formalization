import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocParentKeyLegIds

/-!
# R-6c-body-23 — parent leg-id separation scout: DECISION and vertex-key re-scope

Twenty-third genuine-body step, a sufficiency CHECKPOINT for body-22's `legIds_determine_parent` (another
"flat-false?" gate — better to know now).

## DECISION: leg-ids are INSUFFICIENT to separate parents

A forest component's external legs are a submultiset of the ambient legs (`γ.externalLegs ≤ G.externalLegs`),
and `IsConnectedDivergent = IsConnected ∧ IsOnePI ∧ IsDivergent` forces NONE of them to be nonempty.  So a
component can have an EMPTY external-leg multiset, and two distinct leg-empty components share the empty
leg-id key — `legIds_determine_parent` is then false for them.  (Leg-ids ARE globally unique where
`legIdsUnique` holds, but uniqueness does not help when the multiset is empty.)  Worse, when `B` is the whole
component (full contraction), the surviving legs/edges are all gone and ONLY the star remains, so no
id-channel *derived from legs or edges* can separate such parents.

## The true separating channel: surviving vertices + fresh stars

`contractedSourceGraph.vertices = (γ.vertices \ B.vertices) ∪ B.starVertices starOf` (body-20).  For the actual
occurrence family — the DISJOINT forest components of a fixed `s` — this is exactly what separates:

* the surviving part `γ.vertices \ B.vertices` are real `G`-vertex-ids lying in `γ.vertices`, and distinct
  components are pairwise vertex-DISJOINT, so nonempty-surviving parents are separated by vertices alone;
* stars are FRESH (`IsFreshStarAssignment`: `starOf γ ∉ G.vertices`, and distinct components get distinct
  stars, `IsFreshStarAssignment.eq_of_star_eq`), so a fully-contracted parent (empty surviving) is separated
  by its star.

Since fresh stars lie outside `G.vertices` while surviving vertices lie inside, equal contracted-vertex sets
force equal surviving sets AND equal star sets; disjointness then collapses both parents to the same
component.  So the separation rests on **forest-component disjointness + star freshness**, NOT on legs/edges.

## Re-scope: parentKey := the contracted-graph VERTEX set

We supersede body-22's leg-id key with the vertex key `parentVertexKey H := H.vertices`, reducing
`parentKey_inj` to `vertices_determine_parent` (contracted-vertex equality ⇒ parent graph equality).  Unlike
leg-ids, this key carries the star channel, so it is the honest sufficient candidate — its remaining content
is provable from the disjointness + freshness structural facts already in the codebase
(`IsFreshStarAssignment.eq_of_star_eq`), which is the natural next step.  The genuine de-contraction kernel is
thus **star traceability** (`D.starOf` distinguishes distinct parent components), not leg separation.

Per the HALT: no proof is forced (`vertices_determine_parent` fielded), no facade added, the finding is
recorded honestly.

Landed:

* `parentVertexKey : ResolvedFeynmanGraph → Finset VertexId` — the vertex key;
* `contractedSource_parentVertexKey` — its value on the contracted graph (surviving ∪ stars, from body-20);
* `ResolvedParentVertexSeparationSupply D G s` — `vertices_determine_parent`;
* `.toParentKeyRecoverySupply` — body-20's key supply at `parentVertexKey` (⟹ body-19/`parent_graph_inj`).

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-body-23 — the vertex parent key: a graph's vertex set** (carries the star channel that leg-ids
miss). -/
def parentVertexKey (H : ResolvedFeynmanGraph) : Finset VertexId := H.vertices

variable {s : ResolvedCoassocSplitChoice D G}

/-- **R-6c-body-23 — the vertex key of the contracted source graph: surviving parent vertices plus fresh
stars** (body-20). -/
theorem contractedSource_parentVertexKey (o : s.ForestChoiceOccurrence) :
    parentVertexKey o.contractedSourceGraph =
      (o.γ.1.toResolvedFeynmanGraph.vertices \ o.B.1.vertices) ∪
        o.B.1.starVertices (D.starOf o.γ.1.toResolvedFeynmanGraph o.B.1) :=
  o.contractedSourceGraph_vertices

/-- **R-6c-body-23 — the parent vertex-separation supply.**  The genuine remaining content: equal
contracted-vertex sets (surviving ∪ fresh stars) force equal parent intrinsic graphs — provable from forest
disjointness + star freshness. -/
structure ResolvedParentVertexSeparationSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph) (s : ResolvedCoassocSplitChoice D G) where
  /-- Equal contracted-source vertex sets force equal parent intrinsic graphs. -/
  vertices_determine_parent : ∀ o₁ o₂ : s.ForestChoiceOccurrence,
    o₁.contractedSourceGraph.vertices = o₂.contractedSourceGraph.vertices →
      o₁.γ.1.toResolvedFeynmanGraph = o₂.γ.1.toResolvedFeynmanGraph

/-- **R-6c-body-23 — body-20's key-recovery supply at the concrete vertex key.**  Composing with body-20's
`.toParentGraphInjectivitySupply` (and body-19's adapter) discharges `parent_graph_inj` / `parent_inj` down to
`vertices_determine_parent`. -/
def ResolvedParentVertexSeparationSupply.toParentKeyRecoverySupply
    (S : ResolvedParentVertexSeparationSupply D G s) :
    ResolvedParentKeyRecoverySupply D G s (Finset VertexId) where
  parentKey := parentVertexKey
  parentKey_inj := fun o₁ o₂ h => S.vertices_determine_parent o₁ o₂ h

end GaugeGeometry.QFT.Combinatorial
