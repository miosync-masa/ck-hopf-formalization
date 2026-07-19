import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocComponentOwnerCount
import GaugeGeometry.QFT.HopfAlgebra.BoundarySemanticCorrespondence

/-!
# R-6c-body-433 — the shared residual count transport (PROVED)

Four-hundred-and-thirty-third genuine-body step — banking the count equality both the right and forest region
exclusions turn on.  The quotient ambient's internal edges are, definitionally, the outer complement edges retargeted
(`contractWithStars_internalEdges`, a `rfl`); under `EdgeIdsUnique` the retarget is injective on those edges, so the
retarget transports occurrence counts *exactly*:

```text
count e outer.complementEdges = count (retargetEdge e) quotientAmbient.internalEdges     (retargetEdge e = e_q)
```

* `retargetEdge_injOn_complementEdges` — `A.retargetEdge` is `Set.InjOn` the complement edges (a submultiset of
  `G.internalEdges`), from the R-3a submultiset-injectivity engine `resolvedEdgeRetargetInjectiveOn` via the singleton
  trick;
* `count_complementEdges_eq_count_contractWithStars` — the residual count transport itself, `Multiset.count_map_eq_count`
  (the `InjOn` count-preservation lemma) applied through `contractWithStars_internalEdges`.

Both region exclusions (dedicated next bodies) will compose this with the owner lemma (body-432): the right survivor and
the forest quotient-edge preimage each map their `G`-level count of `e` onto the quotient count of `e_q`, which the
quotient complement positivity bounds `< count e_q quotientAmbient.internalEdges = count e outer.complementEdges`.

Per the HALT/guards: everything stays in `count` (no `∉`/nodup); `EdgeIdsUnique` is used ONLY as the retarget
injectivity (the existing `Ids` gate), transported to a count equality — NOT as a nodup datum.  No facade, no flat term,
no `forgetHopf`, no rep/perm, and NO strict `star_mapPerm` / `promote_collapse` / singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

set_option linter.unusedSectionVars false

namespace ResolvedAdmissibleSubgraph

variable {G : ResolvedFeynmanGraph}

/-- **R-6c-body-433 — the through-`A` edge retarget is injective on the complement edges.**  The complement is a
submultiset of `G.internalEdges`, so the R-3a engine `resolvedEdgeRetargetInjectiveOn` applies (singleton by singleton),
under `EdgeIdsUnique`. -/
theorem retargetEdge_injOn_complementEdges (hId : G.EdgeIdsUnique)
    (A : ResolvedAdmissibleSubgraph G) (starOf : ResolvedFeynmanSubgraph G → VertexId) :
    Set.InjOn (A.retargetEdge starOf) {x : ResolvedFeynmanEdge | x ∈ A.complementEdges} := by
  intro e₁ h₁ e₂ h₂ heq
  have h1G : ({e₁} : Multiset ResolvedFeynmanEdge) ≤ G.internalEdges :=
    Multiset.singleton_le.mpr (A.mem_internalEdges_of_mem_complementEdges h₁)
  have h2G : ({e₂} : Multiset ResolvedFeynmanEdge) ≤ G.internalEdges :=
    Multiset.singleton_le.mpr (A.mem_internalEdges_of_mem_complementEdges h₂)
  have hmap : ({e₁} : Multiset ResolvedFeynmanEdge).map
        (ResolvedFeynmanEdge.retarget (A.retargetVertex starOf))
      = ({e₂} : Multiset ResolvedFeynmanEdge).map
        (ResolvedFeynmanEdge.retarget (A.retargetVertex starOf)) := by
    simp only [Multiset.map_singleton]
    exact congrArg (fun x => ({x} : Multiset ResolvedFeynmanEdge)) heq
  exact Multiset.singleton_inj.mp
    (GaugeGeometry.QFT.HopfAlgebra.resolvedEdgeRetargetInjectiveOn G hId
      (A.retargetVertex starOf) h1G h2G hmap)

/-- **R-6c-body-433 ∎ — the residual count transport.**  An outer complement edge's count equals its retarget's count in
the quotient ambient — the exact count-map preservation under the `InjOn` retarget (`Multiset.count_map_eq_count`) applied
through the `rfl` identity `contractWithStars_internalEdges = complementEdges.map retargetEdge`. -/
theorem count_complementEdges_eq_count_contractWithStars (hId : G.EdgeIdsUnique)
    (A : ResolvedAdmissibleSubgraph G) (starOf : ResolvedFeynmanSubgraph G → VertexId)
    {e : ResolvedFeynmanEdge} (he : e ∈ A.complementEdges) :
    Multiset.count e A.complementEdges
      = Multiset.count (A.retargetEdge starOf e) (A.contractWithStars starOf).internalEdges := by
  rw [contractWithStars_internalEdges]
  exact (Multiset.count_map_eq_count (A.retargetEdge starOf) A.complementEdges
    (A.retargetEdge_injOn_complementEdges hId starOf) e he).symm

end ResolvedAdmissibleSubgraph

end GaugeGeometry.QFT.Combinatorial
