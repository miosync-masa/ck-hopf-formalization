import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestCountBackbone

/-!
# R-6c-body-436 — the ambient retarget `InjOn` and the domain-widened count transport (PROVED)

Four-hundred-and-thirty-sixth genuine-body step — banking the two generic, `count`-safe transport tools the forest
region exclusion needs, isolating the touched↔whole alignment to a single `map_congr` at the point of use.

* `count_map_eq_count_of_injOn_mem` — a domain-widened version of `Multiset.count_map_eq_count`: if `f` is `InjOn` a set
  `S`, `s`'s elements lie in `S`, and `x ∈ S` (NOT necessarily `x ∈ s`), then `(s.map f).count (f x) = s.count x`.  This
  is exactly the transport that avoids assuming the witness edge lies in the preimage multiset: both the witness and every
  preimage element live in `G.internalEdges`, so the ambient `InjOn` over `G.internalEdges` closes the count equality.
* `retargetEdge_injOn_internalEdges` — the ambient upgrade of body-433's complement `InjOn`: `A.retargetEdge` is `InjOn`
  the whole `{e | e ∈ G.internalEdges}` (the R-3a engine on singletons under `EdgeIdsUnique`).

## The forest entanglement (accurately scoped for the transport that consumes these)

The forest parent's internal edges are `touchedOuterForest.internalEdges + quotientEdgePreimage (touchedOuterForest z δ)
(D.starOf …) (touchedLocalComponent z δ)` (body-435).  The clean transport `count e qEP = count (retargetEdge e)
δ.internalEdges` needs the retarget-vertex alignment `whole_touched_retargetEdge_eq`, whose endpoint obligations
`touched_edge_source_ok` / `touched_edge_target_ok` are keyed to `quotientEdgePreimage z.1.1 (D.starOf …) δ` (the WHOLE
outer), while the parent uses the `touchedOuterForest`-keyed preimage.  Reconciling the two preimages is where the forest
exclusion sits deeper than the right one: `quotientEdgePreimage_eq_occurrence_complement`
(`ParentInternalEdgesConcrete`) shows the parent's preimage is pinned to the occurrence source only through the
promotion/wiring value supplies (`StarProm` / `Wiring` / `promoted_retargetEdge_eq_inner`).  These two generic tools are
alignment-agnostic and correct regardless of that reconciliation; the transport body that consumes them will fix the
preimage-domain question and apply `whole_touched_retargetEdge_eq` under a single `Multiset.map_congr`.

Per the HALT/guards: everything stays in `count` (no `∉`); the ambient `InjOn` is the body-433 residual engine widened to
`G.internalEdges` (still not global); no forward-outer, identity, or cover.  No facade, no flat term, no `forgetHopf`, no
rep/perm, and NO strict `star_mapPerm` / `promote_collapse` / singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

/-- **R-6c-body-436 — the domain-widened `InjOn` count-map transport.**  `Multiset.count_map_eq_count` without the
`x ∈ s` hypothesis: an `InjOn` domain `S` containing both `s`'s support and `x` suffices. -/
theorem count_map_eq_count_of_injOn_mem {α β : Type*} [DecidableEq α] [DecidableEq β] {f : α → β}
    {s : Multiset α} {S : Set α} (hf : Set.InjOn f S) (hs : ∀ a ∈ s, a ∈ S)
    {x : α} (hx : x ∈ S) : (s.map f).count (f x) = s.count x := by
  by_cases hxs : x ∈ s
  · exact Multiset.count_map_eq_count f s (Set.InjOn.mono (fun a ha => hs a ha) hf) x hxs
  · rw [Multiset.count_eq_zero_of_notMem hxs, Multiset.count_eq_zero, Multiset.mem_map]
    rintro ⟨a, ha, hfa⟩
    exact hxs (hf (hs a ha) hx hfa ▸ ha)

namespace ResolvedAdmissibleSubgraph

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

set_option linter.unusedSectionVars false

variable {G : ResolvedFeynmanGraph}

/-- **R-6c-body-436 — the through-`A` retarget is `InjOn` the whole ambient internal edges.**  The ambient upgrade of
body-433's complement `InjOn`: singleton-by-singleton via the R-3a engine `resolvedEdgeRetargetInjectiveOn`, under
`EdgeIdsUnique`. -/
theorem retargetEdge_injOn_internalEdges (hId : G.EdgeIdsUnique)
    (A : ResolvedAdmissibleSubgraph G) (starOf : ResolvedFeynmanSubgraph G → VertexId) :
    Set.InjOn (A.retargetEdge starOf) {e : ResolvedFeynmanEdge | e ∈ G.internalEdges} := by
  intro e₁ h₁ e₂ h₂ heq
  have h1G : ({e₁} : Multiset ResolvedFeynmanEdge) ≤ G.internalEdges := Multiset.singleton_le.mpr h₁
  have h2G : ({e₂} : Multiset ResolvedFeynmanEdge) ≤ G.internalEdges := Multiset.singleton_le.mpr h₂
  have hmap : ({e₁} : Multiset ResolvedFeynmanEdge).map
        (ResolvedFeynmanEdge.retarget (A.retargetVertex starOf))
      = ({e₂} : Multiset ResolvedFeynmanEdge).map
        (ResolvedFeynmanEdge.retarget (A.retargetVertex starOf)) := by
    simp only [Multiset.map_singleton]
    exact congrArg (fun x => ({x} : Multiset ResolvedFeynmanEdge)) heq
  exact Multiset.singleton_inj.mp
    (GaugeGeometry.QFT.HopfAlgebra.resolvedEdgeRetargetInjectiveOn G hId
      (A.retargetVertex starOf) h1G h2G hmap)

end ResolvedAdmissibleSubgraph

end GaugeGeometry.QFT.Combinatorial
