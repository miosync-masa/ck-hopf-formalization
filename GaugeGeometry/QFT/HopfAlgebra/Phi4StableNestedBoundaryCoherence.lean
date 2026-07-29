import GaugeGeometry.QFT.HopfAlgebra.Phi4RootRelativeNestedBoundary
import GaugeGeometry.QFT.HopfAlgebra.Phi4WDoublePrimeRawSupply

/-!
# QFT-R1-body-598 — stable nested traceability + ID uniqueness + `mapPerm` coherence

Body-597 built the constructive repair of body-596's re-encoding no-go: the **stable** nested
boundary-completed graph `stableNestedBoundaryCompletedGraph γ δ` (inherited legs kept verbatim, fresh
root-boundary legs added once) is **raw-equal** to the single root completion of the root lift
`R := rootRelativeInner γ δ` (`stableNestedBoundaryCompletedGraph_eq`).

This body TRANSPORTS the body-589 traceability / ID-uniqueness machinery through that raw equality,
and proves the naturality of the whole construction under the identity-preserving vertex relabeling
`mapPerm σ`.  There is **no new ID arithmetic**: every uniqueness statement is body-589 applied to `R`
(whose ambient is the root `G`), gated by `G.EdgeIdsUnique` / `G.LegIdsUnique` through the raw equality;
every relabeling statement rides body-589's `boundaryCompletedResolvedGraph_mapPerm` and body-587's
`mapPermRFS` + saturation transport.  The headline `stableNestedBoundaryCompletedGraph_mapPerm` is a
**raw** `ResolvedFeynmanGraph` equality proved by a rewrite chain — no even/odd 4-way replay.

Multiplicity-safe throughout (`Multiset`, no `Finset`/dedup).  No family-CD; no `promote` /
selectedOuter / split-choice / quotient / alpha / forest-block / coassoc.  Zero new
`class`/`structure`/`instance`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical
open ResolvedFeynmanSubgraph

variable {G : ResolvedFeynmanGraph}

/-! ## Step 1 — the stable root-boundary leg view + its submultiset -/

/-- The freshly-induced root-boundary legs of the stable nested completion, viewed as the induced legs
of **all** of `R`'s resolved boundary edges (`R := rootRelativeInner γ δ`).  This is exactly the ODD
summand of `R.boundaryCompletedResolvedExternalLegs`. -/
noncomputable def stableNestedRootBoundaryLegs (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph) : Multiset ResolvedExternalLeg :=
  (rootRelativeInner γ δ).resolvedBoundaryEdges.map (rootRelativeInner γ δ).boundaryExternalLeg

/-- The root-boundary leg view is a designated submultiset of the stable nested completed legs (it is
the ODD `+`-summand of the single root completion, via body-597's `stableNestedResolvedExternalLegs_eq`).
NO odd-parity classification — pure `Multiset.le_add_left`. -/
theorem stableNestedRootBoundaryLegs_le (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph)
    (hγsat : ResolvedExternalLegSaturated G γ)
    (hδsat : ResolvedExternalLegSaturated γ.boundaryCompletedResolvedGraph δ) :
    stableNestedRootBoundaryLegs γ δ ≤ stableNestedResolvedExternalLegs γ δ := by
  rw [stableNestedResolvedExternalLegs_eq γ δ hγsat hδsat]
  unfold ResolvedFeynmanSubgraph.boundaryCompletedResolvedExternalLegs stableNestedRootBoundaryLegs
  exact Multiset.le_add_left _ _

/-! ## Step 2 — traceability + ID uniqueness (transport from body-589) -/

/-- **body-598 — the fresh root-boundary legs are traceable.**  Every fresh root-boundary leg comes from
a *unique* resolved boundary edge of `R := rootRelativeInner γ δ`, gated by the root `G.EdgeIdsUnique`.
This is body-589's `boundaryExternalLeg_traceable` applied to `R` (ambient `G`), no new arithmetic. -/
theorem stableNestedRootBoundaryLegs_traceable (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph) (hEdge : G.EdgeIdsUnique)
    {ℓ : ResolvedExternalLeg} (hℓ : ℓ ∈ stableNestedRootBoundaryLegs γ δ) :
    ∃! e, e ∈ (rootRelativeInner γ δ).resolvedBoundaryEdges
      ∧ (rootRelativeInner γ δ).boundaryExternalLeg e = ℓ := by
  unfold stableNestedRootBoundaryLegs at hℓ
  exact (rootRelativeInner γ δ).boundaryExternalLeg_traceable hEdge hℓ

/-- **body-598 — the stable nested completed graph has unique `edgeId`s.**  Internal edges are `δ`'s
(unchanged from ambient `G`); the raw equality with the single root completion of `R` transports
body-589's `boundaryCompletedResolvedGraph_edgeIdsUnique`. -/
theorem stableNestedBoundaryCompletedGraph_edgeIdsUnique (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph)
    (hγsat : ResolvedExternalLegSaturated G γ)
    (hδsat : ResolvedExternalLegSaturated γ.boundaryCompletedResolvedGraph δ)
    (hEdge : G.EdgeIdsUnique) :
    (stableNestedBoundaryCompletedGraph γ δ).EdgeIdsUnique := by
  rw [stableNestedBoundaryCompletedGraph_eq γ δ hγsat hδsat]
  exact (rootRelativeInner γ δ).boundaryCompletedResolvedGraph_edgeIdsUnique hEdge

/-- **body-598 — the stable nested completed graph has unique `legId`s.**  Via the raw equality with the
single root completion of `R`, this is body-589's `boundaryCompletedResolvedGraph_legIdsUnique` (EVEN
existing legs by `G.LegIdsUnique`, ODD induced legs by `G.EdgeIdsUnique`, cross by parity). -/
theorem stableNestedBoundaryCompletedGraph_legIdsUnique (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph)
    (hγsat : ResolvedExternalLegSaturated G γ)
    (hδsat : ResolvedExternalLegSaturated γ.boundaryCompletedResolvedGraph δ)
    (hLeg : G.LegIdsUnique) (hEdge : G.EdgeIdsUnique) :
    (stableNestedBoundaryCompletedGraph γ δ).LegIdsUnique := by
  rw [stableNestedBoundaryCompletedGraph_eq γ δ hγsat hδsat]
  exact (rootRelativeInner γ δ).boundaryCompletedResolvedGraph_legIdsUnique hLeg hEdge

/-! ## Step 3 — the nested `mapPerm` subgraph + saturation transport -/

/-- Transport a nested subgraph `δ` (of `H := γ.boundaryCompletedResolvedGraph`) to a nested subgraph of
`(γ.mapPerm σ).boundaryCompletedResolvedGraph`, via body-587's clean `mapPermRFS` over the body-589
boundary-completion/`mapPerm` commutation `boundaryCompletedResolvedGraph_mapPerm`. -/
noncomputable def mapPermNestedBoundarySubgraph (σ : Equiv.Perm VertexId)
    (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph) :
    ResolvedFeynmanSubgraph (γ.mapPerm σ).boundaryCompletedResolvedGraph :=
  mapPermRFS (boundaryCompletedResolvedGraph_mapPerm σ γ) δ

@[simp] theorem mapPermNestedBoundarySubgraph_vertices (σ : Equiv.Perm VertexId)
    (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph) :
    (mapPermNestedBoundarySubgraph σ γ δ).vertices = δ.vertices.image σ := by
  unfold mapPermNestedBoundarySubgraph; rw [mapPermRFS_vertices]

@[simp] theorem mapPermNestedBoundarySubgraph_internalEdges (σ : Equiv.Perm VertexId)
    (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph) :
    (mapPermNestedBoundarySubgraph σ γ δ).internalEdges
      = δ.internalEdges.map (ResolvedFeynmanEdge.map σ) := by
  unfold mapPermNestedBoundarySubgraph; rw [mapPermRFS_internalEdges]

@[simp] theorem mapPermNestedBoundarySubgraph_externalLegs (σ : Equiv.Perm VertexId)
    (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph) :
    (mapPermNestedBoundarySubgraph σ γ δ).externalLegs
      = δ.externalLegs.map (ResolvedExternalLeg.map σ) := by
  unfold mapPermNestedBoundarySubgraph; rw [mapPermRFS_externalLegs]

/-- External-leg saturation transports across the clean `mapPermRFS` over any ambient equality
`G₂ = G₁.mapPerm σ` (subst to body-587's instance-clean `mpFor_externalLegSaturated_iff`, using
`mapPermRFS rfl δ = δ.mapPerm σ` definitionally). -/
theorem resolvedExternalLegSaturated_mapPermRFS_iff {G₁ G₂ : ResolvedFeynmanGraph}
    {σ : Equiv.Perm VertexId} (hσ : G₂ = G₁.mapPerm σ) (δ : ResolvedFeynmanSubgraph G₁) :
    ResolvedExternalLegSaturated G₂ (mapPermRFS hσ δ) ↔ ResolvedExternalLegSaturated G₁ δ := by
  subst hσ
  exact mpFor_externalLegSaturated_iff σ δ

/-- The nested `mapPerm` subgraph is external-leg saturated whenever the source `δ` is. -/
theorem mapPermNestedBoundarySubgraph_saturated (σ : Equiv.Perm VertexId)
    (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph)
    (hδsat : ResolvedExternalLegSaturated γ.boundaryCompletedResolvedGraph δ) :
    ResolvedExternalLegSaturated (γ.mapPerm σ).boundaryCompletedResolvedGraph
      (mapPermNestedBoundarySubgraph σ γ δ) := by
  unfold mapPermNestedBoundarySubgraph
  exact (resolvedExternalLegSaturated_mapPermRFS_iff (boundaryCompletedResolvedGraph_mapPerm σ γ) δ).mpr
    hδsat

/-! ## Step 4 — coherence: `rootRelativeInner` naturality + the headline -/

/-- **body-598 — `rootRelativeInner` is `mapPerm`-natural.**  Lifting the relabeled nested subgraph back
to the relabeled root equals relabeling the root lift.  Vertices / internal edges transport verbatim;
the external legs are the filter/map commute (`σ` injective, `mem_finset_image`).  RAW subgraph equality.
-/
theorem rootRelativeInner_mapPerm (σ : Equiv.Perm VertexId) (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph) :
    rootRelativeInner (γ.mapPerm σ) (mapPermNestedBoundarySubgraph σ γ δ)
      = (rootRelativeInner γ δ).mapPerm σ := by
  apply ResolvedFeynmanSubgraph.ext
  · simp only [rootRelativeInner_vertices, mapPermNestedBoundarySubgraph_vertices,
      ResolvedFeynmanSubgraph.mapPerm_vertices]
  · simp only [rootRelativeInner_internalEdges, mapPermNestedBoundarySubgraph_internalEdges,
      ResolvedFeynmanSubgraph.mapPerm_internalEdges]
  · simp only [rootRelativeInner_externalLegs, mapPermNestedBoundarySubgraph_vertices,
      ResolvedFeynmanSubgraph.mapPerm_externalLegs, ResolvedFeynmanGraph.mapPerm]
    rw [Multiset.filter_map]
    exact congrArg (Multiset.map (ResolvedExternalLeg.map σ))
      (Multiset.filter_congr (fun ℓ _ => σ.injective.mem_finset_image))

/-- **body-598 (HEADLINE) — the stable nested boundary completion is `mapPerm`-natural.**  A raw
`ResolvedFeynmanGraph` equality: completing the relabeled stable nest equals relabeling the stable nest.
Proved by a pure rewrite chain — mapped-stable `=` (597 on the mapped side) single-root-completion of the
mapped root `=` (`rootRelativeInner_mapPerm` + 589 `boundaryCompletedResolvedGraph_mapPerm` on `R`) the
mapped single-root-completion `=` (597 backwards) mapped-stable.  Ids ride `mapPerm`, so no ID work; no
even/odd replay. -/
theorem stableNestedBoundaryCompletedGraph_mapPerm (σ : Equiv.Perm VertexId)
    (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph)
    (hγsat : ResolvedExternalLegSaturated G γ)
    (hδsat : ResolvedExternalLegSaturated γ.boundaryCompletedResolvedGraph δ) :
    stableNestedBoundaryCompletedGraph (γ.mapPerm σ) (mapPermNestedBoundarySubgraph σ γ δ)
      = (stableNestedBoundaryCompletedGraph γ δ).mapPerm σ := by
  rw [stableNestedBoundaryCompletedGraph_eq (γ.mapPerm σ) (mapPermNestedBoundarySubgraph σ γ δ)
        ((mpFor_externalLegSaturated_iff σ γ).mpr hγsat)
        (mapPermNestedBoundarySubgraph_saturated σ γ δ hδsat),
      rootRelativeInner_mapPerm σ γ δ,
      (rootRelativeInner γ δ).boundaryCompletedResolvedGraph_mapPerm σ,
      ← stableNestedBoundaryCompletedGraph_eq γ δ hγsat hδsat]

end GaugeGeometry.QFT.Combinatorial
