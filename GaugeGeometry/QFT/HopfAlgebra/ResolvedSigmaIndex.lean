import GaugeGeometry.QFT.HopfAlgebra.ResolvedSigmaCover

/-!
# Resolved σ-index minimal skeleton (Track R-4-superfull, Step 6C phase 1)

The minimal resolved σ-index *interface* supplying the two hooks the resolved
boundary repair theorems need:

* **(A)** `hV` for `resolvedParentRemnant_injOn` — the source-vertex equality that
  cannot be recovered locally from the remnant (since `retargetVertex` collapses
  components to stars).  Packaged as the field `remnant_vertex_recovery`.
* **(B)** the promoted components / Plus legs for
  `resolved_promotedComponent_externalLegs_le_plus`, specialised to a parent's
  remnant vertices.

This is **skeleton + interface only**: we do *not* constructively build the source
vertex recovery (`resolvedSourceVertices`) — per the HALT, that stays a hook field, to
be discharged when a concrete resolved σ-index is constructed.  The deliverable here is
to pin the σ-index's *responsibilities* (`hA`, `hV`, promoted-leg containment) behind a
clean structure, so a later phase only has to *construct* a `ResolvedSigmaParentSet`.
-/

set_option linter.unusedSectionVars false

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ H : FeynmanGraph, DivergenceMeasure H]
         [∀ H : FeynmanGraph, IsPermInvariantDivergence H]
         [∀ H : FeynmanGraph, IsIsoInvariantDivergence H]
         [∀ H : FeynmanGraph, Fintype (FeynmanSubgraph H)]
         [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
         [IsDivergencePreservedByAdmissibleForestContract]

variable {G : ResolvedFeynmanGraph}

/-! ## Phase 6C-1 — the parent-set interface -/

/-- **Resolved σ-index parent set (minimal skeleton).**  A finite set of parent
subgraphs together with exactly the two facts the resolved insertion repair consumes:
each parent contains `Aout`'s edges (`hA`), and equal remnants force equal source
vertices (`hV`, kept as a hook field — not constructed here). -/
structure ResolvedSigmaParentSet
    (Aout : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId) where
  /-- The finite parent set. -/
  parents : Finset (ResolvedFeynmanSubgraph G)
  /-- Every parent contains the outer forest's internal edges (`hA`). -/
  containsAoutEdges : ∀ γ ∈ parents, Aout.internalEdges ≤ γ.internalEdges
  /-- Equal remnants force equal source vertices (`hV` hook — supplied by the σ-index
  construction, mirroring the flat B-forest-2a remnant-source-vertex recovery). -/
  remnant_vertex_recovery :
    ∀ γ₁ ∈ parents, ∀ γ₂ ∈ parents,
      resolvedParentRemnant Aout starOf γ₁ = resolvedParentRemnant Aout starOf γ₂ →
      γ₁.vertices = γ₂.vertices

/-- **Generic constructor.**  Build a `ResolvedSigmaParentSet` from an explicit parent
set together with its two hooks.  Trivial — but it is the interface a concrete σ-index
construction targets. -/
def ResolvedSigmaParentSet.ofParents
    {Aout : ResolvedAdmissibleSubgraph G}
    {starOf : ResolvedFeynmanSubgraph G → VertexId}
    (parents : Finset (ResolvedFeynmanSubgraph G))
    (hA : ∀ γ ∈ parents, Aout.internalEdges ≤ γ.internalEdges)
    (hV : ∀ γ₁ ∈ parents, ∀ γ₂ ∈ parents,
        resolvedParentRemnant Aout starOf γ₁ = resolvedParentRemnant Aout starOf γ₂ →
        γ₁.vertices = γ₂.vertices) :
    ResolvedSigmaParentSet Aout starOf where
  parents := parents
  containsAoutEdges := hA
  remnant_vertex_recovery := hV

/-! ### Source-vertex recovery: the `hV` discharge attempt

The naive preimage recovery of the source vertices from a remnant. -/

/-- Candidate source-vertex recovery: the `G`-vertices whose retarget lands in `δ`. -/
noncomputable def resolvedRemainderSourceVertices
    (Aout : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId)
    (δ : ResolvedFeynmanSubgraph (Aout.contractWithStars starOf)) : Finset VertexId := by
  classical
  exact G.vertices.filter (fun v => Aout.retargetVertex starOf v ∈ δ.vertices)

/-- **Easy direction (always holds).**  A parent's vertices are recovered by the
preimage.  The *reverse* inclusion is where retarget collapse bites (see the report
note below): a star in the remnant pulls back the *whole* `Aout`-component, so the
preimage over-recovers unless `γ` is component-saturated. -/
theorem subset_resolvedRemainderSourceVertices_parent
    (Aout : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId)
    (γ : ResolvedFeynmanSubgraph G) :
    γ.vertices ⊆
      resolvedRemainderSourceVertices Aout starOf (resolvedParentRemnant Aout starOf γ) := by
  classical
  intro v hv
  rw [resolvedRemainderSourceVertices, Finset.mem_filter]
  exact ⟨γ.vertices_subset hv,
    Finset.mem_image.mpr ⟨v, hv, rfl⟩⟩

/-! **Report (HALT — over-recovery).**  The reverse inclusion
`resolvedRemainderSourceVertices … (remnant γ) ⊆ γ.vertices` is **false in general**:
`Aout.retargetVertex starOf` sends every vertex of an `Aout`-component to that
component's star (`retargetVertex … v = starOf γc` when `v` is in component `γc`,
identity on the complement).  Hence if a star `s` lies in `(remnant γ).vertices`
(because `γ` met component `γc` at *some* vertex), the preimage pulls back **all** of
`γc`'s vertices — even those `γ` does not contain.  So `resolvedRemainderSourceVertices
… = γ.vertices` requires `γ` to be **component-saturated** (contains a whole
`Aout`-component whenever it meets it).

The missing restriction is structural: saturation follows from `hA`
(`Aout.internalEdges ≤ γ.internalEdges`, forcing each component's edges into `γ`, hence
— by `edges_supported` — the component's edge-endpoint vertices) **only if** `Aout`
components have no isolated (edge-free) vertices, i.e. component vertices = component
edge-endpoints.  Establishing that is a connectivity/path argument on `Aout`
components, not currently available.  Per the HALT this is *not* entered here:
`remnant_vertex_recovery` therefore stays a hook field, to be discharged by the σ-index
construction once component vertex-saturation is proved. -/

/-! ## Phase 6C-2 — insertion injectivity from the parent set -/

/-- **Insertion injectivity from the parent-set skeleton.**  Given the σ-index's two
hooks, the parent-remnant map is injective on the parent set — a direct application of
`resolvedParentRemnant_injOn`. -/
theorem ResolvedSigmaParentSet.parentRemnant_injOn
    {Aout : ResolvedAdmissibleSubgraph G}
    {starOf : ResolvedFeynmanSubgraph G → VertexId}
    (P : ResolvedSigmaParentSet Aout starOf)
    (hEdgeId : G.EdgeIdsUnique) (hLegId : G.LegIdsUnique) :
    Set.InjOn (resolvedParentRemnant Aout starOf) ↑P.parents :=
  resolvedParentRemnant_injOn Aout starOf hEdgeId hLegId
    P.remnant_vertex_recovery P.containsAoutEdges

/-! ## Phase 6C-3 — promoted components attached to a parent's remnant -/

/-- The promoted components of a parent `γ`: those outer-forest components whose star
lands in `γ`'s remnant vertices. -/
noncomputable def resolvedPromotedComponentsOfRemnant
    (Aout : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId)
    (γ : ResolvedFeynmanSubgraph G) : Finset (ResolvedFeynmanSubgraph G) :=
  resolvedPromotedComponentsByVertices Aout starOf
    (resolvedParentRemnant Aout starOf γ).vertices

/-- **Promoted-leg containment, specialised to a parent's remnant.**  Each promoted
component of `γ` has its external legs inside the source-plus legs for `γ`'s remnant —
direct from `resolved_promotedComponent_externalLegs_le_plus`. -/
theorem promoted_externalLegs_le_plus_of_parent_set
    (Aout : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId)
    (γ : ResolvedFeynmanSubgraph G) {η : ResolvedFeynmanSubgraph G}
    (hη : η ∈ resolvedPromotedComponentsOfRemnant Aout starOf γ) :
    η.externalLegs ≤ resolvedSourceExactPlusExternalLegs Aout starOf
      (resolvedParentRemnant Aout starOf γ).vertices :=
  resolved_promotedComponent_externalLegs_le_plus Aout starOf _ hη

end GaugeGeometry.QFT.Combinatorial
