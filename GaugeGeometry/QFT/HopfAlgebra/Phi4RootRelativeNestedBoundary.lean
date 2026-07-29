import GaugeGeometry.QFT.HopfAlgebra.ResolvedBoundaryCompletedSubgraph
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaUnconditionalizationFrontier

/-!
# QFT-R1-body-597 — root-relative stable nested boundary completion core

Body-596 proved the **no-go**: re-encoding a nested boundary leg
(`existingLegId (boundaryExternalLeg e) = 4·e+2`) can never equal the direct route
(`boundaryLegId e = 2·e+1`).  The constructive repair here does **not** re-encode inherited legs.

Given `H := γ.boundaryCompletedResolvedGraph` and a nested subgraph `δ : ResolvedFeynmanSubgraph H`,
we lift `δ` back to a root-`G` subgraph `R := rootRelativeInner γ δ` and complete it **once** at root
coordinates.  The inherited legs `δ.externalLegs` are ALREADY root-normalized (they carry root
`legId`s), so they are kept **verbatim**; only the newly-cut root-boundary edges
`newRootBoundary γ δ = R.resolvedBoundaryEdges - inheritedOuter γ δ` receive an odd induced leg.

The headline `stableNestedBoundaryCompletedGraph_eq` is a **raw** `ResolvedFeynmanGraph` equality
(exact ID / multiplicity / profile) between the stable graph — inherited legs verbatim + fresh
root-boundary legs — and `R.boundaryCompletedResolvedExternalLegs`, the single root completion of `R`.

Everything is multiplicity-safe (`Multiset`, no `Finset`/dedup, no membership-only shortcuts).  No
traceability / `LegIdsUnique` / `mapPerm` / family-CD (those are body-598+); no `promote`, no
selectedOuter / alpha / coassoc.  Zero new `class`/`structure`/`instance`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical
open ResolvedFeynmanSubgraph

variable {G : ResolvedFeynmanGraph}

/-! ## Step 1 — the root-relative inner subgraph -/

/-- Lift a nested subgraph `δ` of the boundary-completed graph `H = γ.boundaryCompletedResolvedGraph`
back to a subgraph of the root `G`.  Vertices and internal edges are `δ`'s verbatim (they already live
at root coordinates: `H.vertices = γ.vertices`, `H.internalEdges = γ.internalEdges`); the external legs
are the root-`G` legs saturating `δ`'s vertices. -/
noncomputable def rootRelativeInner (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph) : ResolvedFeynmanSubgraph G where
  vertices := δ.vertices
  internalEdges := δ.internalEdges
  externalLegs := G.externalLegs.filter (fun ℓ => ℓ.attachedTo ∈ δ.vertices)
  vertices_subset := fun _v hv => γ.vertices_subset (δ.vertices_subset hv)
  internalEdges_le := le_trans δ.internalEdges_le γ.internalEdges_le
  externalLegs_le := Multiset.filter_le _ _
  edges_supported := δ.edges_supported
  legs_supported := fun _ℓ hℓ => (Multiset.mem_filter.mp hℓ).2

@[simp] theorem rootRelativeInner_vertices (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph) :
    (rootRelativeInner γ δ).vertices = δ.vertices := rfl

@[simp] theorem rootRelativeInner_internalEdges (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph) :
    (rootRelativeInner γ δ).internalEdges = δ.internalEdges := rfl

@[simp] theorem rootRelativeInner_externalLegs (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph) :
    (rootRelativeInner γ δ).externalLegs
      = G.externalLegs.filter (fun ℓ => ℓ.attachedTo ∈ δ.vertices) := rfl

/-- The inherited outer boundary edges of `δ` seen from the root: the root boundary edges of `γ`
whose inside endpoint already lands inside `δ.vertices`.  These induce legs that `δ` inherited
(root-normalized) — they must NOT be re-encoded. -/
noncomputable def inheritedOuter (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph) : Multiset ResolvedFeynmanEdge :=
  γ.resolvedBoundaryEdges.filter (fun e => γ.resolvedInsideEndpoint e ∈ δ.vertices)

/-! ## Step 2 — saturation gives the exact external-leg decomposition -/

/-- Under external-leg saturation the subgraph's legs are *exactly* the ambient legs attached inside
it: the forward `≤` is `externalLegs_le` + `legs_supported`, the reverse `≤` is the saturation. -/
theorem externalLegs_eq_filter_of_saturated {H : ResolvedFeynmanGraph} (η : ResolvedFeynmanSubgraph H)
    (hsat : ResolvedExternalLegSaturated H η) :
    η.externalLegs = H.externalLegs.filter (fun ℓ => ℓ.attachedTo ∈ η.vertices) :=
  le_antisymm
    (Multiset.le_filter.mpr ⟨η.externalLegs_le, fun ℓ hℓ => η.legs_supported ℓ hℓ⟩)
    hsat

/-- **body-597 (Step 2, multiplicity crux) — the nested legs split at root coordinates.**  Under both
saturation hypotheses, `δ.externalLegs` decomposes into the EVEN re-encoding of the root legs saturating
`δ`, plus the ODD induced legs of the `inheritedOuter` root-boundary edges.  Exact multiplicity. -/
theorem rootRelativeInner_externalLegs_decomp (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph)
    (hγsat : ResolvedExternalLegSaturated G γ)
    (hδsat : ResolvedExternalLegSaturated γ.boundaryCompletedResolvedGraph δ) :
    δ.externalLegs
      = (G.externalLegs.filter (fun ℓ => ℓ.attachedTo ∈ δ.vertices)).map encodeExistingLeg
        + (inheritedOuter γ δ).map γ.boundaryExternalLeg := by
  rw [externalLegs_eq_filter_of_saturated δ hδsat,
    boundaryCompletedResolvedGraph_externalLegs]
  unfold ResolvedFeynmanSubgraph.boundaryCompletedResolvedExternalLegs
  rw [Multiset.filter_add]
  congr 1
  · -- EVEN part: filter-after-map = map-after-filter, then collapse γ.vertices via δ ⊆ γ
    rw [← Multiset.map_filter_of_iff encodeExistingLeg γ.externalLegs
          (fun ℓ => ℓ.attachedTo ∈ δ.vertices) (fun ℓ => ℓ.attachedTo ∈ δ.vertices)
          (fun _ => Iff.rfl)]
    congr 1
    rw [externalLegs_eq_filter_of_saturated γ hγsat, Multiset.filter_filter]
    apply Multiset.filter_congr
    intro ℓ _
    constructor
    · rintro ⟨h1, _⟩; exact h1
    · intro h1; exact ⟨h1, δ.vertices_subset h1⟩
  · -- ODD part: filter-after-map = map-after-filter = inheritedOuter.map (definitional)
    rw [← Multiset.map_filter_of_iff γ.boundaryExternalLeg γ.resolvedBoundaryEdges
          (fun e => γ.resolvedInsideEndpoint e ∈ δ.vertices) (fun ℓ => ℓ.attachedTo ∈ δ.vertices)
          (fun _ => Iff.rfl)]
    rfl

/-! ## Step 3 — the root-boundary residual + inherited-leg agreement -/

/-- The inherited outer edges are genuinely root boundary edges of `R` (their inside endpoint is in
`δ.vertices = R.vertices`, and the other endpoint sits outside `γ.vertices ⊇ δ.vertices`).  Proved by
monotonicity of `filter` over `G.internalEdges` — exact multiplicity, no dedup. -/
theorem inheritedOuter_le_R_resolvedBoundaryEdges (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph) :
    inheritedOuter γ δ ≤ (rootRelativeInner γ δ).resolvedBoundaryEdges := by
  have h1 : inheritedOuter γ δ
      = G.internalEdges.filter
          (fun e => γ.resolvedInsideEndpoint e ∈ δ.vertices ∧ γ.resolvedIsBoundaryEdge e) := by
    unfold inheritedOuter ResolvedFeynmanSubgraph.resolvedBoundaryEdges
    rw [Multiset.filter_filter]
  have h2 : (rootRelativeInner γ δ).resolvedBoundaryEdges
      = G.internalEdges.filter (rootRelativeInner γ δ).resolvedIsBoundaryEdge := rfl
  rw [h1, h2]
  apply Multiset.monotone_filter_right
  intro e he
  obtain ⟨hQ, hbe⟩ := he
  -- goal: R.resolvedIsBoundaryEdge e, where R.vertices = δ.vertices
  show (e.source ∈ δ.vertices ∧ e.target ∉ δ.vertices) ∨
       (e.source ∉ δ.vertices ∧ e.target ∈ δ.vertices)
  unfold ResolvedFeynmanSubgraph.resolvedInsideEndpoint at hQ
  rcases hbe with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · rw [if_pos hs] at hQ
    exact Or.inl ⟨hQ, fun hc => ht (δ.vertices_subset hc)⟩
  · rw [if_neg hs] at hQ
    exact Or.inr ⟨fun hc => hs (δ.vertices_subset hc), hQ⟩

/-- On an inherited outer edge, `γ`'s induced leg and `R`'s induced leg coincide: same odd `legId`
(depends only on `e.edgeId`), same sector, and the same inside endpoint — the endpoint that is inside
`δ.vertices`.  So the inherited leg is kept verbatim under either graph. -/
theorem boundaryExternalLeg_agree_on_inherited (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph)
    {e : ResolvedFeynmanEdge} (he : e ∈ inheritedOuter γ δ) :
    γ.boundaryExternalLeg e = (rootRelativeInner γ δ).boundaryExternalLeg e := by
  unfold inheritedOuter at he
  rw [Multiset.mem_filter] at he
  obtain ⟨_, hQ⟩ := he
  have hend : γ.resolvedInsideEndpoint e = (rootRelativeInner γ δ).resolvedInsideEndpoint e := by
    show (if e.source ∈ γ.vertices then e.source else e.target)
       = (if e.source ∈ δ.vertices then e.source else e.target)
    by_cases hs : e.source ∈ γ.vertices
    · rw [if_pos hs]
      have hsδ : e.source ∈ δ.vertices := by
        have h := hQ
        unfold ResolvedFeynmanSubgraph.resolvedInsideEndpoint at h
        rw [if_pos hs] at h; exact h
      rw [if_pos hsδ]
    · rw [if_neg hs]
      have hsδ : e.source ∉ δ.vertices := fun hc => hs (δ.vertices_subset hc)
      rw [if_neg hsδ]
  unfold ResolvedFeynmanSubgraph.boundaryExternalLeg
  rw [hend]

/-- The freshly-cut root-boundary edges: the root boundary edges of `R` that were NOT already inside
`δ` (multiset difference, so multiplicity-exact).  These — and only these — get a new odd induced leg. -/
noncomputable def newRootBoundary (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph) : Multiset ResolvedFeynmanEdge :=
  (rootRelativeInner γ δ).resolvedBoundaryEdges - inheritedOuter γ δ

/-! ## Step 4 — the stable nested boundary-completed graph -/

/-- The stable nested completed legs: `δ`'s inherited legs KEPT VERBATIM (no re-encoding), plus the
odd induced legs of the freshly-cut root-boundary edges. -/
noncomputable def stableNestedResolvedExternalLegs (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph) : Multiset ResolvedExternalLeg :=
  δ.externalLegs + (newRootBoundary γ δ).map (rootRelativeInner γ δ).boundaryExternalLeg

/-- The stable nested boundary-completed graph.  Same vertices / internal edges as `δ`; external legs
are the stable nested legs (inherited verbatim + fresh root-boundary). -/
noncomputable def stableNestedBoundaryCompletedGraph (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph) : ResolvedFeynmanGraph where
  vertices := δ.vertices
  internalEdges := δ.internalEdges
  externalLegs := stableNestedResolvedExternalLegs γ δ

/-! ## Step 5 — victory: raw graph equality with the single root completion -/

/-- **body-597 (Step 5, HEADLINE legs) — the stable nested legs equal the single root completion of
`R`.**  Split `R.resolvedBoundaryEdges = inheritedOuter + newRootBoundary`; the inherited half rewrites
`R.boundaryExternalLeg` to `γ.boundaryExternalLeg` (agreement) and re-absorbs into `δ.externalLegs` via
Step 2; the fresh half is shared.  Exact ID / multiplicity — NOT a class equality. -/
theorem stableNestedResolvedExternalLegs_eq (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph)
    (hγsat : ResolvedExternalLegSaturated G γ)
    (hδsat : ResolvedExternalLegSaturated γ.boundaryCompletedResolvedGraph δ) :
    stableNestedResolvedExternalLegs γ δ
      = (rootRelativeInner γ δ).boundaryCompletedResolvedExternalLegs := by
  have hdecomp := rootRelativeInner_externalLegs_decomp γ δ hγsat hδsat
  have hRext : (rootRelativeInner γ δ).externalLegs
      = G.externalLegs.filter (fun ℓ => ℓ.attachedTo ∈ δ.vertices) := rfl
  have hsplit : (rootRelativeInner γ δ).resolvedBoundaryEdges
      = inheritedOuter γ δ + newRootBoundary γ δ := by
    unfold newRootBoundary
    rw [add_tsub_cancel_of_le (inheritedOuter_le_R_resolvedBoundaryEdges γ δ)]
  have hmapcong : (inheritedOuter γ δ).map (rootRelativeInner γ δ).boundaryExternalLeg
      = (inheritedOuter γ δ).map γ.boundaryExternalLeg :=
    Multiset.map_congr rfl (fun e he => (boundaryExternalLeg_agree_on_inherited γ δ he).symm)
  unfold stableNestedResolvedExternalLegs ResolvedFeynmanSubgraph.boundaryCompletedResolvedExternalLegs
  rw [hRext, hsplit, Multiset.map_add, hmapcong, hdecomp]
  abel

/-- **body-597 (Step 5, HEADLINE) — the stable nested boundary-completed graph is RAW-equal to the
single root completion `R.boundaryCompletedResolvedGraph`.**  Vertices / internal edges are `δ`'s
(rfl); the legs are the Step-5 legs equality.  This is exactly the constructive repair of body-596's
no-go: inherited legs are kept verbatim, fresh root-boundary legs are added once, and the result
matches completing the root lift `R` in one shot. -/
theorem stableNestedBoundaryCompletedGraph_eq (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph)
    (hγsat : ResolvedExternalLegSaturated G γ)
    (hδsat : ResolvedExternalLegSaturated γ.boundaryCompletedResolvedGraph δ) :
    stableNestedBoundaryCompletedGraph γ δ
      = (rootRelativeInner γ δ).boundaryCompletedResolvedGraph := by
  have hlegs := stableNestedResolvedExternalLegs_eq γ δ hγsat hδsat
  unfold stableNestedBoundaryCompletedGraph ResolvedFeynmanSubgraph.boundaryCompletedResolvedGraph
  rw [ResolvedFeynmanGraph.mk.injEq]
  exact ⟨rfl, rfl, hlegs⟩

end GaugeGeometry.QFT.Combinatorial
