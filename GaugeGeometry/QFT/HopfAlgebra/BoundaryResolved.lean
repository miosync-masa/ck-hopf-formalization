import GaugeGeometry.QFT.HopfAlgebra.Coassoc
import GaugeGeometry.QFT.Combinatorial.ResolvedFeynmanGraphs

/-!
# Boundary-resolved bridge (Track R-bridge-1, Tier 1)

Thin bridge between the flat Connes–Kreimer development (`Coassoc.lean`) and the
boundary-resolved carrier (`ResolvedFeynmanGraphs.lean`).

The flat coassociativity proof leaves two semantic facades — graph-insertion
uniqueness (`ForestGraphInsertionUniquenessModel`) and promoted external-leg
liftability
(`ForestQuotientForestSigmaForestCoverPromotedExternalLegsLiftableModel`).  Both
are **false on the flat carrier** (multiset-level collapse of structurally
distinct boundary data; explicit counterexamples in `HOPF_DECOMPOSITION.md`).

This file does **not** instantiate those flat facade classes — it cannot, because
they are flat-false and the forgetful map runs resolved → flat.  Instead it
states the *distilled boundary-semantics principles* underlying each facade and
proves them as **theorems on the boundary-resolved carrier**, where the
persistent `edgeId`/`legId` survives contraction and the collapse is impossible.
The forgetful map then recovers the flat carrier (§3), exhibiting the flat
facades as artifacts of the coarser flat notation.

Tier 1 only: no resolved `SubGraph` / `forestSigma` layer (that is `R-4-full`).
-/

namespace GaugeGeometry.QFT.HopfAlgebra

open GaugeGeometry.QFT.Combinatorial

/-! ## 1. Insertion uniqueness, distilled and resolved

The flat `ForestGraphInsertionUniquenessModel` asserts that a forest-choice
parent is determined by its vertices and its post-contraction remnant.  On the
flat carrier this fails: two distinct internal edges with identical
`(source, target, sector)` collapse to the same multiset element.  Its distilled
content — *the retargeted (contracted) internal-edge multiset determines the
pre-contraction internal edges* — is a **theorem** on the resolved carrier. -/
theorem resolved_insertion_internalEdges_unique
    (G : ResolvedFeynmanGraph) (hId : G.EdgeIdsUnique) {f : VertexId → VertexId}
    {M₁ M₂ : Multiset ResolvedFeynmanEdge}
    (hM₁ : M₁ ≤ G.internalEdges) (hM₂ : M₂ ≤ G.internalEdges)
    (h : M₁.map (ResolvedFeynmanEdge.retarget f) =
      M₂.map (ResolvedFeynmanEdge.retarget f)) :
    M₁ = M₂ :=
  G.retargetInternalEdges_injective_on_submultisets hId hM₁ hM₂ h

/-! ## 2. Promoted external-leg liftability, distilled and resolved

The flat `…PromotedExternalLegsLiftableModel` asserts that promoted external legs
of a contracted subgraph lift back consistently.  On the flat carrier this fails:
two legs with identical `(attachedTo, sector)` from different half-edges are
indistinguishable.  Its distilled content — *the retargeted external-leg multiset
determines the pre-contraction legs* — is a **theorem** on the resolved carrier. -/
theorem resolved_promotedExternalLegs_unique
    (G : ResolvedFeynmanGraph) (hId : G.LegIdsUnique) {f : VertexId → VertexId}
    {L₁ L₂ : Multiset ResolvedExternalLeg}
    (hL₁ : L₁ ≤ G.externalLegs) (hL₂ : L₂ ≤ G.externalLegs)
    (h : L₁.map (ResolvedExternalLeg.retarget f) =
      L₂.map (ResolvedExternalLeg.retarget f)) :
    L₁ = L₂ :=
  G.retargetExternalLegs_injective_on_submultisets hId hL₁ hL₂ h

/-! ## 3. Forgetful map recovers the flat carrier

The flat carrier is the forgetful image of the resolved carrier: forgetting the
identity-preserving resolved contraction yields the flat graph with endpoints
rewritten by `f`.  This is the JAR commuting square — the identities `edgeId`/
`legId` that `forget` discards are exactly the data whose loss makes the two flat
facades false. -/
theorem resolved_forget_retargetGraph_commutes
    (G : ResolvedFeynmanGraph) (f : VertexId → VertexId) (V : Finset VertexId) :
    (G.retargetGraph f V).forget =
      { vertices := V
        internalEdges := G.forget.internalEdges.map
          (fun e => { source := f e.source, target := f e.target, sector := e.sector })
        externalLegs := G.forget.externalLegs.map
          (fun ℓ => { attachedTo := f ℓ.attachedTo, sector := ℓ.sector }) } :=
  G.forget_retargetGraph f V

/-! ## 3′. Forget/retarget correspondence — resolved retarget projects *onto* the
flat endpoint-rewrite

The `forget` image of the identity-preserving resolved retarget `retarget f` is
the plain flat endpoint-rewrite by `f` (`flatEdgeRetarget` / `flatLegRetarget`) —
**not** the flat star-contraction `FeynmanEdge.retarget`.  These `rfl`-level
correspondences show the resolved injectivity lemmas (§1–§2) are **not**
cherry-picked analogues: they are the boundary-refined versions of *exactly* the
flat collapse map, recovered verbatim under `forget`. -/

/-- Flat endpoint-rewrite of an internal edge along a vertex map — the `forget`
image of `ResolvedFeynmanEdge.retarget`. -/
def flatEdgeRetarget (f : VertexId → VertexId) (e : FeynmanEdge) : FeynmanEdge :=
  { source := f e.source, target := f e.target, sector := e.sector }

/-- Flat attachment-rewrite of an external leg along a vertex map. -/
def flatLegRetarget (f : VertexId → VertexId) (ℓ : ExternalLeg) : ExternalLeg :=
  { attachedTo := f ℓ.attachedTo, sector := ℓ.sector }

/-- `forget` carries the resolved edge retarget to the flat endpoint-rewrite. -/
theorem forget_retarget_edge (f : VertexId → VertexId) (e : ResolvedFeynmanEdge) :
    (e.retarget f).forget = flatEdgeRetarget f e.forget := rfl

/-- `forget` carries the resolved leg retarget to the flat attachment-rewrite. -/
theorem forget_retarget_leg (f : VertexId → VertexId) (ℓ : ResolvedExternalLeg) :
    (ℓ.retarget f).forget = flatLegRetarget f ℓ.forget := rfl

/-- Multiset level: forgetting after resolved-retargeting an internal-edge
multiset equals flat-retargeting after forgetting. -/
theorem map_forget_retarget_edges (f : VertexId → VertexId)
    (M : Multiset ResolvedFeynmanEdge) :
    (M.map (ResolvedFeynmanEdge.retarget f)).map ResolvedFeynmanEdge.forget =
      (M.map ResolvedFeynmanEdge.forget).map (flatEdgeRetarget f) := by
  rw [Multiset.map_map, Multiset.map_map]
  exact Multiset.map_congr rfl (fun e _ => forget_retarget_edge f e)

/-- Multiset level: the same correspondence for external legs. -/
theorem map_forget_retarget_legs (f : VertexId → VertexId)
    (M : Multiset ResolvedExternalLeg) :
    (M.map (ResolvedExternalLeg.retarget f)).map ResolvedExternalLeg.forget =
      (M.map ResolvedExternalLeg.forget).map (flatLegRetarget f) := by
  rw [Multiset.map_map, Multiset.map_map]
  exact Multiset.map_congr rfl (fun ℓ _ => forget_retarget_leg f ℓ)

/-! ## 4. Non-vacuity witness for the repaired boundary semantics

`BoundaryResolvedSemanticModel` bundles the three repaired boundary-semantics
principles (§1–§3) into a single proposition, and `boundaryResolvedSemanticModel`
**inhabits it** on the boundary-resolved carrier.

This is the *positive* object answering the "vacuity / unicorn" objection.  The
two flat facade classes (`ForestGraphInsertionUniquenessModel`,
`ForestQuotientForestSigmaForestCoverPromotedExternalLegsLiftableModel`) are
**false on the flat carrier** — the conditional flat Hopf theorem is therefore a
*proof-skeleton factorization* identifying exactly what the informal flat proof
silently assumes, **not** an inhabited theorem about the flat carrier.  This
structure is intentionally **not** an instance of those flat classes (it cannot
be — they are flat-false and `forget` runs resolved → flat).  Instead it records
the corresponding identity-preservation principles on the resolved carrier, where
the persistent `edgeId`/`legId` makes the multiset collapse impossible.  The
edge/leg injectivity principles are gated on id-uniqueness (`EdgeIdsUnique` /
`LegIdsUnique`) — exactly the structure the flat carrier discards. -/
structure BoundaryResolvedSemanticModel : Prop where
  /-- The retargeted internal-edge submultiset determines its preimage, for
  graphs with unique edge ids (the resolved repair of insertion uniqueness). -/
  edge_submultiset_retarget_injective :
    ∀ (G : ResolvedFeynmanGraph), G.EdgeIdsUnique → ∀ (f : VertexId → VertexId)
      {M₁ M₂ : Multiset ResolvedFeynmanEdge},
      M₁ ≤ G.internalEdges → M₂ ≤ G.internalEdges →
      M₁.map (ResolvedFeynmanEdge.retarget f) =
        M₂.map (ResolvedFeynmanEdge.retarget f) →
      M₁ = M₂
  /-- The retargeted external-leg submultiset determines its preimage, for graphs
  with unique leg ids (the resolved repair of promoted-leg liftability). -/
  leg_submultiset_retarget_injective :
    ∀ (G : ResolvedFeynmanGraph), G.LegIdsUnique → ∀ (f : VertexId → VertexId)
      {L₁ L₂ : Multiset ResolvedExternalLeg},
      L₁ ≤ G.externalLegs → L₂ ≤ G.externalLegs →
      L₁.map (ResolvedExternalLeg.retarget f) =
        L₂.map (ResolvedExternalLeg.retarget f) →
      L₁ = L₂
  /-- The forgetful map commutes with identity-preserving retargeting: the flat
  carrier is the forgetful image of the resolved carrier (the JAR square). -/
  forget_retargetGraph_commutes :
    ∀ (G : ResolvedFeynmanGraph) (f : VertexId → VertexId) (V : Finset VertexId),
      (G.retargetGraph f V).forget =
        { vertices := V
          internalEdges := G.forget.internalEdges.map
            (fun e => { source := f e.source, target := f e.target, sector := e.sector })
          externalLegs := G.forget.externalLegs.map
            (fun ℓ => { attachedTo := f ℓ.attachedTo, sector := ℓ.sector }) }
  /-- The resolved edge retarget projects, after forgetting, *exactly* onto the
  flat endpoint-rewrite (internal-edge multiset level): injectivity holds before
  forgetting, and the maps agree with the flat collapse after forgetting. -/
  edge_forget_retarget_commutes :
    ∀ (f : VertexId → VertexId) (M : Multiset ResolvedFeynmanEdge),
      (M.map (ResolvedFeynmanEdge.retarget f)).map ResolvedFeynmanEdge.forget =
        (M.map ResolvedFeynmanEdge.forget).map (flatEdgeRetarget f)
  /-- The resolved leg retarget projects, after forgetting, *exactly* onto the
  flat attachment-rewrite (external-leg multiset level). -/
  leg_forget_retarget_commutes :
    ∀ (f : VertexId → VertexId) (M : Multiset ResolvedExternalLeg),
      (M.map (ResolvedExternalLeg.retarget f)).map ResolvedExternalLeg.forget =
        (M.map ResolvedExternalLeg.forget).map (flatLegRetarget f)

/-- **Non-vacuity witness.**  The boundary-resolved carrier inhabits
`BoundaryResolvedSemanticModel`: the three repaired principles (§1–§3) hold as
theorems.  This is the concrete positive semantic object underwriting the JAR
claim — the flat facades are *false* (that is the diagnosis); the resolved carrier
is where the corresponding principles are *true*. -/
theorem boundaryResolvedSemanticModel : BoundaryResolvedSemanticModel := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro G hId _f M₁ M₂ hM₁ hM₂ h
    exact resolved_insertion_internalEdges_unique G hId hM₁ hM₂ h
  · intro G hId _f L₁ L₂ hL₁ hL₂ h
    exact resolved_promotedExternalLegs_unique G hId hL₁ hL₂ h
  · intro G f V
    exact resolved_forget_retargetGraph_commutes G f V
  · intro f M
    exact map_forget_retarget_edges f M
  · intro f M
    exact map_forget_retarget_legs f M

end GaugeGeometry.QFT.HopfAlgebra
