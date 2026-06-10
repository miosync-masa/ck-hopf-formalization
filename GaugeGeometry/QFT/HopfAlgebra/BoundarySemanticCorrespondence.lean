import GaugeGeometry.QFT.HopfAlgebra.BoundaryResolved
import GaugeGeometry.QFT.HopfAlgebra.BoundaryResolvedCounterexamples

/-!
# Boundary-semantics correspondence package (Track K)

One Lean package showing that the two flat boundary failures and the two resolved
repairs are the **same** retarget/forget mechanism — not cherry-picked analogues:

* flat: the multiset edge/leg retarget is **not** injective (`not_flat…Injective`,
  from the §6 decidable counterexamples);
* resolved: the identity-preserving retarget **is** injective on submultisets, under
  id-uniqueness (`resolved…InjectiveOn`, the R-3 engine);
* `forget` carries the resolved retarget *verbatim* onto the flat one
  (`…_forget_projection`), so the failure and the repair act on the two sides of the
  same forgetful map.

We work at the distilled mechanism level only: we do **not** instantiate or negate
the flat facade *classes* (large proof-skeleton interfaces, false on the flat
carrier).
-/

namespace GaugeGeometry.QFT.HopfAlgebra

open GaugeGeometry.QFT.Combinatorial

/-! ## K1 — flat mechanism predicates -/

/-- Mechanism predicate: the flat edge-retarget map is injective on edge multisets. -/
def FlatEdgeRetargetInjective : Prop :=
  ∀ (f : VertexId → VertexId) {M₁ M₂ : Multiset FeynmanEdge},
    M₁.map (flatEdgeRetarget f) = M₂.map (flatEdgeRetarget f) → M₁ = M₂

/-- Mechanism predicate: the flat leg-retarget map is injective on leg multisets. -/
def FlatLegRetargetInjective : Prop :=
  ∀ (f : VertexId → VertexId) {L₁ L₂ : Multiset ExternalLeg},
    L₁.map (flatLegRetarget f) = L₂.map (flatLegRetarget f) → L₁ = L₂

/-! ## K2 — the flat mechanisms fail -/

/-- The flat edge-retarget mechanism is not injective (singleton-multiset
counterexample). -/
theorem not_flatEdgeRetargetInjective : ¬ FlatEdgeRetargetInjective := by
  intro h
  obtain ⟨f, M₁, M₂, hne, hcol⟩ := flatEdgeRetarget_multiset_collapse
  exact hne (h f hcol)

/-- The flat leg-retarget mechanism is not injective. -/
theorem not_flatLegRetargetInjective : ¬ FlatLegRetargetInjective := by
  intro h
  obtain ⟨f, L₁, L₂, hne, hcol⟩ := flatLegRetarget_multiset_collapse
  exact hne (h f hcol)

/-! ## K3 — the resolved mechanisms hold -/

/-- Under `EdgeIdsUnique`, the resolved identity-preserving edge retarget is
injective on submultisets (the R-3a engine). -/
theorem resolvedEdgeRetargetInjectiveOn (G : ResolvedFeynmanGraph) (hId : G.EdgeIdsUnique)
    (f : VertexId → VertexId) {M₁ M₂ : Multiset ResolvedFeynmanEdge}
    (hM₁ : M₁ ≤ G.internalEdges) (hM₂ : M₂ ≤ G.internalEdges)
    (h : M₁.map (ResolvedFeynmanEdge.retarget f) = M₂.map (ResolvedFeynmanEdge.retarget f)) :
    M₁ = M₂ :=
  G.retargetInternalEdges_injective_on_submultisets hId hM₁ hM₂ h

/-- Under `LegIdsUnique`, the resolved identity-preserving leg retarget is
injective on submultisets (the R-3b engine). -/
theorem resolvedLegRetargetInjectiveOn (G : ResolvedFeynmanGraph) (hId : G.LegIdsUnique)
    (f : VertexId → VertexId) {L₁ L₂ : Multiset ResolvedExternalLeg}
    (hL₁ : L₁ ≤ G.externalLegs) (hL₂ : L₂ ≤ G.externalLegs)
    (h : L₁.map (ResolvedExternalLeg.retarget f) = L₂.map (ResolvedExternalLeg.retarget f)) :
    L₁ = L₂ :=
  G.retargetExternalLegs_injective_on_submultisets hId hL₁ hL₂ h

/-! ## K4 — the correspondence package -/

/-- **The boundary-semantics correspondence.**  Flat retarget non-injectivity,
resolved retarget injectivity (under id-uniqueness), and the forgetful projection
connecting them — bundled as one `Prop`. -/
structure BoundarySemanticCorrespondence : Prop where
  /-- Flat edge retarget is not injective. -/
  flat_edge_failure : ¬ FlatEdgeRetargetInjective
  /-- Flat leg retarget is not injective. -/
  flat_leg_failure : ¬ FlatLegRetargetInjective
  /-- Resolved edge retarget is injective on submultisets, under `EdgeIdsUnique`. -/
  resolved_edge_repair :
    ∀ (G : ResolvedFeynmanGraph), G.EdgeIdsUnique → ∀ (f : VertexId → VertexId)
      {M₁ M₂ : Multiset ResolvedFeynmanEdge},
      M₁ ≤ G.internalEdges → M₂ ≤ G.internalEdges →
      M₁.map (ResolvedFeynmanEdge.retarget f) = M₂.map (ResolvedFeynmanEdge.retarget f) →
      M₁ = M₂
  /-- Resolved leg retarget is injective on submultisets, under `LegIdsUnique`. -/
  resolved_leg_repair :
    ∀ (G : ResolvedFeynmanGraph), G.LegIdsUnique → ∀ (f : VertexId → VertexId)
      {L₁ L₂ : Multiset ResolvedExternalLeg},
      L₁ ≤ G.externalLegs → L₂ ≤ G.externalLegs →
      L₁.map (ResolvedExternalLeg.retarget f) = L₂.map (ResolvedExternalLeg.retarget f) →
      L₁ = L₂
  /-- `forget` carries the resolved edge retarget onto the flat one. -/
  edge_forget_projection :
    ∀ (f : VertexId → VertexId) (M : Multiset ResolvedFeynmanEdge),
      (M.map (ResolvedFeynmanEdge.retarget f)).map ResolvedFeynmanEdge.forget =
        (M.map ResolvedFeynmanEdge.forget).map (flatEdgeRetarget f)
  /-- `forget` carries the resolved leg retarget onto the flat one. -/
  leg_forget_projection :
    ∀ (f : VertexId → VertexId) (M : Multiset ResolvedExternalLeg),
      (M.map (ResolvedExternalLeg.retarget f)).map ResolvedExternalLeg.forget =
        (M.map ResolvedExternalLeg.forget).map (flatLegRetarget f)

/-- **Track K headline.**  The boundary-semantics correspondence holds: the flat
failure and the resolved repair are the same retarget mechanism on the two sides of
`forget`. -/
theorem boundarySemanticCorrespondence_holds : BoundarySemanticCorrespondence where
  flat_edge_failure := not_flatEdgeRetargetInjective
  flat_leg_failure := not_flatLegRetargetInjective
  resolved_edge_repair := resolvedEdgeRetargetInjectiveOn
  resolved_leg_repair := resolvedLegRetargetInjectiveOn
  edge_forget_projection := map_forget_retarget_edges
  leg_forget_projection := map_forget_retarget_legs

end GaugeGeometry.QFT.HopfAlgebra
