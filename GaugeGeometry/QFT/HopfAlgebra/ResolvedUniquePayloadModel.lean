import GaugeGeometry.QFT.Combinatorial.ResolvedUniqueIdLift
import GaugeGeometry.QFT.HopfAlgebra.ResolvedPayloadModel

/-!
# Unique-id payload model (Track R-4-superfull, Steps 2–3)

Upgrade the Phase 6c payload existence from the constant-id lift to the **unique-id**
lift, so the resolved repair theorems (`parent_eq_of_remainder_eq`,
`externalLegs_lift_unique`, which need `EdgeIdsUnique`/`LegIdsUnique`) apply to the
actual payload graphs.

The crux (per the design note): a subgraph is **not** re-tagged independently; its
edges/legs are lifted as a *submultiset preimage* of the ambient tagged occurrences,
via the kernel `exists_le_map`.
-/

set_option linter.unusedSectionVars false

namespace GaugeGeometry.QFT.Combinatorial

/-- **Submultiset-preimage kernel.**  If `M` is a submultiset of `s.map f`, then it
is the `f`-image of some submultiset of `s` (induction on `M`, peeling a preimage
occurrence each step). -/
theorem exists_le_map {α β : Type*} [DecidableEq α] [DecidableEq β] (f : α → β)
    {s : Multiset α} {M : Multiset β} (h : M ≤ s.map f) : ∃ t ≤ s, t.map f = M := by
  induction M using Multiset.induction generalizing s with
  | empty => exact ⟨0, Multiset.zero_le s, by simp⟩
  | cons b M' ih =>
    have hb : b ∈ s.map f := Multiset.mem_of_le h (Multiset.mem_cons_self b M')
    obtain ⟨a, ha, hfa⟩ := Multiset.mem_map.mp hb
    have hsplit : s.map f = f a ::ₘ (s.erase a).map f := by
      conv_lhs => rw [← Multiset.cons_erase ha, Multiset.map_cons]
    have hM' : M' ≤ (s.erase a).map f := by
      have hbc : b ::ₘ M' ≤ f a ::ₘ (s.erase a).map f := hsplit ▸ h
      rw [hfa] at hbc
      exact (Multiset.cons_le_cons_iff b).mp hbc
    obtain ⟨t', ht'le, ht'⟩ := ih hM'
    refine ⟨a ::ₘ t', ?_, ?_⟩
    · calc a ::ₘ t' ≤ a ::ₘ s.erase a := Multiset.cons_le_cons a ht'le
        _ = s := Multiset.cons_erase ha
    · rw [Multiset.map_cons, ht', hfa]

/-! ### Submultiset lift by forget (edges / legs) -/

/-- Lift a submultiset of the (forgotten) ambient edges to a submultiset of the
ambient tagged edges, preserving `forget` (an occurrence-faithful preimage). -/
noncomputable def liftEdgesByForget (Gf : FeynmanGraph) {M : Multiset FeynmanEdge}
    (h : M ≤ Gf.internalEdges) : Multiset ResolvedFeynmanEdge :=
  (exists_le_map ResolvedFeynmanEdge.forget (s := uniqueIdEdges Gf.internalEdges)
    (M := M) (by rw [map_forget_uniqueIdEdges]; exact h)).choose

theorem liftEdgesByForget_le (Gf : FeynmanGraph) {M : Multiset FeynmanEdge}
    (h : M ≤ Gf.internalEdges) : liftEdgesByForget Gf h ≤ uniqueIdEdges Gf.internalEdges :=
  (exists_le_map ResolvedFeynmanEdge.forget (s := uniqueIdEdges Gf.internalEdges)
    (M := M) (by rw [map_forget_uniqueIdEdges]; exact h)).choose_spec.1

@[simp] theorem liftEdgesByForget_forget (Gf : FeynmanGraph) {M : Multiset FeynmanEdge}
    (h : M ≤ Gf.internalEdges) : (liftEdgesByForget Gf h).map ResolvedFeynmanEdge.forget = M :=
  (exists_le_map ResolvedFeynmanEdge.forget (s := uniqueIdEdges Gf.internalEdges)
    (M := M) (by rw [map_forget_uniqueIdEdges]; exact h)).choose_spec.2

/-- Lift a submultiset of the (forgotten) ambient legs to a submultiset of the
ambient tagged legs, preserving `forget`. -/
noncomputable def liftLegsByForget (Gf : FeynmanGraph) {M : Multiset ExternalLeg}
    (h : M ≤ Gf.externalLegs) : Multiset ResolvedExternalLeg :=
  (exists_le_map ResolvedExternalLeg.forget (s := uniqueIdLegs Gf.externalLegs)
    (M := M) (by rw [map_forget_uniqueIdLegs]; exact h)).choose

theorem liftLegsByForget_le (Gf : FeynmanGraph) {M : Multiset ExternalLeg}
    (h : M ≤ Gf.externalLegs) : liftLegsByForget Gf h ≤ uniqueIdLegs Gf.externalLegs :=
  (exists_le_map ResolvedExternalLeg.forget (s := uniqueIdLegs Gf.externalLegs)
    (M := M) (by rw [map_forget_uniqueIdLegs]; exact h)).choose_spec.1

@[simp] theorem liftLegsByForget_forget (Gf : FeynmanGraph) {M : Multiset ExternalLeg}
    (h : M ≤ Gf.externalLegs) : (liftLegsByForget Gf h).map ResolvedExternalLeg.forget = M :=
  (exists_le_map ResolvedExternalLeg.forget (s := uniqueIdLegs Gf.externalLegs)
    (M := M) (by rw [map_forget_uniqueIdLegs]; exact h)).choose_spec.2

/-! ### Step 2 — unique-id subgraph/forest lift -/

/-- (local) flat subgraph extensionality (carrier determines the subgraph). -/
private theorem feynmanSubgraph_ext' {G : FeynmanGraph} {γ₁ γ₂ : FeynmanSubgraph G}
    (hv : γ₁.vertices = γ₂.vertices) (hi : γ₁.internalEdges = γ₂.internalEdges)
    (he : γ₁.externalLegs = γ₂.externalLegs) : γ₁ = γ₂ := by
  cases γ₁; cases γ₂; cases hv; cases hi; cases he; rfl

/-- A subgraph of the forgotten unique-id graph has its edges in `Gf`. -/
theorem subgraphEdges_le {Gf : FeynmanGraph}
    (γf : FeynmanSubgraph (ofFlatGraphWithUniqueIds Gf).forget) :
    γf.internalEdges ≤ Gf.internalEdges := by
  have := γf.internalEdges_le
  rwa [congrArg FeynmanGraph.internalEdges (forget_ofFlatGraphWithUniqueIds Gf)] at this

theorem subgraphLegs_le {Gf : FeynmanGraph}
    (γf : FeynmanSubgraph (ofFlatGraphWithUniqueIds Gf).forget) :
    γf.externalLegs ≤ Gf.externalLegs := by
  have := γf.externalLegs_le
  rwa [congrArg FeynmanGraph.externalLegs (forget_ofFlatGraphWithUniqueIds Gf)] at this

/-- Unique-id lift of a subgraph of `(ofFlatGraphWithUniqueIds Gf).forget`: edges/legs
are lifted as occurrence-faithful submultiset preimages of the ambient tagged ones. -/
noncomputable def liftUniqueFromForgetSubgraph
    (γf : FeynmanSubgraph (ofFlatGraphWithUniqueIds Gf).forget) :
    ResolvedFeynmanSubgraph (ofFlatGraphWithUniqueIds Gf) where
  vertices := γf.vertices
  internalEdges := liftEdgesByForget Gf (subgraphEdges_le γf)
  externalLegs := liftLegsByForget Gf (subgraphLegs_le γf)
  vertices_subset := γf.vertices_subset
  internalEdges_le := by
    rw [ofFlatGraphWithUniqueIds_internalEdges]; exact liftEdgesByForget_le Gf (subgraphEdges_le γf)
  externalLegs_le := by
    rw [ofFlatGraphWithUniqueIds_externalLegs]; exact liftLegsByForget_le Gf (subgraphLegs_le γf)
  edges_supported := by
    intro e he
    have hfe : e.forget ∈ γf.internalEdges := by
      have hmem : e.forget ∈
          (liftEdgesByForget Gf (subgraphEdges_le γf)).map ResolvedFeynmanEdge.forget :=
        Multiset.mem_map_of_mem _ he
      rwa [liftEdgesByForget_forget] at hmem
    simpa [FeynmanEdge.SupportedOn, ResolvedFeynmanEdge.forget]
      using γf.edges_supported e.forget hfe
  legs_supported := by
    intro ℓ hℓ
    have hfℓ : ℓ.forget ∈ γf.externalLegs := by
      have hmem : ℓ.forget ∈
          (liftLegsByForget Gf (subgraphLegs_le γf)).map ResolvedExternalLeg.forget :=
        Multiset.mem_map_of_mem _ hℓ
      rwa [liftLegsByForget_forget] at hmem
    simpa [ExternalLeg.SupportedOn, ResolvedExternalLeg.forget]
      using γf.legs_supported ℓ.forget hfℓ

@[simp] theorem liftUniqueFromForgetSubgraph_forget_internalEdges
    (γf : FeynmanSubgraph (ofFlatGraphWithUniqueIds Gf).forget) :
    (liftUniqueFromForgetSubgraph γf).forget.internalEdges = γf.internalEdges := by
  show (liftEdgesByForget Gf (subgraphEdges_le γf)).map ResolvedFeynmanEdge.forget = γf.internalEdges
  exact liftEdgesByForget_forget Gf (subgraphEdges_le γf)

@[simp] theorem liftUniqueFromForgetSubgraph_forget_externalLegs
    (γf : FeynmanSubgraph (ofFlatGraphWithUniqueIds Gf).forget) :
    (liftUniqueFromForgetSubgraph γf).forget.externalLegs = γf.externalLegs := by
  show (liftLegsByForget Gf (subgraphLegs_le γf)).map ResolvedExternalLeg.forget = γf.externalLegs
  exact liftLegsByForget_forget Gf (subgraphLegs_le γf)

/-- The unique-id subgraph lift round-trips (same forgetful ambient). -/
theorem forget_liftUniqueFromForgetSubgraph
    (γf : FeynmanSubgraph (ofFlatGraphWithUniqueIds Gf).forget) :
    (liftUniqueFromForgetSubgraph γf).forget = γf :=
  feynmanSubgraph_ext' rfl
    (liftUniqueFromForgetSubgraph_forget_internalEdges γf)
    (liftUniqueFromForgetSubgraph_forget_externalLegs γf)

end GaugeGeometry.QFT.Combinatorial
