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

/-- The unique-id subgraph lift is injective (forget is a left inverse). -/
theorem liftUniqueFromForgetSubgraph_injective {Gf : FeynmanGraph} :
    Function.Injective (liftUniqueFromForgetSubgraph (Gf := Gf)) := by
  intro γ₁ γ₂ h
  have := congrArg ResolvedFeynmanSubgraph.forget h
  rwa [forget_liftUniqueFromForgetSubgraph, forget_liftUniqueFromForgetSubgraph] at this

/-- Per-component edge-count is preserved by the unique-id lift. -/
theorem liftUniqueFromForgetSubgraph_internalEdges_card
    (γf : FeynmanSubgraph (ofFlatGraphWithUniqueIds Gf).forget) :
    (liftUniqueFromForgetSubgraph γf).internalEdges.card = γf.internalEdges.card := by
  have h : (liftUniqueFromForgetSubgraph γf).internalEdges.map ResolvedFeynmanEdge.forget
      = γf.internalEdges :=
    (ResolvedFeynmanSubgraph.forget_internalEdges _).symm.trans
      (liftUniqueFromForgetSubgraph_forget_internalEdges γf)
  rw [← Multiset.card_map ResolvedFeynmanEdge.forget, h]

/-! ### Step 2c — unique-id forest lift -/

variable [∀ H : FeynmanGraph, DivergenceMeasure H]
         [∀ H : FeynmanGraph, IsPermInvariantDivergence H]
         [∀ H : FeynmanGraph, IsIsoInvariantDivergence H]
         [∀ H : FeynmanGraph, Fintype (FeynmanSubgraph H)]
         [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
         [IsDivergencePreservedByAdmissibleForestContract]

/-- (local) flat admissible-subgraph extensionality. -/
private theorem admissibleSubgraph_ext' {G : FeynmanGraph} [DivergenceMeasure G]
    {A₁ A₂ : AdmissibleSubgraph G} (h : A₁.elements = A₂.elements) : A₁ = A₂ := by
  obtain ⟨⟨e₁, d₁, nd₁⟩, cd₁⟩ := A₁
  obtain ⟨⟨e₂, d₂, nd₂⟩, cd₂⟩ := A₂
  cases h; rfl

/-- The unique-id lift of a pairwise-disjoint forest of `(ofFlatGraphWithUniqueIds Gf).forget`
to a resolved forest of `ofFlatGraphWithUniqueIds Gf` (transport-free; same forgetful ambient). -/
noncomputable def ofUniqueForgetForest
    (Af : AdmissibleSubgraph (ofFlatGraphWithUniqueIds Gf).forget)
    (hDisj : Af.IsPairwiseDisjoint) :
    ResolvedAdmissibleSubgraph (ofFlatGraphWithUniqueIds Gf) where
  elements := Af.elements.image liftUniqueFromForgetSubgraph
  isConnectedDivergent := by
    intro γ hγ
    obtain ⟨δf, hδf, rfl⟩ := Finset.mem_image.mp hγ
    rw [forget_liftUniqueFromForgetSubgraph]
    exact Af.isConnectedDivergent_of_mem hδf
  pairwiseDisjoint := by
    intro γ₁ h₁ γ₂ h₂ hne
    obtain ⟨δf₁, hδf₁, rfl⟩ := Finset.mem_image.mp h₁
    obtain ⟨δf₂, hδf₂, rfl⟩ := Finset.mem_image.mp h₂
    exact hDisj hδf₁ hδf₂ (fun h => hne (by rw [h]))

@[simp] theorem ofUniqueForgetForest_elements
    (Af : AdmissibleSubgraph (ofFlatGraphWithUniqueIds Gf).forget)
    (hDisj : Af.IsPairwiseDisjoint) :
    (ofUniqueForgetForest Af hDisj).elements = Af.elements.image liftUniqueFromForgetSubgraph := rfl

/-- The unique-id forest lift round-trips (same forgetful ambient, no transport). -/
theorem forget_ofUniqueForgetForest
    (Af : AdmissibleSubgraph (ofFlatGraphWithUniqueIds Gf).forget)
    (hDisj : Af.IsPairwiseDisjoint) : (ofUniqueForgetForest Af hDisj).forget = Af := by
  apply admissibleSubgraph_ext'
  rw [ResolvedAdmissibleSubgraph.forget_elements, ofUniqueForgetForest_elements,
    Finset.image_image,
    show (ResolvedFeynmanSubgraph.forget ∘ liftUniqueFromForgetSubgraph (Gf := Gf))
      = id from funext (fun γf => forget_liftUniqueFromForgetSubgraph γf),
    Finset.image_id]

/-- `Multiset.map forget` distributes over a finite sum of component edges. -/
private theorem map_forget_finset_sum {ι : Type*} (s : Finset ι)
    (f : ι → Multiset ResolvedFeynmanEdge) :
    (∑ i ∈ s, f i).map ResolvedFeynmanEdge.forget
      = ∑ i ∈ s, (f i).map ResolvedFeynmanEdge.forget := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s his ih =>
    rw [Finset.sum_insert his, Finset.sum_insert his, Multiset.map_add, ih]

/-- Forgetting the aggregate edges of the unique-id forest lift recovers the flat
forest's edges (occurrence-faithfully). -/
theorem ofUniqueForgetForest_internalEdges_forget
    (Af : AdmissibleSubgraph (ofFlatGraphWithUniqueIds Gf).forget)
    (hDisj : Af.IsPairwiseDisjoint) :
    (ofUniqueForgetForest Af hDisj).internalEdges.map ResolvedFeynmanEdge.forget
      = Af.internalEdges := by
  show (∑ γ ∈ (ofUniqueForgetForest Af hDisj).elements, γ.internalEdges).map
      ResolvedFeynmanEdge.forget = Af.internalEdges
  rw [ofUniqueForgetForest_elements,
    Finset.sum_image (fun δ₁ _ δ₂ _ h => liftUniqueFromForgetSubgraph_injective h),
    map_forget_finset_sum,
    show Af.internalEdges = ∑ δ ∈ Af.elements, δ.internalEdges from rfl]
  exact Finset.sum_congr rfl (fun δf _ =>
    (ResolvedFeynmanSubgraph.forget_internalEdges _).symm.trans
      (liftUniqueFromForgetSubgraph_forget_internalEdges δf))

/-- Aggregate edge-count is preserved by the unique-id forest lift. -/
theorem ofUniqueForgetForest_internalEdges_card
    (Af : AdmissibleSubgraph (ofFlatGraphWithUniqueIds Gf).forget)
    (hDisj : Af.IsPairwiseDisjoint) :
    (ofUniqueForgetForest Af hDisj).internalEdges.card = Af.internalEdges.card := by
  rw [← Multiset.card_map ResolvedFeynmanEdge.forget,
    ofUniqueForgetForest_internalEdges_forget]

end GaugeGeometry.QFT.Combinatorial
