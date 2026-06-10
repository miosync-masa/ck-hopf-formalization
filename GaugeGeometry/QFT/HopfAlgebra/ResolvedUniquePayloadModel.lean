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

/-! ### Step 3 — id-unique payload family

The one new structural lemma needed (the unique-id lift is not a clean map, so the
constant-id `map_le_map` route does not transfer): a *resolved* pairwise-disjoint
forest has its aggregate edges contained in the ambient — proved by the count
argument, mirroring the flat `admissibleSubgraph_internalEdges_le_of_pairwise`. -/

/-- A resolved edge of a forest lies in some component. -/
private theorem resolved_mem_internalEdges {G : ResolvedFeynmanGraph}
    {A : ResolvedAdmissibleSubgraph G} {e : ResolvedFeynmanEdge}
    (he : e ∈ A.internalEdges) : ∃ γ ∈ A.elements, e ∈ γ.internalEdges := by
  classical
  have hpos : 0 < Multiset.count e A.internalEdges := Multiset.count_pos.mpr he
  unfold ResolvedAdmissibleSubgraph.internalEdges at hpos
  rw [multiset_count_finset_sum] at hpos
  obtain ⟨γ, hγ, hγ0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos.ne'
  exact ⟨γ, hγ, Multiset.count_ne_zero.mp hγ0⟩

/-- **Resolved disjoint-forest edge containment.**  A pairwise-disjoint resolved
forest has its aggregate internal edges below the ambient (count argument via
vertex-disjointness + component `internalEdges_le`). Mirrors the flat lemma. -/
theorem resolvedAdmissibleSubgraph_internalEdges_le_of_pairwise
    {G : ResolvedFeynmanGraph} (A : ResolvedAdmissibleSubgraph G)
    (hA : A.IsPairwiseDisjoint) : A.internalEdges ≤ G.internalEdges := by
  classical
  rw [Multiset.le_iff_count]
  intro e
  by_cases heA : e ∈ A.internalEdges
  · obtain ⟨γ, hγ, heγ⟩ := resolved_mem_internalEdges heA
    have hzero : ∀ δ ∈ A.elements, δ ≠ γ → δ.internalEdges.count e = 0 := by
      intro δ hδ hne
      by_cases heδ : e ∈ δ.internalEdges
      · have hdisj := hA hδ hγ hne
        have hsuppδ := δ.edges_supported e heδ
        have hsuppγ := γ.edges_supported e heγ
        exact False.elim ((Finset.disjoint_left.mp hdisj hsuppδ.1) hsuppγ.1)
      · exact Multiset.count_eq_zero.mpr heδ
    unfold ResolvedAdmissibleSubgraph.internalEdges
    rw [multiset_count_finset_sum]
    calc (∑ x ∈ A.elements, Multiset.count e x.internalEdges)
        = γ.internalEdges.count e := by
          rw [Finset.sum_eq_single γ]
          · intro δ hδ hne; exact hzero δ hδ hne
          · intro hγnot; exact False.elim (hγnot hγ)
      _ ≤ G.internalEdges.count e := Multiset.count_le_of_le e γ.internalEdges_le
  · rw [Multiset.count_eq_zero.mpr heA]; exact Nat.zero_le _

/-- (local) resolved admissible-subgraph extensionality (determined by `elements`). -/
private theorem resolvedAdmissibleSubgraph_ext' {G : ResolvedFeynmanGraph}
    {A₁ A₂ : ResolvedAdmissibleSubgraph G} (h : A₁.elements = A₂.elements) : A₁ = A₂ := by
  obtain ⟨e₁, cd₁, pd₁⟩ := A₁; obtain ⟨e₂, cd₂, pd₂⟩ := A₂; cases h; rfl

/-- A flat proper forest of `(ofFlatGraphWithUniqueIds Gf).forget` lifts to a resolved
proper forest of the unique-id graph (transport-free; card conditions via forget). -/
theorem ofUniqueForgetForest_isProperForest
    (Af : AdmissibleSubgraph (ofFlatGraphWithUniqueIds Gf).forget)
    (hAf : Af ∈ ((ofFlatGraphWithUniqueIds Gf).forget.properDisjointAdmissibleDivergentSubgraphs).filter
      (fun A => 0 < A.complementEdges.card))
    (hDisj : Af.IsPairwiseDisjoint) :
    (ofUniqueForgetForest Af hDisj).IsProperForest := by
  rw [Finset.mem_filter] at hAf
  obtain ⟨hpd, hcompl⟩ := hAf
  rw [FeynmanGraph.mem_properDisjointAdmissibleDivergentSubgraphs] at hpd
  obtain ⟨hnd, hhnc, hiec, hhpiec⟩ := hpd
  rw [FeynmanGraph.mem_nonemptyDisjointAdmissibleDivergentSubgraphs] at hnd
  obtain ⟨_, hne⟩ := hnd
  refine ⟨hne.image _, ?_, ?_, ?_, ?_⟩
  · intro γ hγ
    obtain ⟨δf, hδf, rfl⟩ := Finset.mem_image.mp hγ
    simpa [ResolvedFeynmanSubgraph.IsNonempty, ResolvedFeynmanSubgraph.vertexCount,
      FeynmanSubgraph.IsNonempty, FeynmanSubgraph.vertexCount] using hhnc δf hδf
  · rw [ofUniqueForgetForest_internalEdges_card]; exact hiec
  · intro γ hγ
    obtain ⟨δf, hδf, rfl⟩ := Finset.mem_image.mp hγ
    rw [liftUniqueFromForgetSubgraph_internalEdges_card]; exact hhpiec δf hδf
  · have hle' : Af.internalEdges ≤ Gf.internalEdges := by
      have hle := admissibleSubgraph_internalEdges_le_of_pairwise Af hDisj
      rwa [congrArg FeynmanGraph.internalEdges (forget_ofFlatGraphWithUniqueIds Gf)] at hle
    have hleR : (ofUniqueForgetForest Af hDisj).internalEdges
        ≤ (ofFlatGraphWithUniqueIds Gf).internalEdges :=
      resolvedAdmissibleSubgraph_internalEdges_le_of_pairwise _
        (ofUniqueForgetForest Af hDisj).isPairwiseDisjoint
    have hambient : (ofFlatGraphWithUniqueIds Gf).internalEdges.card = Gf.internalEdges.card := by
      rw [ofFlatGraphWithUniqueIds_internalEdges, ← Multiset.card_map ResolvedFeynmanEdge.forget,
        map_forget_uniqueIdEdges]
    have hcard : (ofUniqueForgetForest Af hDisj).complementEdges.card = Af.complementEdges.card := by
      show ((ofFlatGraphWithUniqueIds Gf).internalEdges
          - (ofUniqueForgetForest Af hDisj).internalEdges).card
          = ((ofFlatGraphWithUniqueIds Gf).forget.internalEdges - Af.internalEdges).card
      rw [Multiset.card_sub hleR, ofUniqueForgetForest_internalEdges_card, hambient,
        congrArg FeynmanGraph.internalEdges (forget_ofFlatGraphWithUniqueIds Gf),
        Multiset.card_sub hle']
    rw [hcard]; exact hcompl

/-- The canonical unique-id finite proper-forest cover of `ofFlatGraphWithUniqueIds (repG g)`. -/
noncomputable def canonicalUniqueCover (g : HopfGen) :
    ResolvedProperForestFiniteCover (ofFlatGraphWithUniqueIds (repG g).toFeynmanGraph) where
  index :=
    { carrier := (((ofFlatGraphWithUniqueIds (repG g).toFeynmanGraph).forget.properDisjointAdmissibleDivergentSubgraphs).filter
          (fun A => 0 < A.complementEdges.card)).attach.image
        (fun A => ofUniqueForgetForest A.1
          (FeynmanGraph.properDisjointAdmissibleDivergentSubgraphs_isPairwiseDisjoint _
            (Finset.mem_filter.mp A.2).1))
      mem_proper := by
        intro Ares hAres
        obtain ⟨⟨Af, hAf⟩, _, rfl⟩ := Finset.mem_image.mp hAres
        exact ofUniqueForgetForest_isProperForest Af hAf _ }
  forget_complete := by
    intro Aflat hAflat
    refine ⟨ofUniqueForgetForest Aflat
      (FeynmanGraph.properDisjointAdmissibleDivergentSubgraphs_isPairwiseDisjoint _
        (Finset.mem_filter.mp hAflat).1), ?_, forget_ofUniqueForgetForest _ _⟩
    exact Finset.mem_image.mpr ⟨⟨Aflat, hAflat⟩, Finset.mem_attach _ _, rfl⟩
  forget_injective := by
    intro A₁ hA₁ A₂ hA₂ heq
    obtain ⟨⟨B₁, hB₁⟩, _, rfl⟩ := Finset.mem_image.mp hA₁
    obtain ⟨⟨B₂, hB₂⟩, _, rfl⟩ := Finset.mem_image.mp hA₂
    rw [forget_ofUniqueForgetForest, forget_ofUniqueForgetForest] at heq
    apply resolvedAdmissibleSubgraph_ext'
    rw [ofUniqueForgetForest_elements, ofUniqueForgetForest_elements, heq]

/-- The canonical **unique-id** resolved Hopf payload for `g`: the unique-id lift of
`repG g`, with its proper-forest cover. -/
noncomputable def canonicalUniqueResolvedHopfPayload (g : HopfGen) : ResolvedHopfPayload g where
  G := ofFlatGraphWithUniqueIds (repG g).toFeynmanGraph
  forget_eq := forget_ofFlatGraphWithUniqueIds (repG g).toFeynmanGraph
  cover := canonicalUniqueCover g

/-- The unique-id payload carrier has unique edge ids. -/
theorem canonicalUniquePayload_edgeIdsUnique (g : HopfGen) :
    (canonicalUniqueResolvedHopfPayload g).G.EdgeIdsUnique :=
  edgeIdsUnique_ofFlatGraphWithUniqueIds (repG g).toFeynmanGraph

/-- The unique-id payload carrier has unique leg ids. -/
theorem canonicalUniquePayload_legIdsUnique (g : HopfGen) :
    (canonicalUniqueResolvedHopfPayload g).G.LegIdsUnique :=
  legIdsUnique_ofFlatGraphWithUniqueIds (repG g).toFeynmanGraph

/-- The canonical **unique-id** resolved Hopf payload family. -/
noncomputable def canonicalUniqueResolvedHopfPayloadFamily : ResolvedHopfPayloadFamily where
  payload := canonicalUniqueResolvedHopfPayload
  hCD := fun g =>
    FeynmanGraph.admissibleForestCanonicalContractGraph_hCD_of_ambient_preservation
      ((ofFlatGraphWithUniqueIds (repG g).toFeynmanGraph).forget)
      ((forget_ofFlatGraphWithUniqueIds (repG g).toFeynmanGraph).symm ▸ repG_wellFormed g)
      ((forget_ofFlatGraphWithUniqueIds (repG g).toFeynmanGraph).symm ▸ repG_isOnePI g)
      ((forget_ofFlatGraphWithUniqueIds (repG g).toFeynmanGraph).symm ▸ repG_isConnectedDivergent g)

/-- A payload family whose every carrier graph satisfies the identity-uniqueness
hypotheses required by the resolved boundary repair theorems. -/
structure ResolvedHopfPayloadFamilyWithUniqueIds extends ResolvedHopfPayloadFamily where
  edgeIdsUnique : ∀ g, (payload g).G.EdgeIdsUnique
  legIdsUnique : ∀ g, (payload g).G.LegIdsUnique

/-- The canonical id-unique payload family. -/
noncomputable def canonicalResolvedHopfPayloadFamilyWithUniqueIds :
    ResolvedHopfPayloadFamilyWithUniqueIds where
  toResolvedHopfPayloadFamily := canonicalUniqueResolvedHopfPayloadFamily
  edgeIdsUnique := canonicalUniquePayload_edgeIdsUnique
  legIdsUnique := canonicalUniquePayload_legIdsUnique

/-- **R-4-superfull Step 3 headline.**  The id-unique resolved payload family is
inhabited: a canonical unique-id lift supplies, for every generator, a payload whose
carrier graph satisfies `EdgeIdsUnique` and `LegIdsUnique` — exactly the hypotheses
the resolved boundary repair theorems (`parent_eq_of_remainder_eq`,
`externalLegs_lift_unique`) require. -/
theorem resolvedHopfPayloadFamilyWithUniqueIds_exists :
    Nonempty ResolvedHopfPayloadFamilyWithUniqueIds :=
  ⟨canonicalResolvedHopfPayloadFamilyWithUniqueIds⟩

end GaugeGeometry.QFT.Combinatorial
