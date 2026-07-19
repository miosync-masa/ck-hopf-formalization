import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocProperForestMapPerm

/-!
# R-6c-body-417 — the `mapPerm` subgraph/forest equivalences + saturated `carrier_mapPerm` (PROVED)

Four-hundred-and-seventeenth genuine-body step — the `mapPerm` naturality of the ambient-parametric saturated carrier.
Body-416 proved `IsProperForest` is relabeling-invariant; the `carrier_mapPerm` of `saturatedProperForestIndex`
additionally needs SURJECTIVITY of `A ↦ A.mapPerm σ` (`∃ B, B.mapPerm σ = A'`).  Per the design note, that is isolated
into a reusable `Equiv`, sealing the dependent graph-cast in one place.

The key move that keeps everything HEq-free: the inverse is built by DIRECT construction over the FIXED graph `G`
(relabel the value data by `σ.symm`), not by transporting `A.mapPerm σ.symm` across `(G.mapPerm σ).mapPerm σ.symm = G`.
Since a resolved subgraph's value data (`vertices`/`internalEdges`/`externalLegs`) is `G`-independent, the round-trips
are plain equalities over the same graph — no `▸`, no HEq at the `Equiv` level.

* `edge_map_symm_cancel` / … — the four `ResolvedFeynmanEdge`/`ResolvedExternalLeg` `map`∘`map σ.symm` cancels;
* `rfsMapPermEquiv` — `ResolvedFeynmanSubgraph G ≃ ResolvedFeynmanSubgraph (G.mapPerm σ)` (the sealed subgraph bijection);
* `rfsSymm_forget_cd` / `rfsSymm_disjoint` — the connected-divergence / disjointness transport for the `σ.symm` inverse
  (the ONE place HEq is used, via `feynmanSubgraph_heq_of_data` + the reverse flat CD lemma);
* `rasMapPermEquiv` — `ResolvedAdmissibleSubgraph G ≃ ResolvedAdmissibleSubgraph (G.mapPerm σ)`;
* `saturatedProperForestIndex_carrier_mapPerm` — `(saturatedProperForestIndex (G.mapPerm σ)).carrier =
  ((saturatedProperForestIndex G).carrier).image (·.mapPerm σ)` (via `Equiv.symm` + body-416's `iff`).

This lands the `carrier_mapPerm` half of the raw-`W` `index`.  Per the HALT: `hCD` / the ambient-CD emptying
(`cdSupportedIndex`) are the NEXT body (418); no `RawW` inhabitant is assembled here.  No facade, no flat term, no
`forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

set_option linter.unusedSectionVars false

/-- **R-6c-body-417 — `ResolvedFeynmanEdge.map` cancels `σ`/`σ.symm`.** -/
theorem edge_map_symm_cancel (σ : Equiv.Perm VertexId) (e : ResolvedFeynmanEdge) :
    ResolvedFeynmanEdge.map σ.symm (ResolvedFeynmanEdge.map σ e) = e := by
  cases e; simp [ResolvedFeynmanEdge.map]

/-- **R-6c-body-417 — `ResolvedFeynmanEdge.map` cancels `σ.symm`/`σ`.** -/
theorem edge_map_cancel_symm (σ : Equiv.Perm VertexId) (e : ResolvedFeynmanEdge) :
    ResolvedFeynmanEdge.map σ (ResolvedFeynmanEdge.map σ.symm e) = e := by
  cases e; simp [ResolvedFeynmanEdge.map]

/-- **R-6c-body-417 — `ResolvedExternalLeg.map` cancels `σ`/`σ.symm`.** -/
theorem leg_map_symm_cancel (σ : Equiv.Perm VertexId) (ℓ : ResolvedExternalLeg) :
    ResolvedExternalLeg.map σ.symm (ResolvedExternalLeg.map σ ℓ) = ℓ := by
  cases ℓ; simp [ResolvedExternalLeg.map]

/-- **R-6c-body-417 — `ResolvedExternalLeg.map` cancels `σ.symm`/`σ`.** -/
theorem leg_map_cancel_symm (σ : Equiv.Perm VertexId) (ℓ : ResolvedExternalLeg) :
    ResolvedExternalLeg.map σ (ResolvedExternalLeg.map σ.symm ℓ) = ℓ := by
  cases ℓ; simp [ResolvedExternalLeg.map]

/-- **R-6c-body-417 — the subgraph-level relabeling equivalence.**  Inverse built by DIRECT construction over `G`
(value data relabeled by `σ.symm`); round-trips are plain equalities (no dependent cast). -/
noncomputable def rfsMapPermEquiv {G : ResolvedFeynmanGraph} (σ : Equiv.Perm VertexId) :
    ResolvedFeynmanSubgraph G ≃ ResolvedFeynmanSubgraph (G.mapPerm σ) where
  toFun γ := γ.mapPerm σ
  invFun γ' :=
    { vertices := γ'.vertices.image σ.symm
      internalEdges := γ'.internalEdges.map (ResolvedFeynmanEdge.map σ.symm)
      externalLegs := γ'.externalLegs.map (ResolvedExternalLeg.map σ.symm)
      vertices_subset := by
        have h := Finset.image_subset_image (f := (σ.symm : VertexId → VertexId)) γ'.vertices_subset
        rwa [show (G.mapPerm σ).vertices = G.vertices.image σ from rfl, Finset.image_image,
          show (σ.symm : VertexId → VertexId) ∘ σ = id from funext (fun x => σ.symm_apply_apply x),
          Finset.image_id] at h
      internalEdges_le := by
        have h := Multiset.map_le_map (f := ResolvedFeynmanEdge.map σ.symm) γ'.internalEdges_le
        rwa [show (G.mapPerm σ).internalEdges = G.internalEdges.map (ResolvedFeynmanEdge.map σ) from rfl,
          Multiset.map_map, show ResolvedFeynmanEdge.map σ.symm ∘ ResolvedFeynmanEdge.map σ = id from
            funext (edge_map_symm_cancel σ), Multiset.map_id] at h
      externalLegs_le := by
        have h := Multiset.map_le_map (f := ResolvedExternalLeg.map σ.symm) γ'.externalLegs_le
        rwa [show (G.mapPerm σ).externalLegs = G.externalLegs.map (ResolvedExternalLeg.map σ) from rfl,
          Multiset.map_map, show ResolvedExternalLeg.map σ.symm ∘ ResolvedExternalLeg.map σ = id from
            funext (leg_map_symm_cancel σ), Multiset.map_id] at h
      edges_supported := by
        intro e he
        obtain ⟨e₀, he₀, rfl⟩ := Multiset.mem_map.mp he
        obtain ⟨hs, ht⟩ := γ'.edges_supported e₀ he₀
        exact ⟨Finset.mem_image_of_mem σ.symm hs, Finset.mem_image_of_mem σ.symm ht⟩
      legs_supported := by
        intro ℓ hℓ
        obtain ⟨ℓ₀, hℓ₀, rfl⟩ := Multiset.mem_map.mp hℓ
        exact Finset.mem_image_of_mem σ.symm (γ'.legs_supported ℓ₀ hℓ₀) }
  left_inv γ := by
    apply resolvedFeynmanSubgraph_ext
    · show (γ.vertices.image σ).image σ.symm = γ.vertices
      rw [Finset.image_image,
        show (σ.symm : VertexId → VertexId) ∘ σ = id from funext (fun x => σ.symm_apply_apply x),
        Finset.image_id]
    · show (γ.internalEdges.map (ResolvedFeynmanEdge.map σ)).map (ResolvedFeynmanEdge.map σ.symm)
          = γ.internalEdges
      rw [Multiset.map_map, show ResolvedFeynmanEdge.map σ.symm ∘ ResolvedFeynmanEdge.map σ = id from
        funext (edge_map_symm_cancel σ), Multiset.map_id]
    · show (γ.externalLegs.map (ResolvedExternalLeg.map σ)).map (ResolvedExternalLeg.map σ.symm)
          = γ.externalLegs
      rw [Multiset.map_map, show ResolvedExternalLeg.map σ.symm ∘ ResolvedExternalLeg.map σ = id from
        funext (leg_map_symm_cancel σ), Multiset.map_id]
  right_inv γ' := by
    apply resolvedFeynmanSubgraph_ext
    · show (γ'.vertices.image σ.symm).image σ = γ'.vertices
      rw [Finset.image_image,
        show (σ : VertexId → VertexId) ∘ σ.symm = id from funext (fun x => σ.apply_symm_apply x),
        Finset.image_id]
    · show (γ'.internalEdges.map (ResolvedFeynmanEdge.map σ.symm)).map (ResolvedFeynmanEdge.map σ)
          = γ'.internalEdges
      rw [Multiset.map_map, show ResolvedFeynmanEdge.map σ ∘ ResolvedFeynmanEdge.map σ.symm = id from
        funext (edge_map_cancel_symm σ), Multiset.map_id]
    · show (γ'.externalLegs.map (ResolvedExternalLeg.map σ.symm)).map (ResolvedExternalLeg.map σ)
          = γ'.externalLegs
      rw [Multiset.map_map, show ResolvedExternalLeg.map σ ∘ ResolvedExternalLeg.map σ.symm = id from
        funext (leg_map_cancel_symm σ), Multiset.map_id]

@[simp] theorem rfsMapPermEquiv_apply {G : ResolvedFeynmanGraph} (σ : Equiv.Perm VertexId)
    (γ : ResolvedFeynmanSubgraph G) : rfsMapPermEquiv σ γ = γ.mapPerm σ := rfl

@[simp] theorem rfs_symm_vertices {G : ResolvedFeynmanGraph} (σ : Equiv.Perm VertexId)
    (γ' : ResolvedFeynmanSubgraph (G.mapPerm σ)) :
    ((rfsMapPermEquiv σ).symm γ').vertices = γ'.vertices.image σ.symm := rfl

@[simp] theorem rfs_symm_internalEdges {G : ResolvedFeynmanGraph} (σ : Equiv.Perm VertexId)
    (γ' : ResolvedFeynmanSubgraph (G.mapPerm σ)) :
    ((rfsMapPermEquiv σ).symm γ').internalEdges
      = γ'.internalEdges.map (ResolvedFeynmanEdge.map σ.symm) := rfl

@[simp] theorem rfs_symm_externalLegs {G : ResolvedFeynmanGraph} (σ : Equiv.Perm VertexId)
    (γ' : ResolvedFeynmanSubgraph (G.mapPerm σ)) :
    ((rfsMapPermEquiv σ).symm γ').externalLegs
      = γ'.externalLegs.map (ResolvedExternalLeg.map σ.symm) := rfl

/-- **R-6c-body-417 — connected-divergence transports through the `σ.symm` inverse** (the ONE place `HEq` is used, via
`feynmanSubgraph_heq_of_data` + the graph cancel + the flat reverse CD lemma). -/
theorem rfsSymm_forget_cd {G : ResolvedFeynmanGraph} (σ : Equiv.Perm VertexId)
    (γ' : ResolvedFeynmanSubgraph (G.mapPerm σ)) (h : γ'.forget.IsConnectedDivergent) :
    ((rfsMapPermEquiv σ).symm γ').forget.IsConnectedDivergent := by
  have hcancel : (G.mapPerm σ).mapPerm σ.symm = G := by
    rw [← ResolvedFeynmanGraph.mapPerm_mul]; simp
  refine feynmanSubgraph_isConnectedDivergent_of_heq
    (((congrArg ResolvedFeynmanGraph.forget hcancel).symm).trans
      (ResolvedFeynmanGraph.forget_mapPerm σ.symm (G.mapPerm σ))) ?_
    (FeynmanSubgraph.mapPerm_isConnectedDivergent σ.symm h)
  refine feynmanSubgraph_heq_of_data
    (((congrArg ResolvedFeynmanGraph.forget hcancel).symm).trans
      (ResolvedFeynmanGraph.forget_mapPerm σ.symm (G.mapPerm σ))) ?_ ?_ ?_
  · simp only [ResolvedFeynmanSubgraph.forget_vertices, rfs_symm_vertices,
      FeynmanSubgraph.mapPerm_vertices]
  · simp only [ResolvedFeynmanSubgraph.forget_internalEdges, rfs_symm_internalEdges,
      FeynmanSubgraph.mapPerm_internalEdges, Multiset.map_map]
    exact Multiset.map_congr rfl (fun e _ => by
      simp [ResolvedFeynmanEdge.map, ResolvedFeynmanEdge.forget, FeynmanEdge.map])
  · simp only [ResolvedFeynmanSubgraph.forget_externalLegs, rfs_symm_externalLegs,
      FeynmanSubgraph.mapPerm_externalLegs, Multiset.map_map]
    exact Multiset.map_congr rfl (fun l _ => by
      simp [ResolvedExternalLeg.map, ResolvedExternalLeg.forget, ExternalLeg.map])

/-- **R-6c-body-417 — disjointness transports through the `σ.symm` inverse** (vertex-disjointness + `σ.symm` injective). -/
theorem rfsSymm_disjoint {G : ResolvedFeynmanGraph} (σ : Equiv.Perm VertexId)
    {γ' δ' : ResolvedFeynmanSubgraph (G.mapPerm σ)} (h : γ'.Disjoint δ') :
    ((rfsMapPermEquiv σ).symm γ').Disjoint ((rfsMapPermEquiv σ).symm δ') := by
  unfold ResolvedFeynmanSubgraph.Disjoint at h ⊢
  simp only [rfs_symm_vertices]
  exact (Finset.disjoint_image σ.symm.injective).mpr h

/-- **R-6c-body-417 — the forest-level relabeling equivalence.**  Elements ride through `rfsMapPermEquiv`; the inverse's
connected-divergence / disjointness use `rfsSymm_forget_cd` / `rfsSymm_disjoint`. -/
noncomputable def rasMapPermEquiv {G : ResolvedFeynmanGraph} (σ : Equiv.Perm VertexId) :
    ResolvedAdmissibleSubgraph G ≃ ResolvedAdmissibleSubgraph (G.mapPerm σ) where
  toFun A := A.mapPerm σ
  invFun A' :=
    { elements := A'.elements.image (fun γ' => (rfsMapPermEquiv σ).symm γ')
      isConnectedDivergent := by
        intro γ hγ
        obtain ⟨γ', hγ', rfl⟩ := Finset.mem_image.mp hγ
        exact rfsSymm_forget_cd σ γ' (A'.isConnectedDivergent γ' hγ')
      pairwiseDisjoint := by
        intro γ hγ δ hδ hne
        obtain ⟨γ', hγ', rfl⟩ := Finset.mem_image.mp hγ
        obtain ⟨δ', hδ', rfl⟩ := Finset.mem_image.mp hδ
        exact rfsSymm_disjoint σ (A'.pairwiseDisjoint hγ' hδ' (fun h => hne (by rw [h]))) }
  left_inv A := by
    apply ResolvedAdmissibleSubgraph.ext_elements
    ext γ
    simp only [ResolvedAdmissibleSubgraph.mapPerm_elements, Finset.mem_image]
    constructor
    · rintro ⟨γ', ⟨γ₀, hγ₀, rfl⟩, rfl⟩
      have h0 : (rfsMapPermEquiv σ).symm (γ₀.mapPerm σ) = γ₀ :=
        (rfsMapPermEquiv σ).symm_apply_apply γ₀
      rwa [h0]
    · intro hγ
      exact ⟨γ.mapPerm σ, ⟨γ, hγ, rfl⟩, (rfsMapPermEquiv σ).symm_apply_apply γ⟩
  right_inv A' := by
    apply ResolvedAdmissibleSubgraph.ext_elements
    ext γ'
    simp only [ResolvedAdmissibleSubgraph.mapPerm_elements, Finset.mem_image]
    constructor
    · rintro ⟨γ, ⟨γ₀, hγ₀, rfl⟩, rfl⟩
      have h0 : ((rfsMapPermEquiv σ).symm γ₀).mapPerm σ = γ₀ :=
        (rfsMapPermEquiv σ).apply_symm_apply γ₀
      rwa [h0]
    · intro hγ'
      exact ⟨(rfsMapPermEquiv σ).symm γ', ⟨γ', hγ', rfl⟩, (rfsMapPermEquiv σ).apply_symm_apply γ'⟩

@[simp] theorem rasMapPermEquiv_apply {G : ResolvedFeynmanGraph} (σ : Equiv.Perm VertexId)
    (A : ResolvedAdmissibleSubgraph G) : rasMapPermEquiv σ A = A.mapPerm σ := rfl

/-- **R-6c-body-417 ∎ — the saturated proper-forest carrier is `mapPerm`-natural.**  The reverse inclusion uses the
forest equivalence's surjectivity (`rasMapPermEquiv.symm`); both inclusions use body-416's `isProperForest_mapPerm_iff`.
This is the `carrier_mapPerm` field for the raw-`W` `index := saturatedProperForestIndex`. -/
theorem saturatedProperForestIndex_carrier_mapPerm {G : ResolvedFeynmanGraph}
    (σ : Equiv.Perm VertexId) :
    (saturatedProperForestIndex (G.mapPerm σ)).carrier
      = (saturatedProperForestIndex G).carrier.image (fun A => A.mapPerm σ) := by
  ext A'
  simp only [saturatedProperForestIndex, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_image]
  constructor
  · intro hA'
    have key : ((rasMapPermEquiv σ).symm A').mapPerm σ = A' :=
      (rasMapPermEquiv σ).apply_symm_apply A'
    refine ⟨(rasMapPermEquiv σ).symm A', ?_, key⟩
    rw [← isProperForest_mapPerm_iff σ ((rasMapPermEquiv σ).symm A'), key]
    exact hA'
  · rintro ⟨A, hA, rfl⟩
    exact isProperForest_mapPerm σ hA

end GaugeGeometry.QFT.Combinatorial
