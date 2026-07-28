import GaugeGeometry.QFT.HopfAlgebra.Phi4CoproductEntrance
import GaugeGeometry.QFT.HopfAlgebra.Coproduct

/-!
# QFT-R1-body-570 — representative-level φ⁴ coproduct invariance

Body-569 assembled the representative-level φ⁴ coproduct `coproductGen_phi4`.  This body proves that
representative is **invariant under vertex renaming (`mapPerm`) and under graph isomorphism** — the
`Finset.sum_bij` reindex that mirrors the existing (old-layer) H4.6 proof
`coproductGen_isomorphism_invariant`, transported to the family-indexed φ⁴ world.

## Contents

* Step 0 (support) `FeynmanSubgraph.contract_mapPerm_toClass_eq` — the cross-ambient contract-class
  transport `(γ.mapPerm π).contract.toClass = γ.contract.toClass`.  The old-layer public wrapper
  `mapPermSubgraph_contract_toClass_eq` carries auto-bound `[∀ G, DivergenceMeasure G] / IsPermInvariant /
  IsIsoInvariant` binders that are **not** inhabitable in the family-indexed φ⁴ world (body-564), so the
  private `contract_mapPerm_isIso` witness is re-derived here instance-free.
* Step 1 `FeynmanGraph.toPhi4HopfGen_mapPerm` — the ambient generator is rename-stable.
* Step 2 `FeynmanSubgraph.contractToPhi4HopfGen_mapPerm` — the right factor is rename-stable.
* Step 3 `FeynmanGraph.phi4ConnectedStrictSummand_mapPerm` — each connected summand is rename-stable.
* Step 4/5 `FeynmanGraph.coproductGen_phi4_mapPerm` — the full representative coproduct is rename-stable
  (`Finset.sum_bij` on the proper connected-divergent index).
* `FeynmanGraph.coproductGen_phi4_isomorphism_invariant` — the isomorphism-phrased corollary.

Per the HALT: no old coproduct / `HopfH` / generator constructors; no `Quotient.lift` / `Quotient.out` /
`aeval` / class-level coproduct; no coassociativity / forest / W″; ZERO new `class` / `structure` /
`instance`.  The old Perm/Iso/ambient divergence classes are neither inhabited nor consumed.
-/

open scoped TensorProduct

namespace GaugeGeometry.QFT.Combinatorial

variable {G : FeynmanGraph}

/-! ## Step 0 — cross-ambient contract-class transport (instance-free)

The three `feynmanSubgraph_cast_*` lemmas project the data fields of a subgraph through an ambient-graph
equality; used both for surjectivity of the index reindex and as scaffolding.  The `freshAlignedPerm`
block re-derives the private Coproduct witness `contract_mapPerm_isIso` **without** the old-layer instance
binders. -/

private theorem feynmanSubgraph_cast_vertices {A B : FeynmanGraph} (h : A = B)
    (x : FeynmanSubgraph A) : (h ▸ x).vertices = x.vertices := by cases h; rfl

private theorem feynmanSubgraph_cast_internalEdges {A B : FeynmanGraph} (h : A = B)
    (x : FeynmanSubgraph A) : (h ▸ x).internalEdges = x.internalEdges := by cases h; rfl

private theorem feynmanSubgraph_cast_externalLegs {A B : FeynmanGraph} (h : A = B)
    (x : FeynmanSubgraph A) : (h ▸ x).externalLegs = x.externalLegs := by cases h; rfl

/-- `map` commutes with truncated subtraction along an injective map (redeclared instance-free). -/
private theorem map_sub_of_injective {α β : Type*}
    [DecidableEq α] [DecidableEq β] {f : α → β}
    (hf : Function.Injective f) {A B : Multiset α} (hle : B ≤ A) :
    (A - B).map f = A.map f - B.map f := by
  refine Multiset.ext.mpr (fun y => ?_)
  rw [Multiset.count_sub]
  by_cases hy : y ∈ A.map f
  · rcases Multiset.mem_map.mp hy with ⟨x, hxA, rfl⟩
    rw [Multiset.count_map_eq_count' _ _ hf,
        Multiset.count_map_eq_count' _ _ hf,
        Multiset.count_map_eq_count' _ _ hf,
        Multiset.count_sub]
  · have hBmap_le : B.map f ≤ A.map f := Multiset.map_le_map hle
    have hy_B : y ∉ B.map f := fun hyB => hy (Multiset.mem_of_le hBmap_le hyB)
    have hy_sub : y ∉ (A - B).map f := by
      intro h
      rcases Multiset.mem_map.mp h with ⟨x, hx, rfl⟩
      have hxA : x ∈ A := Multiset.mem_of_le (Multiset.sub_le_self _ _) hx
      exact hy (Multiset.mem_map.mpr ⟨x, hxA, rfl⟩)
    rw [Multiset.count_eq_zero_of_notMem hy_sub,
        Multiset.count_eq_zero_of_notMem hy,
        Multiset.count_eq_zero_of_notMem hy_B]

namespace FeynmanSubgraph

variable {G : FeynmanGraph}

/-- `τ` carrying `s₁ := freshVertex G.vertices` to `s₂ := freshVertex (G.mapPerm π).vertices` while
preserving `π`'s action on `G.vertices`. -/
private noncomputable def freshAlignedPerm
    (G : FeynmanGraph) (π : Equiv.Perm VertexId) : Equiv.Perm VertexId :=
  Equiv.swap (FeynmanGraph.freshVertex (G.mapPerm π).vertices)
    (π (FeynmanGraph.freshVertex G.vertices)) * π

private theorem freshAlignedPerm_apply_s₁
    (G : FeynmanGraph) (π : Equiv.Perm VertexId) :
    freshAlignedPerm G π (FeynmanGraph.freshVertex G.vertices) =
      FeynmanGraph.freshVertex (G.mapPerm π).vertices := by
  unfold freshAlignedPerm
  simp [Equiv.swap_apply_right]

private theorem vertices_mapPerm (G : FeynmanGraph) (π : Equiv.Perm VertexId) :
    (G.mapPerm π).vertices = G.vertices.image π := rfl

private theorem mem_vertices_mapPerm {G : FeynmanGraph} {π : Equiv.Perm VertexId}
    {v : VertexId} (hv : v ∈ G.vertices) : π v ∈ (G.mapPerm π).vertices := by
  rw [vertices_mapPerm]
  exact Finset.mem_image.mpr ⟨v, hv, rfl⟩

private theorem freshVertex_mapPerm_not_mem
    (G : FeynmanGraph) (π : Equiv.Perm VertexId) :
    FeynmanGraph.freshVertex (G.mapPerm π).vertices ∉ (G.mapPerm π).vertices :=
  FeynmanGraph.freshVertex_not_mem _

private theorem freshAlignedPerm_apply_of_mem
    {G : FeynmanGraph} {π : Equiv.Perm VertexId}
    {v : VertexId} (hv : v ∈ G.vertices) :
    freshAlignedPerm G π v = π v := by
  unfold freshAlignedPerm
  show Equiv.swap (FeynmanGraph.freshVertex (G.mapPerm π).vertices)
        (π (FeynmanGraph.freshVertex G.vertices)) (π v) = π v
  have hπv_mem : π v ∈ (G.mapPerm π).vertices := mem_vertices_mapPerm hv
  have hs₁_notmem : FeynmanGraph.freshVertex G.vertices ∉ G.vertices :=
    FeynmanGraph.freshVertex_not_mem _
  have hπs₁_notmem : π (FeynmanGraph.freshVertex G.vertices) ∉ (G.mapPerm π).vertices := by
    rw [vertices_mapPerm]
    intro h
    rcases Finset.mem_image.mp h with ⟨w, hw, hwπ⟩
    have : w = FeynmanGraph.freshVertex G.vertices := π.injective hwπ
    exact hs₁_notmem (this ▸ hw)
  have hne_s₂ : π v ≠ FeynmanGraph.freshVertex (G.mapPerm π).vertices := fun h =>
    (freshVertex_mapPerm_not_mem G π) (h ▸ hπv_mem)
  have hne_πs₁ : π v ≠ π (FeynmanGraph.freshVertex G.vertices) := fun h =>
    hπs₁_notmem (h ▸ hπv_mem)
  rw [Equiv.swap_apply_of_ne_of_ne hne_s₂ hne_πs₁]

private theorem contract_mapPerm_vertices_eq
    {G : FeynmanGraph} (_hGwf : G.WellFormed)
    (γ : FeynmanSubgraph G) (π : Equiv.Perm VertexId) :
    (γ.contract.mapPerm (freshAlignedPerm G π)).vertices =
      (γ.mapPerm π).contract.vertices := by
  show ((G.vertices \ γ.vertices) ∪
          {FeynmanGraph.freshVertex G.vertices}).image
        (freshAlignedPerm G π) =
      ((G.mapPerm π).vertices \ (γ.mapPerm π).vertices) ∪
        {FeynmanGraph.freshVertex (G.mapPerm π).vertices}
  rw [Finset.image_union, Finset.image_singleton, freshAlignedPerm_apply_s₁]
  congr 1
  ext w
  constructor
  · intro hw
    rw [Finset.mem_image] at hw
    rcases hw with ⟨v, hv_sdiff, hτv⟩
    rw [Finset.mem_sdiff] at hv_sdiff
    obtain ⟨hvG, hvγ⟩ := hv_sdiff
    have hτeqπ : freshAlignedPerm G π v = π v := freshAlignedPerm_apply_of_mem hvG
    rw [hτeqπ] at hτv
    subst hτv
    rw [Finset.mem_sdiff, vertices_mapPerm]
    refine ⟨mem_vertices_mapPerm hvG, ?_⟩
    intro h
    rcases Finset.mem_image.mp h with ⟨u, hu, huπ⟩
    have : u = v := π.injective huπ
    exact hvγ (this ▸ hu)
  · intro hw
    rw [Finset.mem_sdiff, vertices_mapPerm] at hw
    obtain ⟨hwG, hwγ⟩ := hw
    rcases Finset.mem_image.mp hwG with ⟨v, hvG, rfl⟩
    rw [Finset.mem_image]
    refine ⟨v, Finset.mem_sdiff.mpr ⟨hvG, ?_⟩, ?_⟩
    · intro hv
      apply hwγ
      show π v ∈ (γ.mapPerm π).vertices
      exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
    · exact freshAlignedPerm_apply_of_mem hvG

private theorem contract_mapPerm_isIso
    {G : FeynmanGraph} (hGwf : G.WellFormed)
    (γ : FeynmanSubgraph G) (π : Equiv.Perm VertexId) :
    γ.contract.IsIso (γ.mapPerm π).contract := by
  refine ⟨freshAlignedPerm G π, ?_⟩
  apply FeynmanGraph.mk.injEq _ _ _ _ _ _ |>.mpr
  refine ⟨?_, ?_, ?_⟩
  · show (γ.mapPerm π).contract.vertices =
      (γ.contract.mapPerm (freshAlignedPerm G π)).vertices
    exact (contract_mapPerm_vertices_eq hGwf γ π).symm
  · show (γ.mapPerm π).contract.internalEdges =
      γ.contract.internalEdges.map (FeynmanEdge.map (freshAlignedPerm G π))
    show (γ.mapPerm π).complementEdges.map
          (FeynmanEdge.retarget (γ.mapPerm π).vertices
            (FeynmanGraph.freshVertex (G.mapPerm π).vertices)) =
      (γ.complementEdges.map
          (FeynmanEdge.retarget γ.vertices
            (FeynmanGraph.freshVertex G.vertices))).map
        (FeynmanEdge.map (freshAlignedPerm G π))
    have hcomp : (γ.mapPerm π).complementEdges =
        γ.complementEdges.map (FeynmanEdge.map π) := by
      unfold FeynmanSubgraph.complementEdges
      show ((G.mapPerm π).internalEdges - (γ.mapPerm π).internalEdges) =
        (G.internalEdges - γ.internalEdges).map (FeynmanEdge.map π)
      show G.internalEdges.map (FeynmanEdge.map π) -
          γ.internalEdges.map (FeynmanEdge.map π) =
        (G.internalEdges - γ.internalEdges).map (FeynmanEdge.map π)
      symm
      exact map_sub_of_injective
        (FeynmanGraph.FeynmanEdge_map_injective π) γ.internalEdges_le
    rw [hcomp, Multiset.map_map, Multiset.map_map]
    apply Multiset.map_congr rfl
    intro e he
    have he_inG : e ∈ G.internalEdges :=
      Multiset.mem_of_le (Multiset.sub_le_self _ _) he
    have hsupp := hGwf.1 e he_inG
    have hsrc_G : e.source ∈ G.vertices := by
      simp [FeynmanEdge.SupportedOn] at hsupp; exact hsupp.1
    have htgt_G : e.target ∈ G.vertices := by
      simp [FeynmanEdge.SupportedOn] at hsupp; exact hsupp.2
    show (FeynmanEdge.retarget (γ.mapPerm π).vertices
            (FeynmanGraph.freshVertex (G.mapPerm π).vertices))
          ((FeynmanEdge.map π) e) =
        (FeynmanEdge.map (freshAlignedPerm G π))
          ((FeynmanEdge.retarget γ.vertices
            (FeynmanGraph.freshVertex G.vertices)) e)
    have hsrc_iff : e.source ∈ γ.vertices ↔
        π e.source ∈ (γ.mapPerm π).vertices := by
      show e.source ∈ γ.vertices ↔ π e.source ∈ γ.vertices.image π
      constructor
      · intro h; exact Finset.mem_image.mpr ⟨e.source, h, rfl⟩
      · intro h
        rcases Finset.mem_image.mp h with ⟨v, hv, hvπ⟩
        have : v = e.source := π.injective hvπ
        exact this ▸ hv
    have htgt_iff : e.target ∈ γ.vertices ↔
        π e.target ∈ (γ.mapPerm π).vertices := by
      show e.target ∈ γ.vertices ↔ π e.target ∈ γ.vertices.image π
      constructor
      · intro h; exact Finset.mem_image.mpr ⟨e.target, h, rfl⟩
      · intro h
        rcases Finset.mem_image.mp h with ⟨v, hv, hvπ⟩
        have : v = e.target := π.injective hvπ
        exact this ▸ hv
    apply FeynmanEdge.mk.injEq _ _ _ _ _ _ |>.mpr
    refine ⟨?_, ?_, ?_⟩
    · show (FeynmanEdge.retarget (γ.mapPerm π).vertices
              (FeynmanGraph.freshVertex (G.mapPerm π).vertices)
              ((FeynmanEdge.map π) e)).source =
          ((FeynmanEdge.map (freshAlignedPerm G π))
            (FeynmanEdge.retarget γ.vertices
              (FeynmanGraph.freshVertex G.vertices) e)).source
      simp only [FeynmanEdge.retarget, FeynmanEdge.map]
      by_cases hsγ : e.source ∈ γ.vertices
      · rw [if_pos hsγ, if_pos (hsrc_iff.mp hsγ)]
        exact (freshAlignedPerm_apply_s₁ G π).symm
      · rw [if_neg hsγ, if_neg (fun h => hsγ (hsrc_iff.mpr h))]
        exact (freshAlignedPerm_apply_of_mem hsrc_G).symm
    · show (FeynmanEdge.retarget (γ.mapPerm π).vertices
              (FeynmanGraph.freshVertex (G.mapPerm π).vertices)
              ((FeynmanEdge.map π) e)).target =
          ((FeynmanEdge.map (freshAlignedPerm G π))
            (FeynmanEdge.retarget γ.vertices
              (FeynmanGraph.freshVertex G.vertices) e)).target
      simp only [FeynmanEdge.retarget, FeynmanEdge.map]
      by_cases htγ : e.target ∈ γ.vertices
      · rw [if_pos htγ, if_pos (htgt_iff.mp htγ)]
        exact (freshAlignedPerm_apply_s₁ G π).symm
      · rw [if_neg htγ, if_neg (fun h => htγ (htgt_iff.mpr h))]
        exact (freshAlignedPerm_apply_of_mem htgt_G).symm
    · rfl
  · show (γ.mapPerm π).contract.externalLegs =
      γ.contract.externalLegs.map (ExternalLeg.map (freshAlignedPerm G π))
    show (G.mapPerm π).externalLegs.map
          (ExternalLeg.retarget (γ.mapPerm π).vertices
            (FeynmanGraph.freshVertex (G.mapPerm π).vertices)) =
      (G.externalLegs.map
          (ExternalLeg.retarget γ.vertices
            (FeynmanGraph.freshVertex G.vertices))).map
        (ExternalLeg.map (freshAlignedPerm G π))
    show (G.externalLegs.map (ExternalLeg.map π)).map
          (ExternalLeg.retarget (γ.mapPerm π).vertices
            (FeynmanGraph.freshVertex (G.mapPerm π).vertices)) = _
    rw [Multiset.map_map, Multiset.map_map]
    apply Multiset.map_congr rfl
    intro ℓ hℓ
    have hsupp := hGwf.2 ℓ hℓ
    have hatt_G : ℓ.attachedTo ∈ G.vertices := by
      simp [ExternalLeg.SupportedOn] at hsupp; exact hsupp
    show (ExternalLeg.retarget (γ.mapPerm π).vertices
            (FeynmanGraph.freshVertex (G.mapPerm π).vertices))
          ((ExternalLeg.map π) ℓ) =
        (ExternalLeg.map (freshAlignedPerm G π))
          ((ExternalLeg.retarget γ.vertices
            (FeynmanGraph.freshVertex G.vertices)) ℓ)
    have hatt_iff : ℓ.attachedTo ∈ γ.vertices ↔
        π ℓ.attachedTo ∈ (γ.mapPerm π).vertices := by
      show ℓ.attachedTo ∈ γ.vertices ↔ π ℓ.attachedTo ∈ γ.vertices.image π
      constructor
      · intro h; exact Finset.mem_image.mpr ⟨ℓ.attachedTo, h, rfl⟩
      · intro h
        rcases Finset.mem_image.mp h with ⟨v, hv, hvπ⟩
        have : v = ℓ.attachedTo := π.injective hvπ
        exact this ▸ hv
    apply ExternalLeg.mk.injEq _ _ _ _ |>.mpr
    refine ⟨?_, rfl⟩
    show (ExternalLeg.retarget (γ.mapPerm π).vertices
            (FeynmanGraph.freshVertex (G.mapPerm π).vertices)
            ((ExternalLeg.map π) ℓ)).attachedTo =
        ((ExternalLeg.map (freshAlignedPerm G π))
          (ExternalLeg.retarget γ.vertices
            (FeynmanGraph.freshVertex G.vertices) ℓ)).attachedTo
    simp only [ExternalLeg.retarget, ExternalLeg.map]
    by_cases hattγ : ℓ.attachedTo ∈ γ.vertices
    · rw [if_pos hattγ, if_pos (hatt_iff.mp hattγ)]
      exact (freshAlignedPerm_apply_s₁ G π).symm
    · rw [if_neg hattγ, if_neg (fun h => hattγ (hatt_iff.mpr h))]
      exact (freshAlignedPerm_apply_of_mem hatt_G).symm

/-- **R-6c-QFT-R1-body-570 — cross-ambient contract-class transport.**  `(γ.mapPerm π).contract` and
`γ.contract` are the same `FeynmanGraphClass` (renaming collapses under `IsIso`).  Instance-free
replacement for the old `mapPermSubgraph_contract_toClass_eq`. -/
theorem contract_mapPerm_toClass_eq {G : FeynmanGraph} (hGwf : G.WellFormed)
    (γ : FeynmanSubgraph G) (π : Equiv.Perm VertexId) :
    (γ.mapPerm π).contract.toClass = γ.contract.toClass :=
  ((FeynmanGraph.toClass_eq_iff _ _).mpr (contract_mapPerm_isIso hGwf γ π)).symm

end FeynmanSubgraph

/-! ## Step 1 — the ambient generator is rename-stable -/

/-- **R-6c-QFT-R1-body-570 — the ambient φ⁴ generator is rename-stable.** -/
theorem FeynmanGraph.toPhi4HopfGen_mapPerm (G : FeynmanGraph) (π : Equiv.Perm VertexId)
    (hWF : G.WellFormed) (h1PI : G.IsOnePI)
    (hGDiv : @FeynmanSubgraph.IsDivergent G (phi4DivergenceMeasureFamily G)
      (FeynmanSubgraph.self G hWF)) :
    (G.mapPerm π).toPhi4HopfGen (FeynmanGraph.mapPerm_wellFormed hWF)
        ((FeynmanGraph.mapPerm_isOnePI_iff π G).mpr h1PI)
        ((phi4_mapPerm_isDivergent_iff π (FeynmanSubgraph.self G hWF)).mpr hGDiv)
      = G.toPhi4HopfGen hWF h1PI hGDiv := by
  apply Subtype.ext
  show (G.mapPerm π).toClass = G.toClass
  exact ((FeynmanGraph.toClass_eq_iff G (G.mapPerm π)).mpr ⟨π, rfl⟩).symm

/-! ## Step 2 — the right factor is rename-stable -/

/-- **R-6c-QFT-R1-body-570 — the φ⁴ right factor `[Γ/γ]` is rename-stable.**  `Subtype.ext` on the
underlying class `γ.contract.toClass`, via `FeynmanSubgraph.contract_mapPerm_toClass_eq`.  All proof
arguments enter proof-irrelevantly (the value is `γ.contract.toClass`). -/
theorem FeynmanSubgraph.contractToPhi4HopfGen_mapPerm (γ : FeynmanSubgraph G)
    (π : Equiv.Perm VertexId)
    (hWF : G.WellFormed) (h1PI : G.IsOnePI) (hγ1PI : γ.IsOnePI) (hγNe : γ.IsNonempty)
    (hGDiv : @FeynmanSubgraph.IsDivergent G (phi4DivergenceMeasureFamily G)
      (FeynmanSubgraph.self G hWF))
    (hWFπ : (G.mapPerm π).WellFormed) (h1PIπ : (G.mapPerm π).IsOnePI)
    (hγ1PIπ : (γ.mapPerm π).IsOnePI) (hγNeπ : (γ.mapPerm π).IsNonempty)
    (hGDivπ : @FeynmanSubgraph.IsDivergent (G.mapPerm π) (phi4DivergenceMeasureFamily (G.mapPerm π))
      (FeynmanSubgraph.self (G.mapPerm π) hWFπ)) :
    (γ.mapPerm π).contractToPhi4HopfGen hWFπ h1PIπ hγ1PIπ hγNeπ hGDivπ
      = γ.contractToPhi4HopfGen hWF h1PI hγ1PI hγNe hGDiv := by
  apply Subtype.ext
  show (γ.mapPerm π).contract.toClass = γ.contract.toClass
  exact FeynmanSubgraph.contract_mapPerm_toClass_eq hWF γ π

/-! ## Step 3 — each connected summand is rename-stable -/

/-- **R-6c-QFT-R1-body-570 — each φ⁴ connected coproduct summand `[γ] ⊗ [Γ/γ]` is rename-stable.** -/
theorem FeynmanGraph.phi4ConnectedStrictSummand_mapPerm (G : FeynmanGraph)
    (π : Equiv.Perm VertexId)
    [Fintype (FeynmanSubgraph G)] [Fintype (FeynmanSubgraph (G.mapPerm π))]
    (hWF : G.WellFormed) (h1PI : G.IsOnePI)
    (hGDiv : @FeynmanSubgraph.IsDivergent G (phi4DivergenceMeasureFamily G)
      (FeynmanSubgraph.self G hWF))
    (γ : FeynmanSubgraph G) :
    (G.mapPerm π).phi4ConnectedStrictSummand (FeynmanGraph.mapPerm_wellFormed hWF)
        ((FeynmanGraph.mapPerm_isOnePI_iff π G).mpr h1PI)
        ((phi4_mapPerm_isDivergent_iff π (FeynmanSubgraph.self G hWF)).mpr hGDiv)
        (γ.mapPerm π)
      = G.phi4ConnectedStrictSummand hWF h1PI hGDiv γ := by
  have hmem :
      γ.mapPerm π ∈ (G.mapPerm π).phi4ProperConnectedDivergentSubgraphs ↔
        γ ∈ G.phi4ProperConnectedDivergentSubgraphs :=
    FeynmanGraph.mapPerm_mem_properConnectedDivergentSubgraphsFor_iff
      phi4DivergenceMeasureFamily phi4PermInvariantDivergenceMeasureFamily π G γ
  unfold FeynmanGraph.phi4ConnectedStrictSummand
  by_cases hγ : γ ∈ G.phi4ProperConnectedDivergentSubgraphs
  · rw [dif_pos (hmem.mpr hγ), dif_pos hγ]
    congr 1
    · exact congrArg phi4Gen (FeynmanSubgraph.toPhi4HopfGen_mapPerm γ π
        (G.phi4ProperConnectedDivergentSubgraphs_isConnectedDivergent hγ))
    · refine congrArg phi4Gen (Subtype.ext ?_)
      show (γ.mapPerm π).contract.toClass = γ.contract.toClass
      exact FeynmanSubgraph.contract_mapPerm_toClass_eq hWF γ π
  · rw [dif_neg (fun h => hγ (hmem.mp h)), dif_neg hγ]

/-! ## Step 4/5 — the representative coproduct is rename-stable -/

/-- **R-6c-QFT-R1-body-570 — the representative-level φ⁴ coproduct is rename-stable.**  The two boundary
terms are equal via Step 1; the connected sum is reindexed by `Finset.sum_bij` along `γ ↦ γ.mapPerm π`
(maps-into: body-569 rename certificate; injective: `π` injective through `FeynmanSubgraph.ext_iff`;
surjective: `π⁻¹`-image preimage through the ambient-cast lemmas; per-term: Step 3). -/
theorem FeynmanGraph.coproductGen_phi4_mapPerm (G : FeynmanGraph)
    (π : Equiv.Perm VertexId)
    [Fintype (FeynmanSubgraph G)] [Fintype (FeynmanSubgraph (G.mapPerm π))]
    (hWF : G.WellFormed) (h1PI : G.IsOnePI)
    (hGDiv : @FeynmanSubgraph.IsDivergent G (phi4DivergenceMeasureFamily G)
      (FeynmanSubgraph.self G hWF)) :
    (G.mapPerm π).coproductGen_phi4 (FeynmanGraph.mapPerm_wellFormed hWF)
        ((FeynmanGraph.mapPerm_isOnePI_iff π G).mpr h1PI)
        ((phi4_mapPerm_isDivergent_iff π (FeynmanSubgraph.self G hWF)).mpr hGDiv)
      = G.coproductGen_phi4 hWF h1PI hGDiv := by
  rw [FeynmanGraph.coproductGen_phi4_eq, FeynmanGraph.coproductGen_phi4_eq]
  have hgen :
      phi4Gen ((G.mapPerm π).toPhi4HopfGen (FeynmanGraph.mapPerm_wellFormed hWF)
          ((FeynmanGraph.mapPerm_isOnePI_iff π G).mpr h1PI)
          ((phi4_mapPerm_isDivergent_iff π (FeynmanSubgraph.self G hWF)).mpr hGDiv))
        = phi4Gen (G.toPhi4HopfGen hWF h1PI hGDiv) :=
    congrArg phi4Gen (FeynmanGraph.toPhi4HopfGen_mapPerm G π hWF h1PI hGDiv)
  rw [hgen]
  congr 1
  symm
  refine Finset.sum_bij (fun γ _ => γ.mapPerm π) ?_ ?_ ?_ ?_
  · -- maps into the renamed index
    intro γ hγ
    exact (FeynmanGraph.mapPerm_mem_properConnectedDivergentSubgraphsFor_iff
      phi4DivergenceMeasureFamily phi4PermInvariantDivergenceMeasureFamily π G γ).mpr hγ
  · -- injective
    intro γ₁ _ γ₂ _ heq
    have hELInj : Function.Injective (ExternalLeg.map π) := by
      intro ℓ₁ ℓ₂ h
      cases ℓ₁ with
      | mk a₁ s₁ =>
        cases ℓ₂ with
        | mk a₂ s₂ =>
          have hπa : π a₁ = π a₂ := congrArg ExternalLeg.attachedTo h
          have hs : s₁ = s₂ := congrArg ExternalLeg.sector h
          have : a₁ = a₂ := π.injective hπa
          subst this; subst hs; rfl
    apply FeynmanSubgraph.ext_iff.mpr
    refine ⟨?_, ?_, ?_⟩
    · have h := congrArg FeynmanSubgraph.vertices heq
      rw [FeynmanSubgraph.mapPerm_vertices, FeynmanSubgraph.mapPerm_vertices] at h
      exact Finset.image_injective π.injective h
    · have h := congrArg FeynmanSubgraph.internalEdges heq
      rw [FeynmanSubgraph.mapPerm_internalEdges, FeynmanSubgraph.mapPerm_internalEdges] at h
      exact Multiset.map_injective (FeynmanGraph.FeynmanEdge_map_injective π) h
    · have h := congrArg FeynmanSubgraph.externalLegs heq
      rw [FeynmanSubgraph.mapPerm_externalLegs, FeynmanSubgraph.mapPerm_externalLegs] at h
      exact Multiset.map_injective hELInj h
  · -- surjective, via a `π⁻¹`-image preimage through the ambient-cast lemmas
    intro γ' hγ'
    have hGG : (G.mapPerm π).mapPerm π⁻¹ = G := by
      rw [← FeynmanGraph.mapPerm_mul]; simp
    have hround : (hGG ▸ γ'.mapPerm π⁻¹).mapPerm π = γ' := by
      apply FeynmanSubgraph.ext_iff.mpr
      refine ⟨?_, ?_, ?_⟩
      · rw [FeynmanSubgraph.mapPerm_vertices, feynmanSubgraph_cast_vertices,
          FeynmanSubgraph.mapPerm_vertices, Finset.image_image]
        have hid : (⇑π) ∘ (⇑π⁻¹) = id := by
          rw [← Equiv.Perm.coe_mul, mul_inv_cancel, Equiv.Perm.coe_one]
        rw [hid, Finset.image_id]
      · rw [FeynmanSubgraph.mapPerm_internalEdges, feynmanSubgraph_cast_internalEdges,
          FeynmanSubgraph.mapPerm_internalEdges, Multiset.map_map]
        have hid : (FeynmanEdge.map π) ∘ (FeynmanEdge.map π⁻¹) = id := by
          funext e
          show (e.map π⁻¹).map π = e
          rw [← FeynmanEdge.map_mul, mul_inv_cancel, FeynmanEdge.map_one]
        rw [hid, Multiset.map_id]
      · rw [FeynmanSubgraph.mapPerm_externalLegs, feynmanSubgraph_cast_externalLegs,
          FeynmanSubgraph.mapPerm_externalLegs, Multiset.map_map]
        have hid : (ExternalLeg.map π) ∘ (ExternalLeg.map π⁻¹) = id := by
          funext ℓ
          show (ℓ.map π⁻¹).map π = ℓ
          rw [← ExternalLeg.map_mul, mul_inv_cancel, ExternalLeg.map_one]
        rw [hid, Multiset.map_id]
    refine ⟨hGG ▸ γ'.mapPerm π⁻¹, ?_, hround⟩
    have hmp := (FeynmanGraph.mapPerm_mem_properConnectedDivergentSubgraphsFor_iff
      phi4DivergenceMeasureFamily phi4PermInvariantDivergenceMeasureFamily π G
      (hGG ▸ γ'.mapPerm π⁻¹)).mp
    rw [hround] at hmp
    exact hmp hγ'
  · -- per-term equality (Step 3)
    intro γ hγ
    exact (FeynmanGraph.phi4ConnectedStrictSummand_mapPerm G π hWF h1PI hGDiv γ).symm

/-- **R-6c-QFT-R1-body-570 — the representative-level φ⁴ coproduct is graph-isomorphism invariant.**
Obtains the renaming witness from `IsIso` and reduces to `coproductGen_phi4_mapPerm`; the well-formed /
1PI / divergence hypotheses for the two graphs enter proof-irrelevantly. -/
theorem FeynmanGraph.coproductGen_phi4_isomorphism_invariant
    {G₁ G₂ : FeynmanGraph}
    [Fintype (FeynmanSubgraph G₁)] [Fintype (FeynmanSubgraph G₂)]
    (hIso : G₁.IsIso G₂)
    (hWF₁ : G₁.WellFormed) (h1PI₁ : G₁.IsOnePI)
    (hGDiv₁ : @FeynmanSubgraph.IsDivergent G₁ (phi4DivergenceMeasureFamily G₁)
      (FeynmanSubgraph.self G₁ hWF₁))
    (hWF₂ : G₂.WellFormed) (h1PI₂ : G₂.IsOnePI)
    (hGDiv₂ : @FeynmanSubgraph.IsDivergent G₂ (phi4DivergenceMeasureFamily G₂)
      (FeynmanSubgraph.self G₂ hWF₂)) :
    G₂.coproductGen_phi4 hWF₂ h1PI₂ hGDiv₂ = G₁.coproductGen_phi4 hWF₁ h1PI₁ hGDiv₁ := by
  obtain ⟨π, hπ⟩ := hIso
  subst hπ
  exact FeynmanGraph.coproductGen_phi4_mapPerm G₁ π hWF₁ h1PI₁ hGDiv₁

end GaugeGeometry.QFT.Combinatorial
