import GaugeGeometry.QFT.HopfAlgebra.Phi4ForestMapPermEquiv

/-!
# QFT-R1-body-579 — the boundary-completed left forest aggregate is rename-invariant

Body-578 built the φ⁴ forest coproduct index rename `Equiv`
(`FeynmanGraph.phi4ForestCoproductIndexEquiv`): the same set of forests laid out in different
coordinates.  This body proves the **companion value fact** on the left tensor factor: the
boundary-completed left forest aggregate `AdmissibleSubgraph.toPhi4HopfH` (body-572) is unchanged
when the ambient graph — and every component with it — is renamed by a vertex permutation.  "The same
boundary-completed components, reordered, give the same product."

## Contents

* Step 1 `mapPermSubgraph_toPhi4HopfGen` — one component's boundary-completed left generator
  (body-568) is unchanged by `mapPermSubgraph` transport.  Pure `subst` + body-568's
  `toPhi4HopfGen_mapPerm`; the CD-witness alignment is proof-irrelevance.
* Step 2 (re-derived instance-free, since body-578's copies are `private`)
  `mapPermAdmissibleSubgraphFor_elements'` (the image `rfl`) and `mapPermSubgraph_injective'`
  (from `FeynmanSubgraph.ext_iff` + edge/leg map injectivity).
* Step 3 (target) `AdmissibleSubgraph.toPhi4HopfH_mapPermFor` — the aggregate product is invariant,
  via a `Finset.prod_bij` over the two `attach` products, componentwise by Step 1.
* Step 4 (target) `FeynmanGraph.phi4ForestCoproductIndexEquiv_left_eq` — the thin composition with
  body-578's `phi4ForestCoproductIndexEquiv_apply_coe`.

Per the HALT: no star comparison, no quotient / class equality, no correcting permutation, no forest
summand / sum invariance, no strict forest equality, zero raw boundary-forgetting generator, no
W″ / reflection / coassoc; zero new `class`/`structure`/permanent `instance`; zero forbidden
divergence classes in any public decl.  The only instance binder is the blanket
`[∀ H, Fintype (FeynmanSubgraph H)]`.
-/

namespace GaugeGeometry.QFT.Combinatorial

-- Finite-sum infrastructure as a blanket (so mapped graphs' `Fintype` resolves without reducing
-- deep forest terms — the body-574 performance lesson).  NOT physics.
variable [∀ H : FeynmanGraph, Fintype (FeynmanSubgraph H)]

/-! ## Step 1 — one component's boundary-completed left generator is transport-invariant -/

/-- **body-579 — the boundary-completed left generator of a component is unchanged by
`mapPermSubgraph` transport.**  After `subst hπ`, `mapPermSubgraph rfl γ` is `γ.mapPerm π`
definitionally, and body-568's `toPhi4HopfGen_mapPerm` closes it; the two CD witnesses agree by
proof-irrelevance. -/
theorem mapPermSubgraph_toPhi4HopfGen
    {G₁ G₂ : FeynmanGraph} {π : Equiv.Perm VertexId} (hπ : G₂ = G₁.mapPerm π)
    (γ : FeynmanSubgraph G₁)
    (hγ : @FeynmanSubgraph.IsConnectedDivergent G₁ (phi4DivergenceMeasureFamily G₁) γ)
    (hγ' : @FeynmanSubgraph.IsConnectedDivergent G₂ (phi4DivergenceMeasureFamily G₂)
      (mapPermSubgraph hπ γ)) :
    (mapPermSubgraph hπ γ).toPhi4HopfGen hγ' = γ.toPhi4HopfGen hγ := by
  subst hπ
  -- `mapPermSubgraph rfl γ` reduces to `γ.mapPerm π`; the LHS witness `hγ'` unifies with the
  -- specific witness of `toPhi4HopfGen_mapPerm` by proof-irrelevance.
  exact FeynmanSubgraph.toPhi4HopfGen_mapPerm γ π hγ

/-! ## Step 2 — the minimal re-derived transport facts (body-578's copies are `private`) -/

/-- `mapPermAdmissibleSubgraphFor` carries the image element set (`rfl`; re-derived here because
body-578's copy is `private`). -/
private theorem mapPermAdmissibleSubgraphFor_elements'
    (D : DivergenceMeasureFamily) (Inv : PermInvariantDivergenceMeasureFamily D)
    {G₁ G₂ : FeynmanGraph} {π : Equiv.Perm VertexId}
    (hπ : G₂ = G₁.mapPerm π) (A : AdmissibleSubgraphFor D G₁) :
    (mapPermAdmissibleSubgraphFor D Inv hπ A).elements =
      A.elements.image (mapPermSubgraph hπ) := rfl

/-- `mapPermSubgraph` transport is injective on subgraphs (re-derived instance-free from
`FeynmanSubgraph.ext_iff` + edge/leg map injectivity; body-578's copy is `private`). -/
private theorem mapPermSubgraph_injective'
    {G₁ G₂ : FeynmanGraph} {π : Equiv.Perm VertexId} (hπ : G₂ = G₁.mapPerm π) :
    Function.Injective (mapPermSubgraph hπ : FeynmanSubgraph G₁ → FeynmanSubgraph G₂) := by
  subst hπ
  intro a b hab
  -- `mapPermSubgraph rfl x = x.mapPerm π` definitionally.
  have hab' : a.mapPerm π = b.mapPerm π := hab
  have hELInj : Function.Injective (ExternalLeg.map π) := by
    intro ℓ₁ ℓ₂ h
    cases ℓ₁ with
    | mk a₁ s₁ =>
        cases ℓ₂ with
        | mk a₂ s₂ =>
            have hπa : π a₁ = π a₂ := congrArg ExternalLeg.attachedTo h
            have hs : s₁ = s₂ := congrArg ExternalLeg.sector h
            have hae : a₁ = a₂ := π.injective hπa
            subst hae; subst hs; rfl
  apply FeynmanSubgraph.ext_iff.mpr
  refine ⟨?_, ?_, ?_⟩
  · have h := congrArg FeynmanSubgraph.vertices hab'
    rw [FeynmanSubgraph.mapPerm_vertices, FeynmanSubgraph.mapPerm_vertices] at h
    exact Finset.image_injective π.injective h
  · have h := congrArg FeynmanSubgraph.internalEdges hab'
    rw [FeynmanSubgraph.mapPerm_internalEdges, FeynmanSubgraph.mapPerm_internalEdges] at h
    exact Multiset.map_injective (FeynmanGraph.FeynmanEdge_map_injective π) h
  · have h := congrArg FeynmanSubgraph.externalLegs hab'
    rw [FeynmanSubgraph.mapPerm_externalLegs, FeynmanSubgraph.mapPerm_externalLegs] at h
    exact Multiset.map_injective hELInj h

/-! ## Step 3 — the boundary-completed left forest aggregate is rename-invariant -/

/-- **body-579 (TARGET) — the boundary-completed left forest aggregate is rename-invariant.**  The
product `AdmissibleSubgraph.toPhi4HopfH` over the components of a renamed admissible forest equals
the product over the original.  Componentwise Step 1 through a `Finset.prod_bij` on the two `attach`
products; the CD-witness alignment inside each summand is proof-irrelevance. -/
theorem AdmissibleSubgraph.toPhi4HopfH_mapPermFor
    {G₁ G₂ : FeynmanGraph} {π : Equiv.Perm VertexId} (hπ : G₂ = G₁.mapPerm π)
    (A : AdmissibleSubgraphFor phi4DivergenceMeasureFamily G₁) :
    (mapPermAdmissibleSubgraphFor phi4DivergenceMeasureFamily
        phi4PermInvariantDivergenceMeasureFamily hπ A).toPhi4HopfH = A.toPhi4HopfH := by
  classical
  letI : DivergenceMeasure G₁ := phi4DivergenceMeasureFamily G₁
  letI : DivergenceMeasure G₂ := phi4DivergenceMeasureFamily G₂
  set B := mapPermAdmissibleSubgraphFor phi4DivergenceMeasureFamily
    phi4PermInvariantDivergenceMeasureFamily hπ A with hB
  -- membership transport `A.elements → B.elements`
  have hmem : ∀ (γ : FeynmanSubgraph G₁), γ ∈ A.elements → mapPermSubgraph hπ γ ∈ B.elements := by
    intro γ hγ
    rw [hB, mapPermAdmissibleSubgraphFor_elements']
    exact Finset.mem_image.mpr ⟨γ, hγ, rfl⟩
  symm
  -- expose both aggregates as raw `attach` products
  simp only [AdmissibleSubgraph.toPhi4HopfH]
  refine Finset.prod_bij
    (fun (γ : {x // x ∈ A.elements}) _ => (⟨mapPermSubgraph hπ γ.1, hmem γ.1 γ.2⟩ :
      {x // x ∈ B.elements}))
    (fun _ _ => Finset.mem_attach _ _)
    ?_ ?_ ?_
  · -- injective
    intro γ₁ _ γ₂ _ heq
    have h1 : mapPermSubgraph hπ γ₁.1 = mapPermSubgraph hπ γ₂.1 := congrArg Subtype.val heq
    exact Subtype.ext (mapPermSubgraph_injective' hπ h1)
  · -- surjective
    intro b _
    obtain ⟨bv, hbv⟩ := b
    rw [hB, mapPermAdmissibleSubgraphFor_elements'] at hbv
    rcases Finset.mem_image.mp hbv with ⟨γ, hγ, hγeq⟩
    exact ⟨⟨γ, hγ⟩, Finset.mem_attach _ _, Subtype.ext hγeq⟩
  · -- summand equality (Step 1, componentwise)
    intro γ _
    exact congrArg phi4Gen
      (mapPermSubgraph_toPhi4HopfGen hπ γ.1 (A.isConnectedDivergent_of_mem γ.2)
        (B.isConnectedDivergent_of_mem (hmem γ.1 γ.2))).symm

/-! ## Step 4 — the φ⁴ coproduct-index rename `Equiv` preserves the left aggregate -/

/-- **body-579 (TARGET) — the φ⁴ forest coproduct-index rename `Equiv` preserves the left
aggregate.**  Reading body-578's finished index `Equiv`, the renamed index element carries the same
boundary-completed left forest product as the original. -/
theorem FeynmanGraph.phi4ForestCoproductIndexEquiv_left_eq
    (G : FeynmanGraph) (π : Equiv.Perm VertexId)
    (A : {A : AdmissibleSubgraphFor phi4DivergenceMeasureFamily G //
        A ∈ G.phi4ForestCoproductIndex}) :
    ((G.phi4ForestCoproductIndexEquiv π A).1).toPhi4HopfH = A.1.toPhi4HopfH := by
  rw [G.phi4ForestCoproductIndexEquiv_apply_coe π A]
  exact AdmissibleSubgraph.toPhi4HopfH_mapPermFor (rfl : G.mapPerm π = G.mapPerm π) A.1

end GaugeGeometry.QFT.Combinatorial
