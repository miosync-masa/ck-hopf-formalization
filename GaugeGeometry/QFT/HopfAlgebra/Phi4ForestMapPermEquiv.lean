import GaugeGeometry.QFT.HopfAlgebra.DivergenceFamilyForwardLanding
import GaugeGeometry.QFT.HopfAlgebra.Phi4ForestCoproductEntrance

/-!
# QFT-R1-body-578 — φ⁴ forest coproduct index rename `Equiv`

Bodies 572–574 built the family-indexed φ⁴ forest coproduct index
`FeynmanGraph.phi4ForestCoproductIndex`.  This body proves that the index is the *same set of
forests laid out in different coordinates*: a genuine `Equiv` between the coproduct index of `G` and
that of `G.mapPerm π`, under the vertex renaming.  A later body's `Finset.sum_bij` reads this
finished `Equiv`; here we build **only the index bijection** — no star comparison, no summand, no
left aggregate, no cross-presentation equality.

## Contents

* Step 1 `mapPermAdmissibleSubgraphFor` — transport an admissible forest along the ambient graph
  permutation.  The design copies Coassoc's `mapPermAdmissibleSubgraph` (`ofElements` on the image of
  `mapPermSubgraph`), but the component connected-divergence step is **family-explicit**: it consumes
  body-565's `FeynmanSubgraph.mapPerm_isConnectedDivergent_iff_of_family` via `(D)(Inv)`, never a
  blanket divergence class.  All the measure-free transports (`nestedOrDisjoint`, `disjoint`,
  `isNonempty`, injectivity, round-trips) are re-derived instance-free.
* Step 2 `admissibleSubgraphMapPermEquivFor` — the `AdmissibleSubgraphFor` rename `Equiv`
  (`Finset`-image round-trips proved through `AdmissibleSubgraph.ext → Forest.ext`, no `cast`/`HEq`).
* Step 3 index-predicate preservation — `internalEdges`/`complementEdges` transported by
  `Multiset.map (FeynmanEdge.map π)`, and the proper-disjoint + complement-positivity `iff`.
* Step 4 (target) `FeynmanGraph.phi4ForestCoproductIndexEquiv` — the φ⁴ specialization on the index
  subtype.

Per the HALT: no left aggregate rename, no `toPhi4HopfH`, no canonical contraction / star, no quotient
graph equality, no correcting permutation, no forest summand / sum invariance, zero cross-presentation
star equality, no W″ / reflection / coassoc; zero new `class`/`structure`/permanent `instance`; zero
forbidden divergence classes in any public decl.  The only instance binder is the blanket
`[∀ H, Fintype (FeynmanSubgraph H)]` — finite-sum infrastructure.
-/

namespace GaugeGeometry.QFT.Combinatorial

-- Finite-sum infrastructure as a blanket (so mapped/quotient graphs' `Fintype` resolves without
-- reducing deep terms).  NOT physics.
variable [∀ H : FeynmanGraph, Fintype (FeynmanSubgraph H)]

/-! ## Measure-free permutation transports on `mapPermSubgraph` (re-derived instance-free) -/

/-- The inverse ambient equality obtained from `hπ` via the group identity. -/
private theorem hpiInv {G₁ G₂ : FeynmanGraph} {π : Equiv.Perm VertexId}
    (hπ : G₂ = G₁.mapPerm π) : G₁ = G₂.mapPerm π⁻¹ := by
  subst hπ; rw [← FeynmanGraph.mapPerm_mul]; simp

-- The public `mapPermSubgraph_*` field lemmas in `Coproduct.lean` inherit the file-level blanket
-- `[∀ G, DivergenceMeasure G] [∀ G, IsPermInvariantDivergence G] [∀ G, IsIsoInvariantDivergence G]`
-- (forbidden classes).  The `mapPermSubgraph` *definition* itself is clean, so we re-derive the field
-- lemmas instance-free from the clean `FeynmanSubgraph.mapPerm_*` (Permutation.lean).

private theorem mps_vertices {G₁ G₂ : FeynmanGraph} {π : Equiv.Perm VertexId}
    (hπ : G₂ = G₁.mapPerm π) (γ : FeynmanSubgraph G₁) :
    (mapPermSubgraph hπ γ).vertices = γ.vertices.image π := by
  unfold mapPermSubgraph; subst hπ; exact FeynmanSubgraph.mapPerm_vertices π γ

private theorem mps_internalEdges {G₁ G₂ : FeynmanGraph} {π : Equiv.Perm VertexId}
    (hπ : G₂ = G₁.mapPerm π) (γ : FeynmanSubgraph G₁) :
    (mapPermSubgraph hπ γ).internalEdges = γ.internalEdges.map (FeynmanEdge.map π) := by
  unfold mapPermSubgraph; subst hπ; exact FeynmanSubgraph.mapPerm_internalEdges π γ

private theorem mps_externalLegs {G₁ G₂ : FeynmanGraph} {π : Equiv.Perm VertexId}
    (hπ : G₂ = G₁.mapPerm π) (γ : FeynmanSubgraph G₁) :
    (mapPermSubgraph hπ γ).externalLegs = γ.externalLegs.map (ExternalLeg.map π) := by
  unfold mapPermSubgraph; subst hπ; exact FeynmanSubgraph.mapPerm_externalLegs π γ

private theorem mps_internalEdges_card {G₁ G₂ : FeynmanGraph} {π : Equiv.Perm VertexId}
    (hπ : G₂ = G₁.mapPerm π) (γ : FeynmanSubgraph G₁) :
    (mapPermSubgraph hπ γ).internalEdges.card = γ.internalEdges.card := by
  rw [mps_internalEdges, Multiset.card_map]

/-- Vertex-disjointness is preserved by `mapPermSubgraph` (measure-free). -/
private theorem mapPermSubgraph_disjoint
    {G₁ G₂ : FeynmanGraph} {π : Equiv.Perm VertexId}
    (hπ : G₂ = G₁.mapPerm π) {γ₁ γ₂ : FeynmanSubgraph G₁}
    (h : γ₁.Disjoint γ₂) :
    (mapPermSubgraph hπ γ₁).Disjoint (mapPermSubgraph hπ γ₂) := by
  unfold mapPermSubgraph
  subst hπ
  exact (FeynmanSubgraph.mapPerm_disjoint_iff π γ₁ γ₂).mpr h

/-- Zimmermann compatibility is preserved by `mapPermSubgraph` (measure-free). -/
private theorem mapPermSubgraph_nestedOrDisjoint
    {G₁ G₂ : FeynmanGraph} {π : Equiv.Perm VertexId}
    (hπ : G₂ = G₁.mapPerm π) {γ₁ γ₂ : FeynmanSubgraph G₁}
    (h : γ₁.NestedOrDisjoint γ₂) :
    (mapPermSubgraph hπ γ₁).NestedOrDisjoint (mapPermSubgraph hπ γ₂) := by
  unfold mapPermSubgraph
  subst hπ
  exact (FeynmanSubgraph.mapPerm_nestedOrDisjoint_iff π γ₁ γ₂).mpr h

/-- Component nonemptiness is preserved by `mapPermSubgraph` (measure-free). -/
private theorem mapPermSubgraph_isNonempty
    {G₁ G₂ : FeynmanGraph} {π : Equiv.Perm VertexId}
    (hπ : G₂ = G₁.mapPerm π) {γ : FeynmanSubgraph G₁}
    (h : γ.IsNonempty) :
    (mapPermSubgraph hπ γ).IsNonempty := by
  unfold FeynmanSubgraph.IsNonempty FeynmanSubgraph.vertexCount at h ⊢
  rw [mps_vertices]
  simpa [Finset.card_image_of_injective _ π.injective] using h

/-- Generic `mapPermSubgraph` round-trip: two ambient transports whose permutations multiply to `1`
compose to the identity on subgraphs.  Proved by field equality (`FeynmanSubgraph.ext_iff`), no
`cast`/`HEq`. -/
private theorem mapPermSubgraph_roundtripGen
    {Ga Gb : FeynmanGraph} {a b : Equiv.Perm VertexId}
    (ha : Gb = Ga.mapPerm a) (hb : Ga = Gb.mapPerm b) (hab : b * a = 1)
    (δ : FeynmanSubgraph Ga) :
    mapPermSubgraph hb (mapPermSubgraph ha δ) = δ := by
  apply FeynmanSubgraph.ext_iff.mpr
  have hcompV : (⇑b ∘ ⇑a) = (id : VertexId → VertexId) := by
    funext x
    have hx : (b * a) x = x := by rw [hab]; rfl
    simpa [Equiv.Perm.mul_apply] using hx
  refine ⟨?_, ?_, ?_⟩
  · rw [mps_vertices, mps_vertices, Finset.image_image, hcompV,
      Finset.image_id]
  · rw [mps_internalEdges, mps_internalEdges, Multiset.map_map]
    have hE : (FeynmanEdge.map b) ∘ (FeynmanEdge.map a) = id := by
      funext e
      show FeynmanEdge.map b (FeynmanEdge.map a e) = e
      rw [← FeynmanEdge.map_mul, hab, FeynmanEdge.map_one]
    rw [hE, Multiset.map_id]
  · rw [mps_externalLegs, mps_externalLegs, Multiset.map_map]
    have hL : (ExternalLeg.map b) ∘ (ExternalLeg.map a) = id := by
      funext ℓ
      show ExternalLeg.map b (ExternalLeg.map a ℓ) = ℓ
      rw [← ExternalLeg.map_mul, hab, ExternalLeg.map_one]
    rw [hL, Multiset.map_id]

/-! ## Step 1 — family-explicit admissible-forest transport -/

/-- Connected-divergence of a component is preserved by `mapPermSubgraph`, **family-explicit** (via
body-565), never a blanket divergence class. -/
private theorem mapPermSubgraph_isConnectedDivergent_of_family
    (D : DivergenceMeasureFamily) (Inv : PermInvariantDivergenceMeasureFamily D)
    {G₁ G₂ : FeynmanGraph} {π : Equiv.Perm VertexId}
    (hπ : G₂ = G₁.mapPerm π) {γ : FeynmanSubgraph G₁}
    (h : @FeynmanSubgraph.IsConnectedDivergent G₁ (D G₁) γ) :
    @FeynmanSubgraph.IsConnectedDivergent G₂ (D G₂) (mapPermSubgraph hπ γ) := by
  subst hπ
  exact (FeynmanSubgraph.mapPerm_isConnectedDivergent_iff_of_family D Inv π γ).mpr h

/-- **body-578 — transport an admissible forest along an ambient graph permutation** for an explicit
divergence-measure family.  Design copied from Coassoc's `mapPermAdmissibleSubgraph`, but the
component connected-divergence step is family-explicit (`(D)(Inv)` + body-565); the nested/disjoint
step is measure-free. -/
noncomputable def mapPermAdmissibleSubgraphFor
    (D : DivergenceMeasureFamily) (Inv : PermInvariantDivergenceMeasureFamily D)
    {G₁ G₂ : FeynmanGraph} {π : Equiv.Perm VertexId}
    (hπ : G₂ = G₁.mapPerm π) (A : AdmissibleSubgraphFor D G₁) :
    AdmissibleSubgraphFor D G₂ :=
  @AdmissibleSubgraph.ofElements G₂ (D G₂)
    (A.elements.image (mapPermSubgraph hπ))
    (by
      refine ⟨?_, ?_⟩
      · intro γ' hγ'
        rcases Finset.mem_image.mp hγ' with ⟨γ, hγ, rfl⟩
        exact mapPermSubgraph_isConnectedDivergent_of_family D Inv hπ
          (A.isConnectedDivergent_of_mem hγ)
      · intro γ₁' h₁ γ₂' h₂ hne
        rcases Finset.mem_image.mp h₁ with ⟨γ₁, hγ₁, rfl⟩
        rcases Finset.mem_image.mp h₂ with ⟨γ₂, hγ₂, rfl⟩
        have hne' : γ₁ ≠ γ₂ := fun hγ => hne (by rw [hγ])
        exact mapPermSubgraph_nestedOrDisjoint hπ
          (A.forest.nestedOrDisjoint hγ₁ hγ₂ hne'))

@[simp] private theorem mapPermAdmissibleSubgraphFor_elements
    (D : DivergenceMeasureFamily) (Inv : PermInvariantDivergenceMeasureFamily D)
    {G₁ G₂ : FeynmanGraph} {π : Equiv.Perm VertexId}
    (hπ : G₂ = G₁.mapPerm π) (A : AdmissibleSubgraphFor D G₁) :
    (mapPermAdmissibleSubgraphFor D Inv hπ A).elements =
      A.elements.image (mapPermSubgraph hπ) := rfl

/-- Permutation transport on admissible forests is injective (left-inverse via the round-trip). -/
private theorem mapPermSubgraph_injective_fam
    {G₁ G₂ : FeynmanGraph} {π : Equiv.Perm VertexId} (hπ : G₂ = G₁.mapPerm π) :
    Function.Injective (mapPermSubgraph hπ : FeynmanSubgraph G₁ → FeynmanSubgraph G₂) :=
  Function.LeftInverse.injective
    (g := mapPermSubgraph (hpiInv hπ))
    (fun δ => mapPermSubgraph_roundtripGen hπ (hpiInv hπ) (inv_mul_cancel π) δ)

/-! ## Step 2 — the admissible-forest rename `Equiv` -/

/-- Reverse transport, along `π⁻¹`. -/
noncomputable def mapPermAdmissibleSubgraphForPreimage
    (D : DivergenceMeasureFamily) (Inv : PermInvariantDivergenceMeasureFamily D)
    {G₁ G₂ : FeynmanGraph} {π : Equiv.Perm VertexId}
    (hπ : G₂ = G₁.mapPerm π) (A : AdmissibleSubgraphFor D G₂) :
    AdmissibleSubgraphFor D G₁ :=
  mapPermAdmissibleSubgraphFor D Inv (hpiInv hπ) A

/-- `preimage ∘ forward = id` at the admissible-forest level. -/
private theorem mapPermAdmissibleSubgraphFor_leftInv
    (D : DivergenceMeasureFamily) (Inv : PermInvariantDivergenceMeasureFamily D)
    {G₁ G₂ : FeynmanGraph} {π : Equiv.Perm VertexId}
    (hπ : G₂ = G₁.mapPerm π) (A : AdmissibleSubgraphFor D G₁) :
    mapPermAdmissibleSubgraphFor D Inv (hpiInv hπ)
        (mapPermAdmissibleSubgraphFor D Inv hπ A) = A := by
  apply AdmissibleSubgraph.ext
  apply Forest.ext
  show (mapPermAdmissibleSubgraphFor D Inv (hpiInv hπ)
      (mapPermAdmissibleSubgraphFor D Inv hπ A)).elements = A.elements
  rw [mapPermAdmissibleSubgraphFor_elements, mapPermAdmissibleSubgraphFor_elements,
    Finset.image_image]
  rw [show ((mapPermSubgraph (hpiInv hπ)) ∘ (mapPermSubgraph hπ) :
        FeynmanSubgraph G₁ → FeynmanSubgraph G₁) = id from
      funext (fun δ => mapPermSubgraph_roundtripGen hπ (hpiInv hπ) (inv_mul_cancel π) δ)]
  exact Finset.image_id

/-- `forward ∘ preimage = id` at the admissible-forest level. -/
private theorem mapPermAdmissibleSubgraphFor_rightInv
    (D : DivergenceMeasureFamily) (Inv : PermInvariantDivergenceMeasureFamily D)
    {G₁ G₂ : FeynmanGraph} {π : Equiv.Perm VertexId}
    (hπ : G₂ = G₁.mapPerm π) (B : AdmissibleSubgraphFor D G₂) :
    mapPermAdmissibleSubgraphFor D Inv hπ
        (mapPermAdmissibleSubgraphFor D Inv (hpiInv hπ) B) = B := by
  apply AdmissibleSubgraph.ext
  apply Forest.ext
  show (mapPermAdmissibleSubgraphFor D Inv hπ
      (mapPermAdmissibleSubgraphFor D Inv (hpiInv hπ) B)).elements = B.elements
  rw [mapPermAdmissibleSubgraphFor_elements, mapPermAdmissibleSubgraphFor_elements,
    Finset.image_image]
  rw [show ((mapPermSubgraph hπ) ∘ (mapPermSubgraph (hpiInv hπ)) :
        FeynmanSubgraph G₂ → FeynmanSubgraph G₂) = id from
      funext (fun γ' => mapPermSubgraph_roundtripGen (hpiInv hπ) hπ (mul_inv_cancel π) γ')]
  exact Finset.image_id

/-- **body-578 — the admissible-forest rename `Equiv`** for an explicit family. -/
noncomputable def admissibleSubgraphMapPermEquivFor
    (D : DivergenceMeasureFamily) (Inv : PermInvariantDivergenceMeasureFamily D)
    {G₁ G₂ : FeynmanGraph} {π : Equiv.Perm VertexId} (hπ : G₂ = G₁.mapPerm π) :
    AdmissibleSubgraphFor D G₁ ≃ AdmissibleSubgraphFor D G₂ where
  toFun := mapPermAdmissibleSubgraphFor D Inv hπ
  invFun := mapPermAdmissibleSubgraphForPreimage D Inv hπ
  left_inv A := mapPermAdmissibleSubgraphFor_leftInv D Inv hπ A
  right_inv B := mapPermAdmissibleSubgraphFor_rightInv D Inv hπ B

/-! ## Step 3 — index-predicate preservation -/

/-- `Multiset.map` distributes over subtraction along an injective map. -/
private theorem multiset_map_sub_of_injective {α β : Type*}
    [DecidableEq α] [DecidableEq β] {f : α → β}
    (hf : Function.Injective f) {A B : Multiset α} :
    (A - B).map f = A.map f - B.map f := by
  refine Multiset.ext.mpr (fun y => ?_)
  rw [Multiset.count_sub]
  by_cases hy : y ∈ A.map f
  · rcases Multiset.mem_map.mp hy with ⟨x, _hxA, rfl⟩
    rw [Multiset.count_map_eq_count' _ _ hf, Multiset.count_map_eq_count' _ _ hf,
        Multiset.count_map_eq_count' _ _ hf, Multiset.count_sub]
  · have hy_sub : y ∉ (A - B).map f := by
      intro h
      rcases Multiset.mem_map.mp h with ⟨x, hx, rfl⟩
      have hxA : x ∈ A := Multiset.mem_of_le (Multiset.sub_le_self _ _) hx
      exact hy (Multiset.mem_map.mpr ⟨x, hxA, rfl⟩)
    rw [Multiset.count_eq_zero_of_notMem hy_sub, Multiset.count_eq_zero_of_notMem hy]
    simp

/-- Internal-edge carrier is transported by `Multiset.map (FeynmanEdge.map π)`. -/
private theorem mapPermAdmissibleSubgraphFor_internalEdges
    (D : DivergenceMeasureFamily) (Inv : PermInvariantDivergenceMeasureFamily D)
    {G₁ G₂ : FeynmanGraph} {π : Equiv.Perm VertexId}
    (hπ : G₂ = G₁.mapPerm π) (A : AdmissibleSubgraphFor D G₁) :
    (@AdmissibleSubgraph.internalEdges G₂ (D G₂) (mapPermAdmissibleSubgraphFor D Inv hπ A)) =
      (@AdmissibleSubgraph.internalEdges G₁ (D G₁) A).map (FeynmanEdge.map π) := by
  classical
  simp only [AdmissibleSubgraph.internalEdges]
  rw [mapPermAdmissibleSubgraphFor_elements,
    Finset.sum_image (mapPermSubgraph_injective_fam hπ).injOn]
  simp only [mps_internalEdges]
  rw [← Multiset.coe_mapAddMonoidHom (FeynmanEdge.map π),
    map_sum (Multiset.mapAddMonoidHom (FeynmanEdge.map π))]

/-- Complement-edge carrier is transported by `Multiset.map (FeynmanEdge.map π)`. -/
private theorem mapPermAdmissibleSubgraphFor_complementEdges
    (D : DivergenceMeasureFamily) (Inv : PermInvariantDivergenceMeasureFamily D)
    {G₁ G₂ : FeynmanGraph} {π : Equiv.Perm VertexId}
    (hπ : G₂ = G₁.mapPerm π) (A : AdmissibleSubgraphFor D G₁) :
    (@AdmissibleSubgraph.complementEdges G₂ (D G₂) (mapPermAdmissibleSubgraphFor D Inv hπ A)) =
      (@AdmissibleSubgraph.complementEdges G₁ (D G₁) A).map (FeynmanEdge.map π) := by
  simp only [AdmissibleSubgraph.complementEdges]
  rw [mapPermAdmissibleSubgraphFor_internalEdges,
    multiset_map_sub_of_injective (FeynmanGraph.FeynmanEdge_map_injective π)]
  congr 1
  subst hπ
  rw [FeynmanGraph.mapPerm_internalEdges]

private theorem mapPermAdmissibleSubgraphFor_internalEdges_card
    (D : DivergenceMeasureFamily) (Inv : PermInvariantDivergenceMeasureFamily D)
    {G₁ G₂ : FeynmanGraph} {π : Equiv.Perm VertexId}
    (hπ : G₂ = G₁.mapPerm π) (A : AdmissibleSubgraphFor D G₁) :
    (@AdmissibleSubgraph.internalEdges G₂ (D G₂) (mapPermAdmissibleSubgraphFor D Inv hπ A)).card =
      (@AdmissibleSubgraph.internalEdges G₁ (D G₁) A).card := by
  rw [mapPermAdmissibleSubgraphFor_internalEdges, Multiset.card_map]

private theorem mapPermAdmissibleSubgraphFor_complementEdges_card
    (D : DivergenceMeasureFamily) (Inv : PermInvariantDivergenceMeasureFamily D)
    {G₁ G₂ : FeynmanGraph} {π : Equiv.Perm VertexId}
    (hπ : G₂ = G₁.mapPerm π) (A : AdmissibleSubgraphFor D G₁) :
    (@AdmissibleSubgraph.complementEdges G₂ (D G₂) (mapPermAdmissibleSubgraphFor D Inv hπ A)).card =
      (@AdmissibleSubgraph.complementEdges G₁ (D G₁) A).card := by
  rw [mapPermAdmissibleSubgraphFor_complementEdges, Multiset.card_map]

/-- Pairwise-disjointness transports (measure-free components). -/
private theorem mapPermAdmissibleSubgraphFor_isPairwiseDisjoint
    (D : DivergenceMeasureFamily) (Inv : PermInvariantDivergenceMeasureFamily D)
    {G₁ G₂ : FeynmanGraph} {π : Equiv.Perm VertexId}
    (hπ : G₂ = G₁.mapPerm π) {A : AdmissibleSubgraphFor D G₁}
    (hA : @AdmissibleSubgraph.IsPairwiseDisjoint G₁ (D G₁) A) :
    @AdmissibleSubgraph.IsPairwiseDisjoint G₂ (D G₂)
      (mapPermAdmissibleSubgraphFor D Inv hπ A) := by
  intro γ₁' h₁ γ₂' h₂ hne
  change γ₁' ∈ (mapPermAdmissibleSubgraphFor D Inv hπ A).elements at h₁
  change γ₂' ∈ (mapPermAdmissibleSubgraphFor D Inv hπ A).elements at h₂
  rw [mapPermAdmissibleSubgraphFor_elements] at h₁ h₂
  rcases Finset.mem_image.mp h₁ with ⟨γ₁, hγ₁, rfl⟩
  rcases Finset.mem_image.mp h₂ with ⟨γ₂, hγ₂, rfl⟩
  have hne' : γ₁ ≠ γ₂ := fun hγ => hne (by rw [hγ])
  exact mapPermSubgraph_disjoint hπ (hA hγ₁ hγ₂ hne')

/-- Nonemptiness transports. -/
private theorem mapPermAdmissibleSubgraphFor_isNonempty
    (D : DivergenceMeasureFamily) (Inv : PermInvariantDivergenceMeasureFamily D)
    {G₁ G₂ : FeynmanGraph} {π : Equiv.Perm VertexId}
    (hπ : G₂ = G₁.mapPerm π) {A : AdmissibleSubgraphFor D G₁}
    (hA : @AdmissibleSubgraph.IsNonempty G₁ (D G₁) A) :
    @AdmissibleSubgraph.IsNonempty G₂ (D G₂) (mapPermAdmissibleSubgraphFor D Inv hπ A) := by
  rcases hA with ⟨γ, hγ⟩
  refine ⟨mapPermSubgraph hπ γ, ?_⟩
  change mapPermSubgraph hπ γ ∈ (mapPermAdmissibleSubgraphFor D Inv hπ A).elements
  rw [mapPermAdmissibleSubgraphFor_elements]
  exact Finset.mem_image.mpr ⟨γ, hγ, rfl⟩

/-- Component nonemptiness transports. -/
private theorem mapPermAdmissibleSubgraphFor_hasNonemptyComponents
    (D : DivergenceMeasureFamily) (Inv : PermInvariantDivergenceMeasureFamily D)
    {G₁ G₂ : FeynmanGraph} {π : Equiv.Perm VertexId}
    (hπ : G₂ = G₁.mapPerm π) {A : AdmissibleSubgraphFor D G₁}
    (hA : @AdmissibleSubgraph.HasNonemptyComponents G₁ (D G₁) A) :
    @AdmissibleSubgraph.HasNonemptyComponents G₂ (D G₂)
      (mapPermAdmissibleSubgraphFor D Inv hπ A) := by
  intro γ' hγ'
  rw [mapPermAdmissibleSubgraphFor_elements] at hγ'
  rcases Finset.mem_image.mp hγ' with ⟨γ, hγ, rfl⟩
  exact mapPermSubgraph_isNonempty hπ (hA γ hγ)

/-- Positive-internal-edge components transport. -/
private theorem mapPermAdmissibleSubgraphFor_hasPositiveInternalEdgesComponents
    (D : DivergenceMeasureFamily) (Inv : PermInvariantDivergenceMeasureFamily D)
    {G₁ G₂ : FeynmanGraph} {π : Equiv.Perm VertexId}
    (hπ : G₂ = G₁.mapPerm π) {A : AdmissibleSubgraphFor D G₁}
    (hA : @AdmissibleSubgraph.HasPositiveInternalEdgesComponents G₁ (D G₁) A) :
    @AdmissibleSubgraph.HasPositiveInternalEdgesComponents G₂ (D G₂)
      (mapPermAdmissibleSubgraphFor D Inv hπ A) := by
  intro γ' hγ'
  rw [mapPermAdmissibleSubgraphFor_elements] at hγ'
  rcases Finset.mem_image.mp hγ' with ⟨γ, hγ, rfl⟩
  rw [mps_internalEdges_card]
  exact hA γ hγ

/-- Proper-disjoint membership is preserved (forward). -/
private theorem mapPermAdmissibleSubgraphFor_mem_properDisjoint
    (D : DivergenceMeasureFamily) (Inv : PermInvariantDivergenceMeasureFamily D)
    {G₁ G₂ : FeynmanGraph} {π : Equiv.Perm VertexId}
    (hπ : G₂ = G₁.mapPerm π) {A : AdmissibleSubgraphFor D G₁}
    (hA : A ∈ G₁.properDisjointAdmissibleDivergentSubgraphsFor D) :
    mapPermAdmissibleSubgraphFor D Inv hπ A ∈
      G₂.properDisjointAdmissibleDivergentSubgraphsFor D := by
  obtain ⟨hAnonempty, hAncomp, hAcard, hApos⟩ :=
    (G₁.mem_properDisjointAdmissibleDivergentSubgraphsFor D A).mp hA
  have h1 := (@FeynmanGraph.mem_nonemptyDisjointAdmissibleDivergentSubgraphs G₁ (D G₁) _ A).mp
    hAnonempty
  have h2 := (@FeynmanGraph.mem_disjointAdmissibleDivergentSubgraphs G₁ (D G₁) _ A).mp h1.1
  have tDisjoint := mapPermAdmissibleSubgraphFor_isPairwiseDisjoint D Inv hπ h2.2
  have tNonempty := mapPermAdmissibleSubgraphFor_isNonempty D Inv hπ h1.2
  have tNComp := mapPermAdmissibleSubgraphFor_hasNonemptyComponents D Inv hπ hAncomp
  have tPos := mapPermAdmissibleSubgraphFor_hasPositiveInternalEdgesComponents D Inv hπ hApos
  have tCard :
      0 < (@AdmissibleSubgraph.internalEdges G₂ (D G₂)
        (mapPermAdmissibleSubgraphFor D Inv hπ A)).card := by
    rw [mapPermAdmissibleSubgraphFor_internalEdges_card]
    exact hAcard
  rw [G₂.mem_properDisjointAdmissibleDivergentSubgraphsFor D]
  refine ⟨?_, tNComp, tCard, tPos⟩
  rw [@FeynmanGraph.mem_nonemptyDisjointAdmissibleDivergentSubgraphs G₂ (D G₂) _]
  refine ⟨?_, tNonempty⟩
  rw [@FeynmanGraph.mem_disjointAdmissibleDivergentSubgraphs G₂ (D G₂) _]
  exact ⟨@FeynmanGraph.mem_admissibleDivergentSubgraphs G₂ (D G₂) _
    (mapPermAdmissibleSubgraphFor D Inv hπ A), tDisjoint⟩

/-- Proper-disjoint membership is preserved both ways. -/
private theorem mapPermAdmissibleSubgraphFor_mem_properDisjoint_iff
    (D : DivergenceMeasureFamily) (Inv : PermInvariantDivergenceMeasureFamily D)
    {G₁ G₂ : FeynmanGraph} {π : Equiv.Perm VertexId}
    (hπ : G₂ = G₁.mapPerm π) (A : AdmissibleSubgraphFor D G₁) :
    A ∈ G₁.properDisjointAdmissibleDivergentSubgraphsFor D ↔
      mapPermAdmissibleSubgraphFor D Inv hπ A ∈
        G₂.properDisjointAdmissibleDivergentSubgraphsFor D := by
  constructor
  · exact mapPermAdmissibleSubgraphFor_mem_properDisjoint D Inv hπ
  · intro hfwd
    have hback := mapPermAdmissibleSubgraphFor_mem_properDisjoint D Inv (hpiInv hπ) hfwd
    rwa [mapPermAdmissibleSubgraphFor_leftInv D Inv hπ A] at hback

/-! ## Step 4 — the φ⁴ forest coproduct index `Equiv` -/

/-- Index membership is preserved under the family rename (φ⁴). -/
theorem FeynmanGraph.phi4ForestCoproductIndex_mem_iff
    (G : FeynmanGraph) (π : Equiv.Perm VertexId)
    (A : AdmissibleSubgraphFor phi4DivergenceMeasureFamily G) :
    A ∈ G.phi4ForestCoproductIndex ↔
      mapPermAdmissibleSubgraphFor phi4DivergenceMeasureFamily
          phi4PermInvariantDivergenceMeasureFamily (rfl : G.mapPerm π = G.mapPerm π) A ∈
        (G.mapPerm π).phi4ForestCoproductIndex := by
  rw [G.mem_phi4ForestCoproductIndex, (G.mapPerm π).mem_phi4ForestCoproductIndex]
  refine and_congr ?_ ?_
  · exact mapPermAdmissibleSubgraphFor_mem_properDisjoint_iff phi4DivergenceMeasureFamily
      phi4PermInvariantDivergenceMeasureFamily (rfl : G.mapPerm π = G.mapPerm π) A
  · rw [mapPermAdmissibleSubgraphFor_complementEdges_card phi4DivergenceMeasureFamily
      phi4PermInvariantDivergenceMeasureFamily (rfl : G.mapPerm π = G.mapPerm π) A]

/-- **body-578 (TARGET) — the φ⁴ forest coproduct index rename `Equiv`.**  The same forests laid out
in different coordinates: an `Equiv` of the coproduct-index subtypes under vertex renaming.  A later
body's `Finset.sum_bij` reads this finished `Equiv`. -/
noncomputable def FeynmanGraph.phi4ForestCoproductIndexEquiv
    (G : FeynmanGraph) (π : Equiv.Perm VertexId) :
    {A : AdmissibleSubgraphFor phi4DivergenceMeasureFamily G //
        A ∈ G.phi4ForestCoproductIndex} ≃
      {A : AdmissibleSubgraphFor phi4DivergenceMeasureFamily (G.mapPerm π) //
        A ∈ (G.mapPerm π).phi4ForestCoproductIndex} :=
  Equiv.subtypeEquiv
    (admissibleSubgraphMapPermEquivFor phi4DivergenceMeasureFamily
      phi4PermInvariantDivergenceMeasureFamily (rfl : G.mapPerm π = G.mapPerm π))
    (fun A => G.phi4ForestCoproductIndex_mem_iff π A)

@[simp] theorem FeynmanGraph.phi4ForestCoproductIndexEquiv_apply_coe
    (G : FeynmanGraph) (π : Equiv.Perm VertexId)
    (A : {A : AdmissibleSubgraphFor phi4DivergenceMeasureFamily G //
        A ∈ G.phi4ForestCoproductIndex}) :
    ((G.phi4ForestCoproductIndexEquiv π) A).1 =
      mapPermAdmissibleSubgraphFor phi4DivergenceMeasureFamily
        phi4PermInvariantDivergenceMeasureFamily (rfl : G.mapPerm π = G.mapPerm π) A.1 := rfl

@[simp] theorem FeynmanGraph.phi4ForestCoproductIndexEquiv_symm_apply_coe
    (G : FeynmanGraph) (π : Equiv.Perm VertexId)
    (B : {A : AdmissibleSubgraphFor phi4DivergenceMeasureFamily (G.mapPerm π) //
        A ∈ (G.mapPerm π).phi4ForestCoproductIndex}) :
    ((G.phi4ForestCoproductIndexEquiv π).symm B).1 =
      mapPermAdmissibleSubgraphForPreimage phi4DivergenceMeasureFamily
        phi4PermInvariantDivergenceMeasureFamily (rfl : G.mapPerm π = G.mapPerm π) B.1 := rfl

end GaugeGeometry.QFT.Combinatorial
