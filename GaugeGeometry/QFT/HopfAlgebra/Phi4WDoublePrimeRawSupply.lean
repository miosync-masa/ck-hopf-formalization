import GaugeGeometry.QFT.HopfAlgebra.Phi4WDoublePrimeFiniteIndex
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfSubgraphMapPerm
import GaugeGeometry.QFT.HopfAlgebra.Phi4ForestRightFactor
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRetargetForget
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocContractForget
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocUniqueIdSupportedW
import GaugeGeometry.QFT.HopfAlgebra.SubgraphFintype
import GaugeGeometry.QFT.HopfAlgebra.Phi4LeftFactor

/-!
# QFT-R1-body-587 — family-indexed W″ raw canonical supply (rightTerm-free)

Body-586 built the family-indexed W″ finite index `resolvedLegSaturatedIndexFor D Inv G` and its
membership `iff`.  This body assembles the **body-413-equivalent RAW supply**: a `rightTerm`-free
canonical carrier (`index` / `starOf` / `hCD` / `carrier_mapPerm`) parametrised by an explicit
divergence family `D` + `Inv : PermInvariantDivergenceMeasureFamily D`, and inhabits it for φ⁴.

Everything is keyed to the explicit family `D`; ZERO forbidden divergence classes
(`IsPermInvariantDivergence` / `IsIsoInvariantDivergence` / `IsAmbientInvariantDivergence` /
`IsDivergencePreservedByContract` / `...ByAdmissibleForestContract`) appear in any declaration's type.
The polluted `ResolvedAdmissibleSubgraph.mapPerm` / `canonicalStarOfViaForget` /
`forget_contractWithStars_resolvedStar` are re-derived clean, never consumed.

## Contents

* Step 2 — the clean resolved-forest relabeling `mapPermResolvedAdmissibleSubgraphFor` (+ field lemmas,
  injectivity, `hσ`-parametrised inverse, and the rename `Equiv`), from the clean
  `ResolvedFeynmanSubgraph.mapPerm` primitives (never the polluted `ResolvedAdmissibleSubgraph.mapPerm`).
* Step 1 — the parallel raw interface `ResolvedCanonicalCarrierProperRawSupplyFor`.
* Step 3 — the W″ index `mapPerm` closure `resolvedLegSaturatedIndexFor_mapPerm`.
* Step 4/5 — a clean lifted canonical star `cleanStarOf` and the load-bearing `hCD`
  (`resolvedWDoublePrimeContract_hCD`).
* Step 6 — the concrete φ⁴ supply `phi4WDoublePrimeRawCanonicalSupply`.

Per the HALT: no family right-term, no `rightTerm_mapPerm`, no full `ResolvedCoproductProperForestData`,
no cast to the old `ResolvedCanonicalCarrierProperSupply`, no Measure / E / rep*, no coproduct / coassoc,
no strict cross-presentation star equality `targetStar = σ sourceStar`; exactly one new `structure`; no
`instance` / `class`; no `variable [`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

/-! ## Step 2 — clean resolved-forest relabeling (family-explicit) -/

/-- A resolved subgraph of `G₁` relabeled to `G₂ = G₁.mapPerm σ` (subgraph-level cast, mirroring the
flat `mapPermSubgraph`), built on the CLEAN `ResolvedFeynmanSubgraph.mapPerm`. -/
noncomputable def mapPermRFS {G₁ G₂ : ResolvedFeynmanGraph} {σ : Equiv.Perm VertexId}
    (hσ : G₂ = G₁.mapPerm σ) (γ : ResolvedFeynmanSubgraph G₁) : ResolvedFeynmanSubgraph G₂ :=
  hσ ▸ ResolvedFeynmanSubgraph.mapPerm σ γ

@[simp] theorem mapPermRFS_vertices {G₁ G₂ : ResolvedFeynmanGraph} {σ : Equiv.Perm VertexId}
    (hσ : G₂ = G₁.mapPerm σ) (γ : ResolvedFeynmanSubgraph G₁) :
    (mapPermRFS hσ γ).vertices = γ.vertices.image σ := by
  unfold mapPermRFS; subst hσ; rfl

@[simp] theorem mapPermRFS_internalEdges {G₁ G₂ : ResolvedFeynmanGraph} {σ : Equiv.Perm VertexId}
    (hσ : G₂ = G₁.mapPerm σ) (γ : ResolvedFeynmanSubgraph G₁) :
    (mapPermRFS hσ γ).internalEdges = γ.internalEdges.map (ResolvedFeynmanEdge.map σ) := by
  unfold mapPermRFS; subst hσ; rfl

@[simp] theorem mapPermRFS_externalLegs {G₁ G₂ : ResolvedFeynmanGraph} {σ : Equiv.Perm VertexId}
    (hσ : G₂ = G₁.mapPerm σ) (γ : ResolvedFeynmanSubgraph G₁) :
    (mapPermRFS hσ γ).externalLegs = γ.externalLegs.map (ResolvedExternalLeg.map σ) := by
  unfold mapPermRFS; subst hσ; rfl

/-- The inverse ambient equality obtained from `hσ` via the group identity. -/
theorem hsigmaInv {G₁ G₂ : ResolvedFeynmanGraph} {σ : Equiv.Perm VertexId}
    (hσ : G₂ = G₁.mapPerm σ) : G₁ = G₂.mapPerm σ⁻¹ := by
  subst hσ; rw [← ResolvedFeynmanGraph.mapPerm_mul]; simp

theorem mapPermRFS_disjoint {G₁ G₂ : ResolvedFeynmanGraph} {σ : Equiv.Perm VertexId}
    (hσ : G₂ = G₁.mapPerm σ) {γ δ : ResolvedFeynmanSubgraph G₁} (h : γ.Disjoint δ) :
    (mapPermRFS hσ γ).Disjoint (mapPermRFS hσ δ) := by
  unfold mapPermRFS; subst hσ; exact ResolvedFeynmanSubgraph.mapPerm_disjoint σ h

/-- Round-trip of two subgraph relabelings whose permutations cancel. -/
theorem mapPermRFS_roundtripGen {Ga Gb : ResolvedFeynmanGraph} {a b : Equiv.Perm VertexId}
    (ha : Gb = Ga.mapPerm a) (hb : Ga = Gb.mapPerm b) (hab : b * a = 1)
    (δ : ResolvedFeynmanSubgraph Ga) :
    mapPermRFS hb (mapPermRFS ha δ) = δ := by
  apply ResolvedFeynmanSubgraph.ext
  · rw [mapPermRFS_vertices, mapPermRFS_vertices, Finset.image_image]
    have hcomp : (⇑b ∘ ⇑a) = (id : VertexId → VertexId) := by
      funext x
      have hx : (b * a) x = x := by rw [hab]; rfl
      simpa [Equiv.Perm.mul_apply] using hx
    rw [hcomp, Finset.image_id]
  · rw [mapPermRFS_internalEdges, mapPermRFS_internalEdges, Multiset.map_map]
    have hE : (ResolvedFeynmanEdge.map b) ∘ (ResolvedFeynmanEdge.map a) = id := by
      funext e; show ResolvedFeynmanEdge.map b (ResolvedFeynmanEdge.map a e) = e
      rw [← ResolvedFeynmanEdge.map_mul, hab, ResolvedFeynmanEdge.map_one]
    rw [hE, Multiset.map_id]
  · rw [mapPermRFS_externalLegs, mapPermRFS_externalLegs, Multiset.map_map]
    have hL : (ResolvedExternalLeg.map b) ∘ (ResolvedExternalLeg.map a) = id := by
      funext ℓ; show ResolvedExternalLeg.map b (ResolvedExternalLeg.map a ℓ) = ℓ
      rw [← ResolvedExternalLeg.map_mul, hab, ResolvedExternalLeg.map_one]
    rw [hL, Multiset.map_id]

theorem mapPermRFS_injective {G₁ G₂ : ResolvedFeynmanGraph} {σ : Equiv.Perm VertexId}
    (hσ : G₂ = G₁.mapPerm σ) :
    Function.Injective (mapPermRFS hσ : ResolvedFeynmanSubgraph G₁ → ResolvedFeynmanSubgraph G₂) :=
  Function.LeftInverse.injective
    (g := mapPermRFS (hsigmaInv hσ))
    (fun δ => mapPermRFS_roundtripGen hσ (hsigmaInv hσ) (inv_mul_cancel σ) δ)

/-- A `HEq` of flat subgraphs from a graph equality + the three data-field equalities (clean
re-derivation of `feynmanSubgraph_heq_of_data`, whose library version is forbidden-class-polluted). -/
theorem flatSubgraph_heq_of_data {G₁ G₂ : FeynmanGraph} (hg : G₁ = G₂)
    {a : FeynmanSubgraph G₁} {b : FeynmanSubgraph G₂}
    (hv : a.vertices = b.vertices) (hi : a.internalEdges = b.internalEdges)
    (he : a.externalLegs = b.externalLegs) : HEq a b := by
  subst hg
  apply heq_of_eq
  obtain ⟨av, ai, ae, _, _, _, _, _⟩ := a
  obtain ⟨bv, bi, be, _, _, _, _, _⟩ := b
  dsimp only at hv hi he
  subst hv; subst hi; subst he; rfl

/-- The forget of a relabeled subgraph is heterogeneously the relabeled forget (clean re-derivation
of the forbidden-class-polluted `ResolvedFeynmanSubgraph.forget_mapPerm`). -/
theorem mapPermRFS_forget {G₁ G₂ : ResolvedFeynmanGraph} {σ : Equiv.Perm VertexId}
    (hσ : G₂ = G₁.mapPerm σ) (γ : ResolvedFeynmanSubgraph G₁) :
    HEq ((mapPermRFS hσ γ).forget) (γ.forget.mapPerm σ) := by
  unfold mapPermRFS; subst hσ
  refine flatSubgraph_heq_of_data (ResolvedFeynmanGraph.forget_mapPerm σ G₁) ?_ ?_ ?_
  · simp only [ResolvedFeynmanSubgraph.forget_vertices, ResolvedFeynmanSubgraph.mapPerm_vertices,
      FeynmanSubgraph.mapPerm_vertices]
  · simp only [ResolvedFeynmanSubgraph.forget_internalEdges,
      ResolvedFeynmanSubgraph.mapPerm_internalEdges, FeynmanSubgraph.mapPerm_internalEdges,
      Multiset.map_map]
    exact Multiset.map_congr rfl (fun e _ => by simp)
  · simp only [ResolvedFeynmanSubgraph.forget_externalLegs,
      ResolvedFeynmanSubgraph.mapPerm_externalLegs, FeynmanSubgraph.mapPerm_externalLegs,
      Multiset.map_map]
    exact Multiset.map_congr rfl (fun ℓ _ => by simp)

/-- Clean extensionality of a family-indexed resolved admissible subgraph by its `elements`
(the library `ResolvedAdmissibleSubgraph.ext_elements` is forbidden-class-polluted). -/
theorem rasFor_ext {D : DivergenceMeasureFamily} {G : ResolvedFeynmanGraph}
    {A B : @ResolvedAdmissibleSubgraph D G} (h : A.elements = B.elements) : A = B := by
  obtain ⟨ae, a1, a2⟩ := A
  obtain ⟨be, b1, b2⟩ := B
  dsimp only at h
  subst h
  rfl

/-- Family-explicit HEq transport of `IsConnectedDivergent` across a graph equality. -/
theorem isCD_of_heq_family (D : DivergenceMeasureFamily) {G₁ G₂ : FeynmanGraph} (hg : G₁ = G₂)
    {a : FeynmanSubgraph G₁} {b : FeynmanSubgraph G₂} (hab : HEq a b)
    (hb : @FeynmanSubgraph.IsConnectedDivergent G₂ (D G₂) b) :
    @FeynmanSubgraph.IsConnectedDivergent G₁ (D G₁) a := by
  subst hg; obtain rfl := eq_of_heq hab; exact hb

/-- **body-587 (Step 2) — clean resolved admissible-forest relabeling**, family-explicit; components
transported by the CLEAN `mapPermRFS`, component CD via the family transport, disjointness clean. -/
noncomputable def mapPermResolvedAdmissibleSubgraphFor
    (D : DivergenceMeasureFamily) (Inv : PermInvariantDivergenceMeasureFamily D)
    {G₁ G₂ : ResolvedFeynmanGraph} {σ : Equiv.Perm VertexId} (hσ : G₂ = G₁.mapPerm σ)
    (A : @ResolvedAdmissibleSubgraph D G₁) : @ResolvedAdmissibleSubgraph D G₂ where
  elements := A.elements.image (mapPermRFS hσ)
  isConnectedDivergent := by
    intro γ' hγ'
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hγ'
    refine isCD_of_heq_family D (hσ ▸ ResolvedFeynmanGraph.forget_mapPerm σ G₁ :
        G₂.forget = G₁.forget.mapPerm σ) (mapPermRFS_forget hσ γ) ?_
    exact (FeynmanSubgraph.mapPerm_isConnectedDivergent_iff_of_family D Inv σ γ.forget).mpr
      (A.isConnectedDivergent γ hγ)
  pairwiseDisjoint := by
    intro γ' hγ' δ' hδ' hne
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hγ'
    obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.mp hδ'
    exact mapPermRFS_disjoint hσ (A.pairwiseDisjoint hγ hδ (fun h => hne (by rw [h])))

@[simp] theorem mapPermResolvedAdmissibleSubgraphFor_elements
    (D : DivergenceMeasureFamily) (Inv : PermInvariantDivergenceMeasureFamily D)
    {G₁ G₂ : ResolvedFeynmanGraph} {σ : Equiv.Perm VertexId} (hσ : G₂ = G₁.mapPerm σ)
    (A : @ResolvedAdmissibleSubgraph D G₁) :
    (mapPermResolvedAdmissibleSubgraphFor D Inv hσ A).elements =
      A.elements.image (mapPermRFS hσ) := rfl

theorem mapPermResolvedAdmissibleSubgraphFor_injective
    (D : DivergenceMeasureFamily) (Inv : PermInvariantDivergenceMeasureFamily D)
    {G₁ G₂ : ResolvedFeynmanGraph} {σ : Equiv.Perm VertexId} (hσ : G₂ = G₁.mapPerm σ) :
    Function.Injective (mapPermResolvedAdmissibleSubgraphFor D Inv hσ) := by
  intro A B h
  apply rasFor_ext
  have : A.elements.image (mapPermRFS hσ) = B.elements.image (mapPermRFS hσ) :=
    congrArg ResolvedAdmissibleSubgraph.elements h
  exact Finset.image_injective (mapPermRFS_injective hσ) this

/-- Reverse relabeling, along `σ⁻¹`. -/
noncomputable def mapPermResolvedAdmissibleSubgraphForPreimage
    (D : DivergenceMeasureFamily) (Inv : PermInvariantDivergenceMeasureFamily D)
    {G₁ G₂ : ResolvedFeynmanGraph} {σ : Equiv.Perm VertexId} (hσ : G₂ = G₁.mapPerm σ)
    (A : @ResolvedAdmissibleSubgraph D G₂) : @ResolvedAdmissibleSubgraph D G₁ :=
  mapPermResolvedAdmissibleSubgraphFor D Inv (hsigmaInv hσ) A

theorem mapPermResolvedAdmissibleSubgraphFor_leftInv
    (D : DivergenceMeasureFamily) (Inv : PermInvariantDivergenceMeasureFamily D)
    {G₁ G₂ : ResolvedFeynmanGraph} {σ : Equiv.Perm VertexId} (hσ : G₂ = G₁.mapPerm σ)
    (A : @ResolvedAdmissibleSubgraph D G₁) :
    mapPermResolvedAdmissibleSubgraphFor D Inv (hsigmaInv hσ)
        (mapPermResolvedAdmissibleSubgraphFor D Inv hσ A) = A := by
  apply rasFor_ext
  rw [mapPermResolvedAdmissibleSubgraphFor_elements, mapPermResolvedAdmissibleSubgraphFor_elements,
    Finset.image_image]
  rw [show ((mapPermRFS (hsigmaInv hσ)) ∘ (mapPermRFS hσ) :
        ResolvedFeynmanSubgraph G₁ → ResolvedFeynmanSubgraph G₁) = id from
      funext (fun δ => mapPermRFS_roundtripGen hσ (hsigmaInv hσ) (inv_mul_cancel σ) δ)]
  exact Finset.image_id

theorem mapPermResolvedAdmissibleSubgraphFor_rightInv
    (D : DivergenceMeasureFamily) (Inv : PermInvariantDivergenceMeasureFamily D)
    {G₁ G₂ : ResolvedFeynmanGraph} {σ : Equiv.Perm VertexId} (hσ : G₂ = G₁.mapPerm σ)
    (B : @ResolvedAdmissibleSubgraph D G₂) :
    mapPermResolvedAdmissibleSubgraphFor D Inv hσ
        (mapPermResolvedAdmissibleSubgraphFor D Inv (hsigmaInv hσ) B) = B := by
  apply rasFor_ext
  rw [mapPermResolvedAdmissibleSubgraphFor_elements, mapPermResolvedAdmissibleSubgraphFor_elements,
    Finset.image_image]
  rw [show ((mapPermRFS hσ) ∘ (mapPermRFS (hsigmaInv hσ)) :
        ResolvedFeynmanSubgraph G₂ → ResolvedFeynmanSubgraph G₂) = id from
      funext (fun γ => mapPermRFS_roundtripGen (hsigmaInv hσ) hσ (mul_inv_cancel σ) γ)]
  exact Finset.image_id

/-- **body-587 (Step 2) — the resolved admissible-forest rename `Equiv`** for an explicit family. -/
noncomputable def resolvedAdmissibleSubgraphMapPermEquivFor
    (D : DivergenceMeasureFamily) (Inv : PermInvariantDivergenceMeasureFamily D)
    {G₁ G₂ : ResolvedFeynmanGraph} {σ : Equiv.Perm VertexId} (hσ : G₂ = G₁.mapPerm σ) :
    @ResolvedAdmissibleSubgraph D G₁ ≃ @ResolvedAdmissibleSubgraph D G₂ where
  toFun := mapPermResolvedAdmissibleSubgraphFor D Inv hσ
  invFun := mapPermResolvedAdmissibleSubgraphForPreimage D Inv hσ
  left_inv A := mapPermResolvedAdmissibleSubgraphFor_leftInv D Inv hσ A
  right_inv B := mapPermResolvedAdmissibleSubgraphFor_rightInv D Inv hσ B

/-! ## Step 1 — the parallel raw interface -/

/-- **body-587 (Step 1) — the family-indexed `rightTerm`-free raw canonical carrier.**  Mirrors
body-413's `ResolvedCanonicalCarrierProperRawSupply`, but keyed to the explicit divergence family
`(D, Inv)` — `hCD` lands in body-584's `IsConnectedDivergentFor`, and `carrier_mapPerm` uses the clean
`mapPermResolvedAdmissibleSubgraphFor`. -/
structure ResolvedCanonicalCarrierProperRawSupplyFor
    (D : DivergenceMeasureFamily) (Inv : PermInvariantDivergenceMeasureFamily D) where
  /-- The per-graph proper-forest index. -/
  index : (G : ResolvedFeynmanGraph) → @ResolvedProperForestFiniteIndex D G
  /-- The star assignment per forest. -/
  starOf : (G : ResolvedFeynmanGraph) → @ResolvedAdmissibleSubgraph D G →
    (ResolvedFeynmanSubgraph G → VertexId)
  /-- The star-contraction of every index member is family-connected-divergent. -/
  hCD : ∀ (G : ResolvedFeynmanGraph) (A : @ResolvedAdmissibleSubgraph D G), A ∈ (index G).carrier →
    ResolvedFeynmanGraphClass.IsConnectedDivergentFor D Inv
      (A.contractWithStars (starOf G A)).toResolvedClass
  /-- The index carrier transports by relabeling. -/
  carrier_mapPerm : ∀ (G : ResolvedFeynmanGraph) (σ : Equiv.Perm VertexId),
    (index (G.mapPerm σ)).carrier =
      ((index G).carrier).image
        (mapPermResolvedAdmissibleSubgraphFor D Inv (rfl : G.mapPerm σ = G.mapPerm σ))

/-! ## Step 3 — the W″ index `mapPerm` closure -/

/-- `ResolvedFeynmanEdge.map σ` is injective (clean re-derivation; the library
`ResolvedFeynmanEdge.map_injective` carries a spurious `DivergenceMeasure` binder). -/
theorem rfeMap_injective (σ : Equiv.Perm VertexId) :
    Function.Injective (ResolvedFeynmanEdge.map σ) := by
  intro a b hab; cases a; cases b
  simp only [ResolvedFeynmanEdge.map, ResolvedFeynmanEdge.mk.injEq] at hab
  obtain ⟨hid, hs, ht, hsec⟩ := hab
  exact (ResolvedFeynmanEdge.mk.injEq ..).mpr ⟨hid, σ.injective hs, σ.injective ht, hsec⟩

/-- `EdgeIdsUnique` is `mapPerm`-invariant (instance-free). -/
theorem edgeIdsUnique_mapPerm_iff (G : ResolvedFeynmanGraph) (σ : Equiv.Perm VertexId) :
    (G.mapPerm σ).EdgeIdsUnique ↔ G.EdgeIdsUnique := by
  have hIE : (G.mapPerm σ).internalEdges = G.internalEdges.map (ResolvedFeynmanEdge.map σ) := rfl
  have hid : ∀ e : ResolvedFeynmanEdge, (ResolvedFeynmanEdge.map σ e).edgeId = e.edgeId := fun _ => rfl
  unfold ResolvedFeynmanGraph.EdgeIdsUnique
  rw [hIE]
  constructor
  · intro h e₁ he₁ e₂ he₂ heq
    have := h _ (Multiset.mem_map_of_mem (ResolvedFeynmanEdge.map σ) he₁) _
      (Multiset.mem_map_of_mem (ResolvedFeynmanEdge.map σ) he₂) (by rw [hid, hid]; exact heq)
    exact rfeMap_injective σ this
  · intro h e₁ he₁ e₂ he₂ heq
    obtain ⟨d₁, hd₁, rfl⟩ := Multiset.mem_map.mp he₁
    obtain ⟨d₂, hd₂, rfl⟩ := Multiset.mem_map.mp he₂
    rw [hid, hid] at heq
    rw [h d₁ hd₁ d₂ hd₂ heq]

/-- `LegIdsUnique` is `mapPerm`-invariant (instance-free). -/
theorem legIdsUnique_mapPerm_iff (G : ResolvedFeynmanGraph) (σ : Equiv.Perm VertexId) :
    (G.mapPerm σ).LegIdsUnique ↔ G.LegIdsUnique := by
  have hLE : (G.mapPerm σ).externalLegs = G.externalLegs.map (ResolvedExternalLeg.map σ) := rfl
  have hid : ∀ ℓ : ResolvedExternalLeg, (ResolvedExternalLeg.map σ ℓ).legId = ℓ.legId := fun _ => rfl
  have hinj : Function.Injective (ResolvedExternalLeg.map σ) := by
    intro a b hab; cases a; cases b
    simp only [ResolvedExternalLeg.map, ResolvedExternalLeg.mk.injEq] at hab
    obtain ⟨hid', ha, hsec⟩ := hab
    exact (ResolvedExternalLeg.mk.injEq ..).mpr ⟨hid', σ.injective ha, hsec⟩
  unfold ResolvedFeynmanGraph.LegIdsUnique
  rw [hLE]
  constructor
  · intro h ℓ₁ hℓ₁ ℓ₂ hℓ₂ heq
    have := h _ (Multiset.mem_map_of_mem (ResolvedExternalLeg.map σ) hℓ₁) _
      (Multiset.mem_map_of_mem (ResolvedExternalLeg.map σ) hℓ₂) (by rw [hid, hid]; exact heq)
    exact hinj this
  · intro h ℓ₁ hℓ₁ ℓ₂ hℓ₂ heq
    obtain ⟨d₁, hd₁, rfl⟩ := Multiset.mem_map.mp hℓ₁
    obtain ⟨d₂, hd₂, rfl⟩ := Multiset.mem_map.mp hℓ₂
    rw [hid, hid] at heq
    rw [h d₁ hd₁ d₂ hd₂ heq]

/-- `Multiset.map` distributes over subtraction along an injective map (private, clean re-derivation). -/
private theorem map_sub_inj {α β : Type*} [DecidableEq α] [DecidableEq β] {f : α → β}
    (hf : Function.Injective f) (s t : Multiset α) : (s - t).map f = s.map f - t.map f := by
  ext b
  rw [Multiset.count_sub]
  by_cases hb : ∃ a, f a = b
  · obtain ⟨a, rfl⟩ := hb
    rw [Multiset.count_map_eq_count' f _ hf, Multiset.count_map_eq_count' f _ hf,
        Multiset.count_map_eq_count' f _ hf, Multiset.count_sub]
  · have h0 : ∀ m : Multiset α, (m.map f).count b = 0 := fun m => by
      rw [Multiset.count_eq_zero, Multiset.mem_map]; rintro ⟨a, _, rfl⟩; exact hb ⟨a, rfl⟩
    rw [h0, h0, h0]

section IndexMapPerm
variable (D : DivergenceMeasureFamily) (Inv : PermInvariantDivergenceMeasureFamily D)
    {G : ResolvedFeynmanGraph} (σ : Equiv.Perm VertexId)

/-- The relabeled forest's aggregated internal edges. -/
theorem mpFor_internalEdges (A : @ResolvedAdmissibleSubgraph D G) :
    (mapPermResolvedAdmissibleSubgraphFor D Inv (rfl : G.mapPerm σ = G.mapPerm σ) A).internalEdges =
      A.internalEdges.map (ResolvedFeynmanEdge.map σ) := by
  simp only [ResolvedAdmissibleSubgraph.internalEdges,
    mapPermResolvedAdmissibleSubgraphFor_elements]
  rw [Finset.sum_image (fun a _ b _ h => mapPermRFS_injective _ h)]
  simp only [mapPermRFS_internalEdges]
  exact (map_sum (Multiset.mapAddMonoidHom (ResolvedFeynmanEdge.map σ))
    (fun γ => γ.internalEdges) A.elements).symm

/-- The relabeled forest's complement edges. -/
theorem mpFor_complementEdges (A : @ResolvedAdmissibleSubgraph D G) :
    (mapPermResolvedAdmissibleSubgraphFor D Inv (rfl : G.mapPerm σ = G.mapPerm σ) A).complementEdges =
      A.complementEdges.map (ResolvedFeynmanEdge.map σ) := by
  unfold ResolvedAdmissibleSubgraph.complementEdges
  rw [mpFor_internalEdges]
  have hG : (G.mapPerm σ).internalEdges = G.internalEdges.map (ResolvedFeynmanEdge.map σ) := rfl
  rw [hG]
  exact (map_sub_inj (rfeMap_injective σ) G.internalEdges A.internalEdges).symm

/-- **body-587 (Step 3) — `IsProperForest` transports along the clean relabeling.** -/
theorem mpFor_isProperForest_iff (A : @ResolvedAdmissibleSubgraph D G) :
    (mapPermResolvedAdmissibleSubgraphFor D Inv (rfl : G.mapPerm σ = G.mapPerm σ) A).IsProperForest
      ↔ A.IsProperForest := by
  simp only [ResolvedAdmissibleSubgraph.IsProperForest, ResolvedAdmissibleSubgraph.IsNonempty,
    ResolvedAdmissibleSubgraph.HasNonemptyComponents,
    ResolvedAdmissibleSubgraph.HasPositiveInternalEdgesComponents,
    mapPermResolvedAdmissibleSubgraphFor_elements, mpFor_internalEdges D Inv σ A,
    mpFor_complementEdges D Inv σ A, Multiset.card_map, Finset.image_nonempty,
    Finset.forall_mem_image, ResolvedFeynmanSubgraph.IsNonempty,
    ResolvedFeynmanSubgraph.vertexCount, mapPermRFS_vertices, mapPermRFS_internalEdges,
    Finset.card_image_of_injective _ σ.injective]

/-- Single-component external-leg saturation transports (clean re-derivation of body-532). -/
theorem mpFor_externalLegSaturated_iff {H : ResolvedFeynmanGraph} (δ : ResolvedFeynmanSubgraph H) :
    ResolvedExternalLegSaturated (H.mapPerm σ)
        (mapPermRFS (rfl : H.mapPerm σ = H.mapPerm σ) δ)
      ↔ ResolvedExternalLegSaturated H δ := by
  have hmapinj : Function.Injective (ResolvedExternalLeg.map σ) := by
    intro ℓ₁ ℓ₂ h
    cases ℓ₁; cases ℓ₂
    simp only [ResolvedExternalLeg.map, ResolvedExternalLeg.mk.injEq] at h ⊢
    exact ⟨h.1, σ.injective h.2.1, h.2.2⟩
  have hfm : (H.externalLegs.map (ResolvedExternalLeg.map σ)).filter
        (fun ℓ => ℓ.attachedTo ∈ δ.vertices.image σ)
      = (H.externalLegs.filter (fun ℓ => ℓ.attachedTo ∈ δ.vertices)).map
          (ResolvedExternalLeg.map σ) := by
    rw [Multiset.filter_map]
    exact congrArg (Multiset.map (ResolvedExternalLeg.map σ))
      (Multiset.filter_congr (fun ℓ _ => σ.injective.mem_finset_image))
  simp only [ResolvedExternalLegSaturated, ResolvedFeynmanGraph.mapPerm,
    mapPermRFS_externalLegs, mapPermRFS_vertices, hfm, Multiset.map_le_map_iff hmapinj]

/-- **body-587 (Step 3) — forest external-leg saturation transports along the clean relabeling.** -/
theorem mpFor_forestExternalLegSaturated_iff (A : @ResolvedAdmissibleSubgraph D G) :
    ResolvedForestExternalLegSaturated
        (mapPermResolvedAdmissibleSubgraphFor D Inv (rfl : G.mapPerm σ = G.mapPerm σ) A)
      ↔ ResolvedForestExternalLegSaturated A := by
  unfold ResolvedForestExternalLegSaturated
  constructor
  · intro h δ hδ
    have hmem : mapPermRFS (rfl : G.mapPerm σ = G.mapPerm σ) δ ∈
        (mapPermResolvedAdmissibleSubgraphFor D Inv (rfl : G.mapPerm σ = G.mapPerm σ) A).elements := by
      rw [mapPermResolvedAdmissibleSubgraphFor_elements]; exact Finset.mem_image_of_mem _ hδ
    exact (mpFor_externalLegSaturated_iff σ δ).mp (h _ hmem)
  · intro h δ' hδ'
    rw [mapPermResolvedAdmissibleSubgraphFor_elements] at hδ'
    obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.mp hδ'
    exact (mpFor_externalLegSaturated_iff σ δ).mpr (h δ hδ)

private theorem perm_mem_image_iff (σ : Equiv.Perm VertexId) (v : VertexId) (s : Finset VertexId) :
    σ v ∈ s.image σ ↔ v ∈ s := by
  constructor
  · intro hv
    obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp hv
    rwa [σ.injective hwv] at hw
  · intro hv; exact Finset.mem_image_of_mem σ hv

/-- Ambient support is `mapPerm`-invariant (instance-free re-derivation of the spuriously polluted
`ambientSupported_mapPerm_iff`). -/
theorem resolvedAmbientSupported_mapPerm_iff (G : ResolvedFeynmanGraph) (σ : Equiv.Perm VertexId) :
    ResolvedAmbientSupported (G.mapPerm σ) ↔ ResolvedAmbientSupported G := by
  constructor
  · rintro ⟨hE, hL⟩
    refine ⟨fun e₀ he₀ => ?_, fun ℓ₀ hℓ₀ => ?_⟩
    · have hmem : e₀.map σ ∈ (G.mapPerm σ).internalEdges := Multiset.mem_map_of_mem _ he₀
      obtain ⟨hs, ht⟩ := hE (e₀.map σ) hmem
      exact ⟨(perm_mem_image_iff σ e₀.source G.vertices).mp hs,
        (perm_mem_image_iff σ e₀.target G.vertices).mp ht⟩
    · have hmem : ℓ₀.map σ ∈ (G.mapPerm σ).externalLegs := Multiset.mem_map_of_mem _ hℓ₀
      exact (perm_mem_image_iff σ ℓ₀.attachedTo G.vertices).mp (hL (ℓ₀.map σ) hmem)
  · rintro ⟨hE, hL⟩
    refine ⟨fun e he => ?_, fun ℓ hℓ => ?_⟩
    · obtain ⟨e₀, he₀, rfl⟩ := Multiset.mem_map.mp he
      obtain ⟨hs, ht⟩ := hE e₀ he₀
      exact ⟨(perm_mem_image_iff σ e₀.source G.vertices).mpr hs,
        (perm_mem_image_iff σ e₀.target G.vertices).mpr ht⟩
    · obtain ⟨ℓ₀, hℓ₀, rfl⟩ := Multiset.mem_map.mp hℓ
      exact (perm_mem_image_iff σ ℓ₀.attachedTo G.vertices).mpr (hL ℓ₀ hℓ₀)

/-- **body-587 (Step 3 target) — the W″ index carrier transports along the clean relabeling.** -/
theorem resolvedLegSaturatedIndexFor_mapPerm :
    resolvedLegSaturatedIndexFor D Inv (G.mapPerm σ) =
      (resolvedLegSaturatedIndexFor D Inv G).image
        (mapPermResolvedAdmissibleSubgraphFor D Inv (rfl : G.mapPerm σ = G.mapPerm σ)) := by
  ext A
  rw [Finset.mem_image, mem_resolvedLegSaturatedIndexFor]
  constructor
  · rintro ⟨hsupp, hcd, hedge, hleg, hpf, hsat⟩
    refine ⟨mapPermResolvedAdmissibleSubgraphForPreimage D Inv
      (rfl : G.mapPerm σ = G.mapPerm σ) A, ?_, ?_⟩
    · rw [mem_resolvedLegSaturatedIndexFor]
      have hBA : mapPermResolvedAdmissibleSubgraphFor D Inv (rfl : G.mapPerm σ = G.mapPerm σ)
          (mapPermResolvedAdmissibleSubgraphForPreimage D Inv (rfl : G.mapPerm σ = G.mapPerm σ) A)
          = A := mapPermResolvedAdmissibleSubgraphFor_rightInv D Inv rfl A
      refine ⟨(resolvedAmbientSupported_mapPerm_iff G σ).mp hsupp, ?_,
        (edgeIdsUnique_mapPerm_iff G σ).mp hedge, (legIdsUnique_mapPerm_iff G σ).mp hleg,
        ?_, ?_⟩
      · rwa [ResolvedFeynmanGraph.toResolvedClass_mapPerm] at hcd
      · rw [← mpFor_isProperForest_iff D Inv σ, hBA]; exact hpf
      · rw [← mpFor_forestExternalLegSaturated_iff D Inv σ, hBA]; exact hsat
    · exact mapPermResolvedAdmissibleSubgraphFor_rightInv D Inv rfl A
  · rintro ⟨B, hB, rfl⟩
    rw [mem_resolvedLegSaturatedIndexFor] at hB
    obtain ⟨hsupp, hcd, hedge, hleg, hpf, hsat⟩ := hB
    refine ⟨(resolvedAmbientSupported_mapPerm_iff G σ).mpr hsupp, ?_,
      (edgeIdsUnique_mapPerm_iff G σ).mpr hedge, (legIdsUnique_mapPerm_iff G σ).mpr hleg,
      (mpFor_isProperForest_iff D Inv σ B).mpr hpf,
      (mpFor_forestExternalLegSaturated_iff D Inv σ B).mpr hsat⟩
    rw [ResolvedFeynmanGraph.toResolvedClass_mapPerm]; exact hcd


end IndexMapPerm

/-! ## Step 4a — clean resolved→flat forget bridge (re-derivations, forbidden-class-free)

The library forget-bridge lemmas (`forget_vertices_eq`, `forget_internalEdges_eq_map`,
`forget_isPairwiseDisjoint`, `forget_mem_properDisjointAdmissibleDivergentSubgraphs`, …) all live in
maximally forbidden-class-polluted sections.  We re-derive the pieces we need from the CLEAN
primitives (`ResolvedAdmissibleSubgraph.forget_elements`, `internalEdges_le_of_components_le`,
`forget_injOn_elements_of_isProperForest`, the flat `mem_*` membership lemmas — all only
`DivergenceMeasure`). -/

/-- `Multiset.map forget` distributes over a finite sum of component internal edges. -/
private theorem fgMapSum {G : ResolvedFeynmanGraph}
    (s : Finset (ResolvedFeynmanSubgraph G)) :
    (∑ γ ∈ s, γ.internalEdges).map ResolvedFeynmanEdge.forget
      = ∑ γ ∈ s, γ.internalEdges.map ResolvedFeynmanEdge.forget := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert γ s hγs ih =>
      rw [Finset.sum_insert hγs, Finset.sum_insert hγs, Multiset.map_add, ih]

/-- Forgetting keeps the vertex set. -/
theorem fgVerticesEq {D : DivergenceMeasureFamily} {G : ResolvedFeynmanGraph}
    (A : @ResolvedAdmissibleSubgraph D G) : A.forget.vertices = A.vertices := by
  letI : (H : FeynmanGraph) → DivergenceMeasure H := D
  ext v
  simp only [AdmissibleSubgraph.vertices, ResolvedAdmissibleSubgraph.vertices, Finset.mem_biUnion,
    ResolvedAdmissibleSubgraph.forget_elements, Finset.mem_image]
  constructor
  · rintro ⟨η, ⟨γ, hγ, rfl⟩, hv⟩
    exact ⟨γ, hγ, by rwa [ResolvedFeynmanSubgraph.forget_vertices] at hv⟩
  · rintro ⟨γ, hγ, hv⟩
    exact ⟨γ.forget, ⟨γ, hγ, rfl⟩, by rwa [ResolvedFeynmanSubgraph.forget_vertices]⟩

/-- Forgetting is injective on the components of a proper forest. -/
theorem fgInjOn {D : DivergenceMeasureFamily} {G : ResolvedFeynmanGraph}
    (A : @ResolvedAdmissibleSubgraph D G) (hne : A.HasNonemptyComponents) :
    Set.InjOn ResolvedFeynmanSubgraph.forget {γ | γ ∈ A.elements} := by
  intro γ₁ h₁ γ₂ h₂ hfg
  by_contra hcon
  have hdis : _root_.Disjoint γ₁.vertices γ₂.vertices := A.pairwiseDisjoint h₁ h₂ hcon
  have hv : γ₁.vertices = γ₂.vertices := by
    rw [← ResolvedFeynmanSubgraph.forget_vertices γ₁,
      ← ResolvedFeynmanSubgraph.forget_vertices γ₂, hfg]
  rw [← hv] at hdis
  obtain ⟨v, hvmem⟩ := Finset.card_pos.mp (hne γ₁ h₁ : 0 < γ₁.vertices.card)
  exact absurd hvmem (Finset.disjoint_left.mp hdis hvmem)

/-- The aggregate internal edges of the forgotten forest are the forgotten aggregate internal edges. -/
theorem fgInternalEdgesMap {D : DivergenceMeasureFamily} {G : ResolvedFeynmanGraph}
    (A : @ResolvedAdmissibleSubgraph D G) (hne : A.HasNonemptyComponents) :
    A.forget.internalEdges = A.internalEdges.map ResolvedFeynmanEdge.forget := by
  letI : (H : FeynmanGraph) → DivergenceMeasure H := D
  show (∑ δ ∈ A.forget.elements, δ.internalEdges)
      = (∑ γ ∈ A.elements, γ.internalEdges).map ResolvedFeynmanEdge.forget
  rw [ResolvedAdmissibleSubgraph.forget_elements,
    Finset.sum_image (fun γ₁ h₁ γ₂ h₂ h => fgInjOn A hne h₁ h₂ h), fgMapSum]
  exact Finset.sum_congr rfl (fun γ _ => ResolvedFeynmanSubgraph.forget_internalEdges γ)

/-- The aggregate internal edges are bounded by the ambient's. -/
theorem fgIntEdgesLe {D : DivergenceMeasureFamily} {G : ResolvedFeynmanGraph}
    (A : @ResolvedAdmissibleSubgraph D G) : A.internalEdges ≤ G.internalEdges := by
  letI : (H : FeynmanGraph) → DivergenceMeasure H := D
  classical
  rw [Multiset.le_iff_count]
  intro e
  have hcount : (∑ γ ∈ A.elements, γ.internalEdges).count e
      = ∑ γ ∈ A.elements, (γ.internalEdges).count e := by
    induction A.elements using Finset.induction_on with
    | empty => simp
    | insert a t ha ih => rw [Finset.sum_insert ha, Multiset.count_add, ih, Finset.sum_insert ha]
  show (∑ γ ∈ A.elements, γ.internalEdges).count e ≤ G.internalEdges.count e
  rw [hcount]
  by_cases heA : ∃ γ ∈ A.elements, e ∈ γ.internalEdges
  · obtain ⟨γ, hγ, heγ⟩ := heA
    have hzero : ∀ δ ∈ A.elements, δ ≠ γ → δ.internalEdges.count e = 0 := by
      intro δ hδ hne
      by_cases heδ : e ∈ δ.internalEdges
      · have hdisj : _root_.Disjoint δ.vertices γ.vertices := A.pairwiseDisjoint hδ hγ hne
        obtain ⟨hsδ, _⟩ := δ.edges_supported e heδ
        obtain ⟨hsγ, _⟩ := γ.edges_supported e heγ
        exact absurd hsγ (Finset.disjoint_left.mp hdisj hsδ)
      · exact Multiset.count_eq_zero.mpr heδ
    rw [Finset.sum_eq_single γ (fun δ hδ hne => hzero δ hδ hne) (fun hγnot => absurd hγ hγnot)]
    exact Multiset.count_le_of_le e γ.internalEdges_le
  · push_neg at heA
    have hz : ∑ γ ∈ A.elements, (γ.internalEdges).count e = 0 :=
      Finset.sum_eq_zero (fun γ hγ => Multiset.count_eq_zero.mpr (heA γ hγ))
    rw [hz]; exact Nat.zero_le _

/-- Forgetting preserves pairwise disjointness. -/
theorem fgPairwiseDisjoint {D : DivergenceMeasureFamily} {G : ResolvedFeynmanGraph}
    (A : @ResolvedAdmissibleSubgraph D G) : A.forget.IsPairwiseDisjoint := by
  letI : (H : FeynmanGraph) → DivergenceMeasure H := D
  intro δ₁ hδ₁ δ₂ hδ₂ hne12
  have hδ₁' : δ₁ ∈ A.elements.image ResolvedFeynmanSubgraph.forget := by
    rw [← ResolvedAdmissibleSubgraph.forget_elements]; exact hδ₁
  have hδ₂' : δ₂ ∈ A.elements.image ResolvedFeynmanSubgraph.forget := by
    rw [← ResolvedAdmissibleSubgraph.forget_elements]; exact hδ₂
  obtain ⟨γ₁, hγ₁, rfl⟩ := Finset.mem_image.mp hδ₁'
  obtain ⟨γ₂, hγ₂, rfl⟩ := Finset.mem_image.mp hδ₂'
  have hγ : γ₁ ≠ γ₂ := fun h => hne12 (by rw [h])
  exact (ResolvedFeynmanSubgraph.forget_disjoint_iff).mpr (A.pairwiseDisjoint hγ₁ hγ₂ hγ)

/-- Forgetting preserves forest nonemptiness. -/
theorem fgNonempty {D : DivergenceMeasureFamily} {G : ResolvedFeynmanGraph}
    (A : @ResolvedAdmissibleSubgraph D G) (h : A.IsNonempty) : A.forget.IsNonempty := by
  letI : (H : FeynmanGraph) → DivergenceMeasure H := D
  show (A.forget.elements).Nonempty
  rw [ResolvedAdmissibleSubgraph.forget_elements]
  exact h.image _

/-- Forgetting preserves componentwise nonemptiness. -/
theorem fgNonemptyComp {D : DivergenceMeasureFamily} {G : ResolvedFeynmanGraph}
    (A : @ResolvedAdmissibleSubgraph D G) (h : A.HasNonemptyComponents) :
    A.forget.HasNonemptyComponents := by
  letI : (H : FeynmanGraph) → DivergenceMeasure H := D
  intro δ hδ
  rw [ResolvedAdmissibleSubgraph.forget_elements] at hδ
  obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hδ
  have hγne : γ.IsNonempty := h γ hγ
  simpa [FeynmanSubgraph.IsNonempty, FeynmanSubgraph.vertexCount,
    ResolvedFeynmanSubgraph.IsNonempty, ResolvedFeynmanSubgraph.vertexCount] using hγne

/-- Forgetting preserves componentwise positive internal-edge count. -/
theorem fgPosIntComp {D : DivergenceMeasureFamily} {G : ResolvedFeynmanGraph}
    (A : @ResolvedAdmissibleSubgraph D G) (h : A.HasPositiveInternalEdgesComponents) :
    A.forget.HasPositiveInternalEdgesComponents := by
  letI : (H : FeynmanGraph) → DivergenceMeasure H := D
  intro δ hδ
  rw [ResolvedAdmissibleSubgraph.forget_elements] at hδ
  obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hδ
  simpa [ResolvedFeynmanSubgraph.forget_internalEdges, Multiset.card_map] using h γ hγ

/-- **body-587 (Step 4a) — the resolved proper forest forgets to a flat proper-disjoint forest.** -/
theorem fgMem {D : DivergenceMeasureFamily} {G : ResolvedFeynmanGraph}
    (A : @ResolvedAdmissibleSubgraph D G) (hA : @ResolvedAdmissibleSubgraph.IsProperForest D G A) :
    A.forget ∈ G.forget.properDisjointAdmissibleDivergentSubgraphsFor D := by
  letI : (H : FeynmanGraph) → DivergenceMeasure H := D
  rw [G.forget.mem_properDisjointAdmissibleDivergentSubgraphsFor D]
  refine ⟨?_, fgNonemptyComp A hA.2.1, ?_, fgPosIntComp A hA.2.2.2.1⟩
  · rw [@FeynmanGraph.mem_nonemptyDisjointAdmissibleDivergentSubgraphs G.forget (D G.forget) _]
    refine ⟨?_, fgNonempty A hA.1⟩
    rw [@FeynmanGraph.mem_disjointAdmissibleDivergentSubgraphs G.forget (D G.forget) _]
    exact ⟨@FeynmanGraph.mem_admissibleDivergentSubgraphs G.forget (D G.forget) _ A.forget,
      fgPairwiseDisjoint A⟩
  · rw [fgInternalEdgesMap A hA.2.1, Multiset.card_map]; exact hA.2.2.1

/-! ## Step 4 — the clean lifted canonical star -/

/-- **body-587 (Step 4) — the flat canonical star of the forgotten forest**, keyed to `D`
(clean re-derivation of `flatCanonicalStar`, whose library form picks up forbidden classes). -/
noncomputable def cleanFlatStar (D : DivergenceMeasureFamily) {G : ResolvedFeynmanGraph}
    (A : @ResolvedAdmissibleSubgraph D G)
    (hA : @ResolvedAdmissibleSubgraph.IsProperForest D G A) :
    FeynmanSubgraph G.forget → VertexId :=
  letI : (H : FeynmanGraph) → DivergenceMeasure H := D
  FeynmanGraph.admissibleForestCanonicalStarOf G.forget A.forget (fgMem A hA)

/-- **body-587 (Step 4) — the lifted resolved canonical star** (the flat canonical star precomposed
with `forget`), keyed to `D` (clean re-derivation of `canonicalStarOfViaForget`). -/
noncomputable def cleanStarOf (D : DivergenceMeasureFamily) {G : ResolvedFeynmanGraph}
    (A : @ResolvedAdmissibleSubgraph D G)
    (hA : @ResolvedAdmissibleSubgraph.IsProperForest D G A) :
    ResolvedFeynmanSubgraph G → VertexId :=
  fun γ => cleanFlatStar D A hA γ.forget

/-- The total star assignment used by the supply (canonical on proper forests, junk elsewhere). -/
noncomputable def cleanStarOfTotal (D : DivergenceMeasureFamily) (G : ResolvedFeynmanGraph)
    (A : @ResolvedAdmissibleSubgraph D G) : ResolvedFeynmanSubgraph G → VertexId :=
  if h : @ResolvedAdmissibleSubgraph.IsProperForest D G A then cleanStarOf D A h else fun _ => 0

/-! ## Step 5 — the resolved↔flat contraction-forget bridge + `hCD` -/

/-- Complement edges commute with `forget` (bounded multiset map-subtraction). -/
theorem forget_complementEdges_eq_clean {D : DivergenceMeasureFamily} {G : ResolvedFeynmanGraph}
    (A : @ResolvedAdmissibleSubgraph D G) (hne : A.HasNonemptyComponents) :
    A.forget.complementEdges = A.complementEdges.map ResolvedFeynmanEdge.forget := by
  letI : (H : FeynmanGraph) → DivergenceMeasure H := D
  rw [AdmissibleSubgraph.complementEdges, ResolvedAdmissibleSubgraph.complementEdges,
    fgInternalEdgesMap A hne, multiset_map_sub_of_le ResolvedFeynmanEdge.forget (fgIntEdgesLe A)]
  rfl

/-- The retarget maps agree, for any compatible flat/resolved star pair. -/
theorem retargetVertex_forget_eq_gen {D : DivergenceMeasureFamily} {G : ResolvedFeynmanGraph}
    (A : @ResolvedAdmissibleSubgraph D G)
    (s : FeynmanSubgraph G.forget → VertexId) (r : ResolvedFeynmanSubgraph G → VertexId)
    (hcompat : ∀ γ ∈ A.elements, s γ.forget = r γ) (v : VertexId) :
    A.forget.retargetVertex s v = A.retargetVertex r v := by
  letI : (H : FeynmanGraph) → DivergenceMeasure H := D
  by_cases hv : v ∈ A.vertices
  · have hv' : v ∈ A.forget.vertices := by rw [fgVerticesEq]; exact hv
    rw [ResolvedAdmissibleSubgraph.retargetVertex,
        ResolvedAdmissibleSubgraph.componentAt?_of_mem _ hv,
        AdmissibleSubgraph.retargetVertex, AdmissibleSubgraph.componentAt?_of_mem _ hv']
    have hcomp : A.forget.componentAt hv' = (A.componentAt hv).forget := by
      apply AdmissibleSubgraph.componentAt_eq_of_mem_vertices (fgPairwiseDisjoint A)
        (Finset.mem_image_of_mem _ (A.componentAt_mem hv))
      rw [ResolvedFeynmanSubgraph.forget_vertices]; exact A.componentAt_vertex_mem hv
    show s (A.forget.componentAt hv') = r (A.componentAt hv)
    rw [hcomp]; exact hcompat (A.componentAt hv) (A.componentAt_mem hv)
  · have hv' : v ∉ A.forget.vertices := by rw [fgVerticesEq]; exact hv
    rw [ResolvedAdmissibleSubgraph.retargetVertex_of_not_mem _ _ hv,
        AdmissibleSubgraph.retargetVertex_of_not_mem _ _ hv']

/-- The star-vertex sets agree, for any compatible star pair. -/
theorem starVertices_forget_eq_gen {D : DivergenceMeasureFamily} {G : ResolvedFeynmanGraph}
    (A : @ResolvedAdmissibleSubgraph D G)
    (s : FeynmanSubgraph G.forget → VertexId) (r : ResolvedFeynmanSubgraph G → VertexId)
    (hcompat : ∀ γ ∈ A.elements, s γ.forget = r γ) :
    A.forget.starVertices s = A.starVertices r := by
  letI : (H : FeynmanGraph) → DivergenceMeasure H := D
  unfold AdmissibleSubgraph.starVertices ResolvedAdmissibleSubgraph.starVertices
  rw [ResolvedAdmissibleSubgraph.forget_elements, Finset.image_image]
  exact Finset.image_congr (fun γ hγ => hcompat γ hγ)

/-- **body-587 (Step 5) — forgetting the resolved lifted-canonical-star contraction is the FLAT
canonical-star contraction of the forgotten forest** (clean re-derivation of
`forget_contractWithStars_resolvedStar`, for the lifted star pair). -/
theorem forget_contractWithStars_cleanStar {D : DivergenceMeasureFamily} {G : ResolvedFeynmanGraph}
    (A : @ResolvedAdmissibleSubgraph D G)
    (hpf : @ResolvedAdmissibleSubgraph.IsProperForest D G A) :
    (A.contractWithStars (cleanStarOf D A hpf)).forget
      = A.forget.contractWithStars (cleanFlatStar D A hpf) := by
  letI : (H : FeynmanGraph) → DivergenceMeasure H := D
  have hcompat : ∀ γ ∈ A.elements, cleanFlatStar D A hpf γ.forget = cleanStarOf D A hpf γ :=
    fun γ _ => rfl
  rw [ResolvedAdmissibleSubgraph.forget_contractWithStars]
  have hv : (G.vertices \ A.vertices) ∪ A.starVertices (cleanStarOf D A hpf)
      = (G.forget.vertices \ A.forget.vertices) ∪ A.forget.starVertices (cleanFlatStar D A hpf) := by
    rw [fgVerticesEq, starVertices_forget_eq_gen A _ _ hcompat]
    rfl
  have hi : (A.complementEdges.map ResolvedFeynmanEdge.forget).map
        (fun e => ({ source := A.retargetVertex (cleanStarOf D A hpf) e.source,
                     target := A.retargetVertex (cleanStarOf D A hpf) e.target,
                     sector := e.sector } : FeynmanEdge))
      = A.forget.complementEdges.map (A.forget.retargetEdge (cleanFlatStar D A hpf)) := by
    rw [forget_complementEdges_eq_clean A hpf.2.1]
    simp only [Multiset.map_map]
    refine Multiset.map_congr rfl (fun e _ => ?_)
    simp only [Function.comp_apply, AdmissibleSubgraph.retargetEdge, ResolvedFeynmanEdge.forget,
      retargetVertex_forget_eq_gen A _ _ hcompat]
  have he : (G.externalLegs.map ResolvedExternalLeg.forget).map
        (fun l => ({ attachedTo := A.retargetVertex (cleanStarOf D A hpf) l.attachedTo,
                     sector := l.sector } : ExternalLeg))
      = G.forget.externalLegs.map (A.forget.retargetExternalLeg (cleanFlatStar D A hpf)) := by
    rw [show G.forget.externalLegs = G.externalLegs.map ResolvedExternalLeg.forget from rfl]
    simp only [Multiset.map_map]
    refine Multiset.map_congr rfl (fun l _ => ?_)
    simp only [Function.comp_apply, AdmissibleSubgraph.retargetExternalLeg,
      ResolvedExternalLeg.forget, retargetVertex_forget_eq_gen A _ _ hcompat]
  exact congr (congr (congrArg FeynmanGraph.mk hv) hi) he

/-- **body-587 (Step 5, THE MOUNTAIN) — the load-bearing `hCD`.**  On a W″ index member the lifted
canonical-star contraction is family-connected-divergent: topology via the clean resolved↔flat
forget-contraction identity, numerical divergence via body-573's φ⁴ canonical-forest CD, glued by the
strict graph equality (NO strict star equality, NO star-renaming permutation). -/
theorem resolvedWDoublePrimeContract_hCD (G : ResolvedFeynmanGraph)
    (A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G)
    (hpf : @ResolvedAdmissibleSubgraph.IsProperForest phi4DivergenceMeasureFamily G A)
    (hcdAmbient : ResolvedFeynmanGraphClass.IsConnectedDivergentFor phi4DivergenceMeasureFamily
      phi4PermInvariantDivergenceMeasureFamily G.toResolvedClass) :
    ResolvedFeynmanGraphClass.IsConnectedDivergentFor phi4DivergenceMeasureFamily
      phi4PermInvariantDivergenceMeasureFamily
      (@ResolvedAdmissibleSubgraph.contractWithStars phi4DivergenceMeasureFamily G A
        (cleanStarOf phi4DivergenceMeasureFamily A hpf)).toResolvedClass := by
  letI : (H : FeynmanGraph) → DivergenceMeasure H := phi4DivergenceMeasureFamily
  rw [ResolvedFeynmanGraphClass.isConnectedDivergentFor_toResolvedClass] at hcdAmbient ⊢
  obtain ⟨hGWF, hGself⟩ := hcdAmbient
  have hAf : A.forget ∈ G.forget.properDisjointAdmissibleDivergentSubgraphsFor
      phi4DivergenceMeasureFamily := fgMem A hpf
  have hEq : (A.contractWithStars (cleanStarOf phi4DivergenceMeasureFamily A hpf)).forget
      = phi4CanonicalForestContractGraph G.forget A.forget hAf := by
    rw [forget_contractWithStars_cleanStar, phi4CanonicalForestContractGraph_eq_contractWithStars]
    congr 1
  obtain ⟨hQWF, hQcd⟩ :=
    phi4CanonicalForestContractGraph_exists_self_isConnectedDivergent hGWF hGself.isOnePI
      hGself.isDivergent A.forget hAf
  rw [hEq]
  exact ⟨hQWF, hQcd⟩

/-! ## Step 6 — the concrete φ⁴ supply -/

/-- The φ⁴ W″ per-graph index payload (named so `(index G).carrier` reduces in `hCD`). -/
noncomputable def phi4WDoublePrimeIndexData (G : ResolvedFeynmanGraph) :
    @ResolvedProperForestFiniteIndex phi4DivergenceMeasureFamily G := by
  letI : (H : FeynmanGraph) → DivergenceMeasure H := phi4DivergenceMeasureFamily
  exact { carrier := resolvedLegSaturatedIndexFor phi4DivergenceMeasureFamily
            phi4PermInvariantDivergenceMeasureFamily G,
          mem_proper := fun A hA => ((mem_resolvedLegSaturatedIndexFor phi4DivergenceMeasureFamily
            phi4PermInvariantDivergenceMeasureFamily G A).mp hA).2.2.2.2.1 }

/-- **body-587 ∎ — the φ⁴ W″ raw canonical supply.**  Index = the family-indexed W″ finite index
(body-586), star = the lifted canonical star (total via `dite`), `hCD` = Step 5, `carrier_mapPerm` =
Step 3.  A body-413-equivalent `rightTerm`-free RAW supply, fully family-keyed and axiom-clean. -/
noncomputable def phi4WDoublePrimeRawCanonicalSupply :
    ResolvedCanonicalCarrierProperRawSupplyFor phi4DivergenceMeasureFamily
      phi4PermInvariantDivergenceMeasureFamily where
  index := phi4WDoublePrimeIndexData
  starOf := fun G A => cleanStarOfTotal phi4DivergenceMeasureFamily G A
  hCD := by
    intro G A hA
    have hA' : A ∈ resolvedLegSaturatedIndexFor phi4DivergenceMeasureFamily
        phi4PermInvariantDivergenceMeasureFamily G := hA
    obtain ⟨_, hcd, _, _, hpf, _⟩ := (mem_resolvedLegSaturatedIndexFor phi4DivergenceMeasureFamily
      phi4PermInvariantDivergenceMeasureFamily G A).mp hA'
    have hstar : cleanStarOfTotal phi4DivergenceMeasureFamily G A
        = cleanStarOf phi4DivergenceMeasureFamily A hpf := by
      unfold cleanStarOfTotal; rw [dif_pos hpf]
    rw [hstar]
    exact resolvedWDoublePrimeContract_hCD G A hpf hcd
  carrier_mapPerm := fun G σ =>
    resolvedLegSaturatedIndexFor_mapPerm phi4DivergenceMeasureFamily
      phi4PermInvariantDivergenceMeasureFamily (G := G) σ

end GaugeGeometry.QFT.Combinatorial
