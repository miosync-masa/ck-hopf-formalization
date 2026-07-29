import GaugeGeometry.QFT.HopfAlgebra.Phi4WDoublePrimeRawSupply
import GaugeGeometry.QFT.HopfAlgebra.Phi4ResolvedHopfCarrier

/-!
# QFT-R1-body-588 — family-native W″ right term + full carrier data

Body-587 assembled the `rightTerm`-free RAW family supply
(`ResolvedCanonicalCarrierProperRawSupplyFor` / `phi4WDoublePrimeRawCanonicalSupply`).  This body
adds the **resolved family right term** `resolvedForestRightTermFor` and its rename-invariance
`rightTerm_mapPerm`, giving the FULL family W″ CARRIER data
(`ResolvedCanonicalCarrierProperSupplyFor` / `phi4WDoublePrimeCanonicalSupply`).

## The boundary

A full **carrier** supply is completeable now; a full **coproduct** supply is NOT (that needs the
resolved boundary completion for the LEFT component, body-589+).  So this body builds ONLY the right
factor: the full contracted graph → a direct resolved generator, plus `rightTerm_mapPerm`.  No left
forest term, no resolved boundary completion, no coproduct / aeval / coassoc, no Measure / E / rep*.

## Step 3/4 — body-580 transplanted to the resolved world

The rename-invariance is body-580 (`phi4CanonicalForestContractGraph_mapPerm_toClass_eq`), transplanted
to resolved graphs / forests / edges (which PRESERVE `edgeId`/`legId`).  The strict labeled contracted
graphs are **not** equal — the two canonical fresh stars are chosen independently — so a **correcting
permutation** `τ = ρ · σ` absorbs the star mismatch: `ρ` fixes every visible vertex of `G.mapPerm σ`
and sends each `σ`-image of a source star to the matching target star.  The two action laws promote to
the whole-graph equality `Qσ = Q.mapPerm τ`, whence equal resolved classes.

Per the HALT: NO strict cross-presentation star equality `targetStar (mapPerm γ) = σ (sourceStar γ)`
is ever proved or stated — the whole construction routes through `ρ`; no cast / equality to the old
`ResolvedCanonicalCarrierProperSupply` / old `ResolvedHopfGen` / `ResolvedHopfH`; no left term /
boundary completion / coproduct / aeval / coassoc / Measure / E / rep*; exactly ONE new `structure`
(Step 6); zero forbidden divergence classes in any declaration's type; no `variable [`.  The
correcting-permutation engine `finite_visible_star_permutation` is re-derived verbatim (Mathlib-only
finite-support extension; consumes no divergence class).
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

/-! ## Step 1 — the family resolved right term -/

/-- **body-588 (Step 1) — the family-native forest right term.**  The single generator of the
star-contraction `A.contractWithStars starOf` (one connected-divergent resolved graph), read as the
family-indexed resolved generator (body-584).  No old `ResolvedHopfGen` / `ResolvedHopfH`. -/
noncomputable def resolvedForestRightTermFor
    (D : DivergenceMeasureFamily) (Inv : PermInvariantDivergenceMeasureFamily D)
    {G : ResolvedFeynmanGraph} (A : @ResolvedAdmissibleSubgraph D G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId)
    (hCD : ResolvedFeynmanGraphClass.IsConnectedDivergentFor D Inv
      (A.contractWithStars starOf).toResolvedClass) :
    ResolvedHopfHFor D Inv :=
  MvPolynomial.X ((A.contractWithStars starOf).toResolvedHopfGenFor D Inv
    ((ResolvedFeynmanGraphClass.isConnectedDivergentFor_toResolvedClass D Inv
      (A.contractWithStars starOf)).mp hCD))

/-- **body-588 (Step 1 anchor) — the right term depends only on the contracted resolved class.**
Equal contracted classes give equal right terms (the CD witnesses enter proof-irrelevantly). -/
theorem resolvedForestRightTermFor_class_eq
    (D : DivergenceMeasureFamily) (Inv : PermInvariantDivergenceMeasureFamily D)
    {G₁ G₂ : ResolvedFeynmanGraph}
    (A₁ : @ResolvedAdmissibleSubgraph D G₁) (A₂ : @ResolvedAdmissibleSubgraph D G₂)
    (s₁ : ResolvedFeynmanSubgraph G₁ → VertexId) (s₂ : ResolvedFeynmanSubgraph G₂ → VertexId)
    (hCD₁ : ResolvedFeynmanGraphClass.IsConnectedDivergentFor D Inv
      (A₁.contractWithStars s₁).toResolvedClass)
    (hCD₂ : ResolvedFeynmanGraphClass.IsConnectedDivergentFor D Inv
      (A₂.contractWithStars s₂).toResolvedClass)
    (hcls : (A₁.contractWithStars s₁).toResolvedClass = (A₂.contractWithStars s₂).toResolvedClass) :
    resolvedForestRightTermFor D Inv A₁ s₁ hCD₁ = resolvedForestRightTermFor D Inv A₂ s₂ hCD₂ := by
  unfold resolvedForestRightTermFor
  refine congrArg MvPolynomial.X (Subtype.ext ?_)
  rw [ResolvedFeynmanGraph.toResolvedHopfGenFor_val, ResolvedFeynmanGraph.toResolvedHopfGenFor_val]
  exact hcls

/-! ## Step 2 — lifted canonical star facts (freshness + injectivity, thin) -/

/-- **body-588 (Step 2) — the lifted canonical star is fresh** (its value on any component lies
outside the ambient vertex set), via the flat canonical star's freshness on `G.forget`. -/
theorem cleanStarOf_not_mem_vertices
    {D : DivergenceMeasureFamily} {G : ResolvedFeynmanGraph}
    (A : @ResolvedAdmissibleSubgraph D G)
    (hpf : @ResolvedAdmissibleSubgraph.IsProperForest D G A)
    {γ : ResolvedFeynmanSubgraph G} (hγ : γ ∈ A.elements) :
    cleanStarOf D A hpf γ ∉ G.vertices := by
  letI : (H : FeynmanGraph) → DivergenceMeasure H := D
  have h : cleanStarOf D A hpf γ = A.forget.componentFreshStar γ.forget := rfl
  rw [h]
  have hn := AdmissibleSubgraph.componentFreshStar_not_mem_vertices A.forget γ.forget
  rwa [ResolvedFeynmanGraph.forget_vertices] at hn

/-- **body-588 (Step 2) — the lifted canonical star is injective on the forest's components.**
Injectivity of the flat canonical star on `A.forget.elements`, plus `fgInjOn`. -/
theorem cleanStarOf_injOn
    {D : DivergenceMeasureFamily} {G : ResolvedFeynmanGraph}
    (A : @ResolvedAdmissibleSubgraph D G)
    (hpf : @ResolvedAdmissibleSubgraph.IsProperForest D G A)
    {γ₁ : ResolvedFeynmanSubgraph G} (hγ₁ : γ₁ ∈ A.elements)
    {γ₂ : ResolvedFeynmanSubgraph G} (hγ₂ : γ₂ ∈ A.elements)
    (h : cleanStarOf D A hpf γ₁ = cleanStarOf D A hpf γ₂) : γ₁ = γ₂ := by
  letI : (H : FeynmanGraph) → DivergenceMeasure H := D
  have h₁ : cleanStarOf D A hpf γ₁ = A.forget.componentFreshStar γ₁.forget := rfl
  have h₂ : cleanStarOf D A hpf γ₂ = A.forget.componentFreshStar γ₂.forget := rfl
  rw [h₁, h₂] at h
  have hmem₁ : γ₁.forget ∈ A.forget.elements := by
    rw [ResolvedAdmissibleSubgraph.forget_elements]; exact Finset.mem_image_of_mem _ hγ₁
  have hfg : γ₁.forget = γ₂.forget :=
    AdmissibleSubgraph.componentFreshStar_eq_of_eq hmem₁ h
  exact fgInjOn A hpf.2.1 hγ₁ hγ₂ hfg

/-! ## Step 3 — the correcting-permutation engine (Mathlib-only finite-support extension) -/

/-- A finite partial vertex relabeling can be extended to a permutation of `VertexId`: fix the finite
set `S` and send the finite injective family `src` to the finite injective family `dst`, provided both
families are disjoint from `S`.  Re-derived verbatim from `Phi4ForestQuotientRename.lean` (whose copy
is `private`); uses only Mathlib primitives — no divergence class. -/
private theorem finite_visible_star_permutation
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset VertexId) (src dst : ι → VertexId)
    (hsrcInj : Function.Injective src)
    (hdstInj : Function.Injective dst)
    (hsrcS : ∀ i, src i ∉ S)
    (hdstS : ∀ i, dst i ∉ S) :
    ∃ τ : Equiv.Perm VertexId,
      (∀ v, v ∈ S → τ v = v) ∧
      ∀ i, τ (src i) = dst i := by
  classical
  let srcSet : Finset VertexId := Finset.univ.image src
  let dstSet : Finset VertexId := Finset.univ.image dst
  let support : Finset VertexId := S ∪ srcSet ∪ dstSet
  let p : {x // x ∈ support} → VertexId := fun x =>
    if h : ∃ i, src i = x.1 then dst h.choose else x.1
  let domain : Finset {x // x ∈ support} :=
    Finset.univ.filter (fun x : {x // x ∈ support} =>
      x.1 ∈ S ∨ ∃ i, src i = x.1)
  have hcard : Fintype.card {x // x ∈ support} = support.card :=
    Fintype.card_coe support
  have hp_subset : Finset.image p domain ⊆ support := by
    intro y hy
    rw [Finset.mem_image] at hy
    rcases hy with ⟨x, hx, rfl⟩
    dsimp [p]
    split
    · rename_i hsrc
      simp [support, dstSet]
    · exact x.2
  have hp_inj : Set.InjOn p (domain : Set {x // x ∈ support}) := by
    intro x hx y hy hxy
    have hx' : x.1 ∈ S ∨ ∃ i, src i = x.1 := by
      simpa [domain] using hx
    have hy' : y.1 ∈ S ∨ ∃ i, src i = y.1 := by
      simpa [domain] using hy
    rcases hx' with hxS | hxsrc
    · rcases hy' with hyS | hysrc
      · dsimp [p] at hxy
        have hxNotSrc : ¬ ∃ i, src i = x.1 := by
          rintro ⟨i, hi⟩
          exact hsrcS i (hi ▸ hxS)
        have hyNotSrc : ¬ ∃ i, src i = y.1 := by
          rintro ⟨i, hi⟩
          exact hsrcS i (hi ▸ hyS)
        simp [hxNotSrc, hyNotSrc] at hxy
        exact hxy
      · dsimp [p] at hxy
        have hxNotSrc : ¬ ∃ i, src i = x.1 := by
          rintro ⟨i, hi⟩
          exact hsrcS i (hi ▸ hxS)
        simp [hxNotSrc, hysrc] at hxy
        exact False.elim (hdstS hysrc.choose (hxy ▸ hxS))
    · rcases hy' with hyS | hysrc
      · dsimp [p] at hxy
        have hyNotSrc : ¬ ∃ i, src i = y.1 := by
          rintro ⟨i, hi⟩
          exact hsrcS i (hi ▸ hyS)
        simp [hxsrc, hyNotSrc] at hxy
        exact False.elim (hdstS hxsrc.choose (hxy.symm ▸ hyS))
      · dsimp [p] at hxy
        simp [hxsrc, hysrc] at hxy
        have hi :
            hxsrc.choose = hysrc.choose :=
          hdstInj hxy
        have hxval : x.1 = y.1 := by
          rw [← hxsrc.choose_spec, ← hysrc.choose_spec, hi]
        exact Subtype.ext hxval
  obtain ⟨σ, hσ⟩ :=
    Finset.exists_equiv_extend_of_card_eq hcard hp_subset hp_inj
  let τ : Equiv.Perm VertexId :=
    Equiv.Perm.extendDomain σ (Finset.equivToSet support)
  refine ⟨τ, ?_, ?_⟩
  · intro v hvS
    have hvSupport : v ∈ support := by
      simp [support, hvS]
    have hvDomain : (⟨v, hvSupport⟩ : {x // x ∈ support}) ∈ domain := by
      dsimp [domain]
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, Or.inl hvS⟩
    have hpv : p ⟨v, hvSupport⟩ = v := by
      dsimp [p]
      have hvNotSrc : ¬ ∃ i, src i = v := by
        rintro ⟨i, hi⟩
        exact hsrcS i (hi ▸ hvS)
      simp [hvNotSrc]
    have hσv : (σ ⟨v, hvSupport⟩ : VertexId) = v := by
      simpa [hpv] using hσ ⟨v, hvSupport⟩ hvDomain
    have hτ :
        τ ((Finset.equivToSet support) ⟨v, hvSupport⟩) =
          (Finset.equivToSet support) (σ ⟨v, hvSupport⟩) :=
      Equiv.Perm.extendDomain_apply_image σ
        (Finset.equivToSet support) ⟨v, hvSupport⟩
    change τ v = (σ ⟨v, hvSupport⟩ : VertexId) at hτ
    exact hτ.trans hσv
  · intro i
    have hsrcSupport : src i ∈ support := by
      simp [support, srcSet]
    have hsrcDomain :
        (⟨src i, hsrcSupport⟩ : {x // x ∈ support}) ∈ domain := by
      dsimp [domain]
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, Or.inr ⟨i, rfl⟩⟩
    have hp_src : p ⟨src i, hsrcSupport⟩ = dst i := by
      dsimp [p]
      split
      · rename_i h
        have hi : h.choose = i :=
          hsrcInj h.choose_spec
        exact congrArg dst hi
      · rename_i h
        exact False.elim (h ⟨i, rfl⟩)
    have hσsrc : (σ ⟨src i, hsrcSupport⟩ : VertexId) = dst i := by
      simpa [hp_src] using hσ ⟨src i, hsrcSupport⟩ hsrcDomain
    have hτ :
        τ ((Finset.equivToSet support) ⟨src i, hsrcSupport⟩) =
          (Finset.equivToSet support) (σ ⟨src i, hsrcSupport⟩) :=
      Equiv.Perm.extendDomain_apply_image σ
        (Finset.equivToSet support) ⟨src i, hsrcSupport⟩
    change τ (src i) = (σ ⟨src i, hsrcSupport⟩ : VertexId) at hτ
    exact hτ.trans hσsrc

/-! ## Step 3b — resolved component-retarget computation (clean re-derivations) -/

/-- The chosen component of a resolved forest at a carrier vertex is the unique component containing
it (from the structural pairwise-disjointness field). -/
theorem resolved_componentAt_eq
    {D : DivergenceMeasureFamily} {G : ResolvedFeynmanGraph}
    (A : @ResolvedAdmissibleSubgraph D G) {v : VertexId} (hv : v ∈ A.vertices)
    {γ : ResolvedFeynmanSubgraph G} (hγ : γ ∈ A.elements) (hvγ : v ∈ γ.vertices) :
    A.componentAt hv = γ := by
  by_contra hne
  have hdisj : (A.componentAt hv).Disjoint γ := A.pairwiseDisjoint (A.componentAt_mem hv) hγ hne
  exact (Finset.disjoint_left.mp hdisj (A.componentAt_vertex_mem hv)) hvγ

/-- Resolved `retargetVertex` computes to the component's star on a component member. -/
theorem resolved_retargetVertex_of_mem_component
    {D : DivergenceMeasureFamily} {G : ResolvedFeynmanGraph}
    (A : @ResolvedAdmissibleSubgraph D G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId)
    {γ : ResolvedFeynmanSubgraph G} (hγ : γ ∈ A.elements)
    {v : VertexId} (hvγ : v ∈ γ.vertices) :
    A.retargetVertex starOf v = starOf γ := by
  have hv : v ∈ A.vertices := ResolvedAdmissibleSubgraph.mem_vertices.mpr ⟨γ, hγ, hvγ⟩
  rw [ResolvedAdmissibleSubgraph.retargetVertex, A.componentAt?_of_mem hv,
    resolved_componentAt_eq A hv hγ hvγ]

/-! ## Step 4 — the resolved W″ contraction class rename-invariance (body-580 transplant) -/

/-- **body-588 (Step 4, TARGET) — the resolved W″ star-contraction is rename-invariant up to
resolved class.**  Renaming the ambient by `σ` (transporting the forest by `mapPermResolvedAdmissible…`)
leaves the lifted-canonical-star contraction unchanged as a resolved class.  The strict contracted
graphs differ only in their canonical fresh stars; the correcting permutation `τ = ρ · σ` transports
one to the other, giving `Qσ = Q.mapPerm τ`, hence equal classes.  NO strict cross-presentation star
equality is used — `ρ` absorbs the star mismatch.  Resolved edges/legs preserve `edgeId`/`legId`, so
the id fields match automatically. -/
theorem resolvedWDoublePrimeContract_class_mapPerm
    (D : DivergenceMeasureFamily) (Inv : PermInvariantDivergenceMeasureFamily D)
    {G : ResolvedFeynmanGraph} (σ : Equiv.Perm VertexId)
    (A : @ResolvedAdmissibleSubgraph D G)
    (hpf : @ResolvedAdmissibleSubgraph.IsProperForest D G A)
    (hpfσ : @ResolvedAdmissibleSubgraph.IsProperForest D (G.mapPerm σ)
      (mapPermResolvedAdmissibleSubgraphFor D Inv (rfl : G.mapPerm σ = G.mapPerm σ) A))
    (hsupp : ResolvedAmbientSupported G) :
    ((mapPermResolvedAdmissibleSubgraphFor D Inv (rfl : G.mapPerm σ = G.mapPerm σ) A).contractWithStars
        (cleanStarOf D (mapPermResolvedAdmissibleSubgraphFor D Inv
          (rfl : G.mapPerm σ = G.mapPerm σ) A) hpfσ)).toResolvedClass
      = (A.contractWithStars (cleanStarOf D A hpf)).toResolvedClass := by
  classical
  set Aσ := mapPermResolvedAdmissibleSubgraphFor D Inv (rfl : G.mapPerm σ = G.mapPerm σ) A with hAσdef
  have hAσelem : Aσ.elements = A.elements.image (mapPermRFS (rfl : G.mapPerm σ = G.mapPerm σ)) := by
    rw [hAσdef]; exact mapPermResolvedAdmissibleSubgraphFor_elements D Inv _ A
  have hmapV : (G.mapPerm σ).vertices = G.vertices.image σ := rfl
  -- `Aσ.vertices = A.vertices.image σ`
  have hAσ_vertices : Aσ.vertices = A.vertices.image σ := by
    ext u
    rw [ResolvedAdmissibleSubgraph.mem_vertices, Finset.mem_image]
    constructor
    · rintro ⟨γ', hγ', huγ'⟩
      rw [hAσelem] at hγ'
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hγ'
      rw [mapPermRFS_vertices] at huγ'
      obtain ⟨w, hwγ, rfl⟩ := Finset.mem_image.mp huγ'
      exact ⟨w, ResolvedAdmissibleSubgraph.mem_vertices.mpr ⟨γ, hγ, hwγ⟩, rfl⟩
    · rintro ⟨w, hwA, rfl⟩
      obtain ⟨γ, hγ, hwγ⟩ := ResolvedAdmissibleSubgraph.mem_vertices.mp hwA
      refine ⟨mapPermRFS (rfl : G.mapPerm σ = G.mapPerm σ) γ, ?_, ?_⟩
      · rw [hAσelem]; exact Finset.mem_image.mpr ⟨γ, hγ, rfl⟩
      · rw [mapPermRFS_vertices]; exact Finset.mem_image_of_mem σ hwγ
  -- ==== Step A : the correcting permutation τ = ρ · σ ====
  have hsrcInj : Function.Injective
      (fun γ : {x // x ∈ A.elements} => σ (cleanStarOf D A hpf γ.1)) := by
    intro γ₁ γ₂ h
    have hstar : cleanStarOf D A hpf γ₁.1 = cleanStarOf D A hpf γ₂.1 := σ.injective h
    exact Subtype.ext (cleanStarOf_injOn A hpf γ₁.2 γ₂.2 hstar)
  have hdstInj : Function.Injective
      (fun γ : {x // x ∈ A.elements} =>
        cleanStarOf D Aσ hpfσ (mapPermRFS (rfl : G.mapPerm σ = G.mapPerm σ) γ.1)) := by
    intro γ₁ γ₂ h
    have hm₁ : mapPermRFS (rfl : G.mapPerm σ = G.mapPerm σ) γ₁.1 ∈ Aσ.elements := by
      rw [hAσelem]; exact Finset.mem_image_of_mem _ γ₁.2
    have hm₂ : mapPermRFS (rfl : G.mapPerm σ = G.mapPerm σ) γ₂.1 ∈ Aσ.elements := by
      rw [hAσelem]; exact Finset.mem_image_of_mem _ γ₂.2
    have hmps : mapPermRFS (rfl : G.mapPerm σ = G.mapPerm σ) γ₁.1
              = mapPermRFS (rfl : G.mapPerm σ = G.mapPerm σ) γ₂.1 :=
      cleanStarOf_injOn Aσ hpfσ hm₁ hm₂ h
    exact Subtype.ext (mapPermRFS_injective (rfl : G.mapPerm σ = G.mapPerm σ) hmps)
  have hsrcS : ∀ γ : {x // x ∈ A.elements},
      σ (cleanStarOf D A hpf γ.1) ∉ (G.mapPerm σ).vertices := by
    intro γ hc
    have hc' : σ (cleanStarOf D A hpf γ.1) ∈ G.vertices.image σ := hc
    rw [σ.injective.mem_finset_image] at hc'
    exact cleanStarOf_not_mem_vertices A hpf γ.2 hc'
  have hdstS : ∀ γ : {x // x ∈ A.elements},
      cleanStarOf D Aσ hpfσ (mapPermRFS (rfl : G.mapPerm σ = G.mapPerm σ) γ.1)
        ∉ (G.mapPerm σ).vertices := by
    intro γ
    have hm : mapPermRFS (rfl : G.mapPerm σ = G.mapPerm σ) γ.1 ∈ Aσ.elements := by
      rw [hAσelem]; exact Finset.mem_image_of_mem _ γ.2
    exact cleanStarOf_not_mem_vertices Aσ hpfσ hm
  obtain ⟨ρ, hρfix, hρmap⟩ := finite_visible_star_permutation
    (ι := {x // x ∈ A.elements})
    (G.mapPerm σ).vertices
    (fun γ => σ (cleanStarOf D A hpf γ.1))
    (fun γ => cleanStarOf D Aσ hpfσ (mapPermRFS (rfl : G.mapPerm σ = G.mapPerm σ) γ.1))
    hsrcInj hdstInj hsrcS hdstS
  set τ : Equiv.Perm VertexId := ρ * σ with hτdef
  have hτ_ambient : ∀ v, v ∈ G.vertices → τ v = σ v := by
    intro v hv
    rw [hτdef, Equiv.Perm.mul_apply]
    exact hρfix (σ v) (Finset.mem_image_of_mem σ hv)
  have hτ_star : ∀ γ, γ ∈ A.elements →
      τ (cleanStarOf D A hpf γ)
        = cleanStarOf D Aσ hpfσ (mapPermRFS (rfl : G.mapPerm σ = G.mapPerm σ) γ) := by
    intro γ hγ
    rw [hτdef, Equiv.Perm.mul_apply]
    exact hρmap ⟨γ, hγ⟩
  -- ==== Step B : the retarget coordinate law ====
  have hcoord : ∀ v, v ∈ G.vertices →
      τ (A.retargetVertex (cleanStarOf D A hpf) v)
        = Aσ.retargetVertex (cleanStarOf D Aσ hpfσ) (σ v) := by
    intro v hvG
    by_cases hvA : v ∈ A.vertices
    · obtain ⟨γ, hγ, hvγ⟩ := ResolvedAdmissibleSubgraph.mem_vertices.mp hvA
      have hmpsγ : mapPermRFS (rfl : G.mapPerm σ = G.mapPerm σ) γ ∈ Aσ.elements := by
        rw [hAσelem]; exact Finset.mem_image_of_mem _ hγ
      have hσvγ : σ v ∈ (mapPermRFS (rfl : G.mapPerm σ = G.mapPerm σ) γ).vertices := by
        rw [mapPermRFS_vertices]; exact Finset.mem_image_of_mem σ hvγ
      rw [resolved_retargetVertex_of_mem_component A (cleanStarOf D A hpf) hγ hvγ,
        hτ_star γ hγ,
        resolved_retargetVertex_of_mem_component Aσ (cleanStarOf D Aσ hpfσ) hmpsγ hσvγ]
    · have hσvA : σ v ∉ Aσ.vertices := by
        rw [hAσ_vertices, σ.injective.mem_finset_image]; exact hvA
      rw [ResolvedAdmissibleSubgraph.retargetVertex_of_not_mem A (cleanStarOf D A hpf) hvA,
        hτ_ambient v hvG,
        ResolvedAdmissibleSubgraph.retargetVertex_of_not_mem Aσ (cleanStarOf D Aσ hpfσ) hσvA]
  -- ==== Step C : the three field equalities → Qσ = Q.mapPerm τ ====
  have hv : (Aσ.contractWithStars (cleanStarOf D Aσ hpfσ)).vertices
          = ((A.contractWithStars (cleanStarOf D A hpf)).mapPerm τ).vertices := by
    show (Aσ.contractWithStars (cleanStarOf D Aσ hpfσ)).vertices
        = ((A.contractWithStars (cleanStarOf D A hpf)).vertices).image τ
    rw [ResolvedAdmissibleSubgraph.contractWithStars_vertices,
        ResolvedAdmissibleSubgraph.contractWithStars_vertices, Finset.image_union]
    congr 1
    · have himg : (G.vertices \ A.vertices).image τ = (G.vertices \ A.vertices).image σ :=
        Finset.image_congr (fun w hw => hτ_ambient w (Finset.mem_sdiff.mp hw).1)
      rw [himg, Finset.image_sdiff G.vertices A.vertices σ.injective, hmapV, hAσ_vertices]
    · show Aσ.elements.image (cleanStarOf D Aσ hpfσ)
         = (A.elements.image (cleanStarOf D A hpf)).image τ
      rw [hAσelem, Finset.image_image, Finset.image_image]
      exact Finset.image_congr (fun γ hγ => (hτ_star γ hγ).symm)
  have hi : (Aσ.contractWithStars (cleanStarOf D Aσ hpfσ)).internalEdges
          = ((A.contractWithStars (cleanStarOf D A hpf)).mapPerm τ).internalEdges := by
    have hmapIE : ((A.contractWithStars (cleanStarOf D A hpf)).mapPerm τ).internalEdges
        = (A.contractWithStars (cleanStarOf D A hpf)).internalEdges.map (ResolvedFeynmanEdge.map τ) :=
      rfl
    rw [hmapIE, ResolvedAdmissibleSubgraph.contractWithStars_internalEdges,
        ResolvedAdmissibleSubgraph.contractWithStars_internalEdges,
        mpFor_complementEdges D Inv σ A, Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl (fun e he => ?_)
    have heG : e ∈ G.internalEdges :=
      Multiset.mem_of_le (Multiset.sub_le_self _ _) he
    obtain ⟨hs, ht⟩ := hsupp.1 e heG
    show ({ edgeId := e.edgeId,
            source := Aσ.retargetVertex (cleanStarOf D Aσ hpfσ) (σ e.source),
            target := Aσ.retargetVertex (cleanStarOf D Aσ hpfσ) (σ e.target),
            sector := e.sector } : ResolvedFeynmanEdge)
       = { edgeId := e.edgeId,
           source := τ (A.retargetVertex (cleanStarOf D A hpf) e.source),
           target := τ (A.retargetVertex (cleanStarOf D A hpf) e.target),
           sector := e.sector }
    rw [ResolvedFeynmanEdge.mk.injEq]
    exact ⟨rfl, (hcoord e.source hs).symm, (hcoord e.target ht).symm, rfl⟩
  have hlegs : (Aσ.contractWithStars (cleanStarOf D Aσ hpfσ)).externalLegs
          = ((A.contractWithStars (cleanStarOf D A hpf)).mapPerm τ).externalLegs := by
    have hmapEL : ((A.contractWithStars (cleanStarOf D A hpf)).mapPerm τ).externalLegs
        = (A.contractWithStars (cleanStarOf D A hpf)).externalLegs.map (ResolvedExternalLeg.map τ) :=
      rfl
    have hmapGL : (G.mapPerm σ).externalLegs = G.externalLegs.map (ResolvedExternalLeg.map σ) := rfl
    rw [hmapEL, ResolvedAdmissibleSubgraph.contractWithStars_externalLegs,
        ResolvedAdmissibleSubgraph.contractWithStars_externalLegs, hmapGL,
        Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl (fun ℓ hℓ => ?_)
    have hℓv : ℓ.attachedTo ∈ G.vertices := hsupp.2 ℓ hℓ
    show ({ legId := ℓ.legId,
            attachedTo := Aσ.retargetVertex (cleanStarOf D Aσ hpfσ) (σ ℓ.attachedTo),
            sector := ℓ.sector } : ResolvedExternalLeg)
       = { legId := ℓ.legId,
           attachedTo := τ (A.retargetVertex (cleanStarOf D A hpf) ℓ.attachedTo),
           sector := ℓ.sector }
    rw [ResolvedExternalLeg.mk.injEq]
    exact ⟨rfl, (hcoord ℓ.attachedTo hℓv).symm, rfl⟩
  have hτcontract : Aσ.contractWithStars (cleanStarOf D Aσ hpfσ)
          = (A.contractWithStars (cleanStarOf D A hpf)).mapPerm τ :=
    congr (congr (congrArg ResolvedFeynmanGraph.mk hv) hi) hlegs
  -- ==== Step D : equal resolved classes ====
  rw [hτcontract, ResolvedFeynmanGraph.toResolvedClass_mapPerm]

/-! ## Step 5 — the family right term is rename-invariant -/

/-- **body-588 (Step 5) — the resolved family right term is rename-invariant.**  Feed Step 4's
resolved-class equality into the Step 1 anchor (CD witnesses proof-irrelevant). -/
theorem resolvedForestRightTermFor_mapPerm
    (D : DivergenceMeasureFamily) (Inv : PermInvariantDivergenceMeasureFamily D)
    {G : ResolvedFeynmanGraph} (σ : Equiv.Perm VertexId)
    (A : @ResolvedAdmissibleSubgraph D G)
    (hpf : @ResolvedAdmissibleSubgraph.IsProperForest D G A)
    (hpfσ : @ResolvedAdmissibleSubgraph.IsProperForest D (G.mapPerm σ)
      (mapPermResolvedAdmissibleSubgraphFor D Inv (rfl : G.mapPerm σ = G.mapPerm σ) A))
    (hsupp : ResolvedAmbientSupported G)
    (hCD : ResolvedFeynmanGraphClass.IsConnectedDivergentFor D Inv
      (A.contractWithStars (cleanStarOf D A hpf)).toResolvedClass)
    (hCDσ : ResolvedFeynmanGraphClass.IsConnectedDivergentFor D Inv
      ((mapPermResolvedAdmissibleSubgraphFor D Inv (rfl : G.mapPerm σ = G.mapPerm σ) A).contractWithStars
        (cleanStarOf D (mapPermResolvedAdmissibleSubgraphFor D Inv
          (rfl : G.mapPerm σ = G.mapPerm σ) A) hpfσ)).toResolvedClass) :
    resolvedForestRightTermFor D Inv A (cleanStarOf D A hpf) hCD
      = resolvedForestRightTermFor D Inv
          (mapPermResolvedAdmissibleSubgraphFor D Inv (rfl : G.mapPerm σ = G.mapPerm σ) A)
          (cleanStarOf D (mapPermResolvedAdmissibleSubgraphFor D Inv
            (rfl : G.mapPerm σ = G.mapPerm σ) A) hpfσ) hCDσ :=
  resolvedForestRightTermFor_class_eq D Inv A _ _ _ hCD hCDσ
    (resolvedWDoublePrimeContract_class_mapPerm D Inv σ A hpf hpfσ hsupp).symm

/-! ## Step 6 — the full family carrier supply -/

/-- **body-588 (Step 6) — the FULL family-indexed proper-forest carrier supply.**  Extends the
body-587 RAW supply with the resolved family right term's rename-invariance `rightTerm_mapPerm`
(replacing the strict `star_mapPerm`; the correcting permutation absorbs the star mismatch).  A
CARRIER supply only — no left forest term / boundary completion / coproduct. -/
structure ResolvedCanonicalCarrierProperSupplyFor
    (D : DivergenceMeasureFamily) (Inv : PermInvariantDivergenceMeasureFamily D)
    extends ResolvedCanonicalCarrierProperRawSupplyFor D Inv where
  /-- The family forest right term is `mapPerm`-invariant (body-405 analogue, family-native). -/
  rightTerm_mapPerm : ∀ (G : ResolvedFeynmanGraph) (σ : Equiv.Perm VertexId)
    (A : @ResolvedAdmissibleSubgraph D G) (hA : A ∈ (index G).carrier)
    (hAσ : mapPermResolvedAdmissibleSubgraphFor D Inv (rfl : G.mapPerm σ = G.mapPerm σ) A
      ∈ (index (G.mapPerm σ)).carrier),
    resolvedForestRightTermFor D Inv A (starOf G A) (hCD G A hA)
      = resolvedForestRightTermFor D Inv
          (mapPermResolvedAdmissibleSubgraphFor D Inv (rfl : G.mapPerm σ = G.mapPerm σ) A)
          (starOf (G.mapPerm σ)
            (mapPermResolvedAdmissibleSubgraphFor D Inv (rfl : G.mapPerm σ = G.mapPerm σ) A))
          (hCD (G.mapPerm σ)
            (mapPermResolvedAdmissibleSubgraphFor D Inv (rfl : G.mapPerm σ = G.mapPerm σ) A) hAσ)

/-- **body-588 ∎ — the φ⁴ FULL W″ carrier supply.**  The body-587 RAW supply plus the family right
term's rename-invariance (Step 5), with `hpf` / `hpfσ` / `hsupp` recovered from W″ index membership. -/
noncomputable def phi4WDoublePrimeCanonicalSupply :
    ResolvedCanonicalCarrierProperSupplyFor phi4DivergenceMeasureFamily
      phi4PermInvariantDivergenceMeasureFamily :=
  { phi4WDoublePrimeRawCanonicalSupply with
    rightTerm_mapPerm := by
      intro G σ A hA hAσ
      letI : (H : FeynmanGraph) → DivergenceMeasure H := phi4DivergenceMeasureFamily
      have hA' : A ∈ resolvedLegSaturatedIndexFor phi4DivergenceMeasureFamily
          phi4PermInvariantDivergenceMeasureFamily G := hA
      obtain ⟨hsupp, _hcd, _he, _hl, hpf, _hsat⟩ :=
        (mem_resolvedLegSaturatedIndexFor phi4DivergenceMeasureFamily
          phi4PermInvariantDivergenceMeasureFamily G A).mp hA'
      set Aσ := mapPermResolvedAdmissibleSubgraphFor phi4DivergenceMeasureFamily
        phi4PermInvariantDivergenceMeasureFamily (rfl : G.mapPerm σ = G.mapPerm σ) A with hAσdef
      have hpfσ : @ResolvedAdmissibleSubgraph.IsProperForest phi4DivergenceMeasureFamily
          (G.mapPerm σ) Aσ :=
        (mpFor_isProperForest_iff phi4DivergenceMeasureFamily
          phi4PermInvariantDivergenceMeasureFamily σ A).mpr hpf
      have hstarA : cleanStarOfTotal phi4DivergenceMeasureFamily G A
          = cleanStarOf phi4DivergenceMeasureFamily A hpf := by
        unfold cleanStarOfTotal; rw [dif_pos hpf]
      have hstarAσ : cleanStarOfTotal phi4DivergenceMeasureFamily (G.mapPerm σ) Aσ
          = cleanStarOf phi4DivergenceMeasureFamily Aσ hpfσ := by
        unfold cleanStarOfTotal; rw [dif_pos hpfσ]
      have hcls := resolvedWDoublePrimeContract_class_mapPerm phi4DivergenceMeasureFamily
        phi4PermInvariantDivergenceMeasureFamily σ A hpf hpfσ hsupp
      have hclsTot :
          (A.contractWithStars (cleanStarOfTotal phi4DivergenceMeasureFamily G A)).toResolvedClass
            = (Aσ.contractWithStars
                (cleanStarOfTotal phi4DivergenceMeasureFamily (G.mapPerm σ) Aσ)).toResolvedClass := by
        rw [hstarA, hstarAσ]; exact hcls.symm
      exact resolvedForestRightTermFor_class_eq phi4DivergenceMeasureFamily
        phi4PermInvariantDivergenceMeasureFamily A Aσ
        (cleanStarOfTotal phi4DivergenceMeasureFamily G A)
        (cleanStarOfTotal phi4DivergenceMeasureFamily (G.mapPerm σ) Aσ) _ _ hclsTot }

end GaugeGeometry.QFT.Combinatorial
