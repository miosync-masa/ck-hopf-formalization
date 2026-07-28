import GaugeGeometry.QFT.HopfAlgebra.Phi4ForestLeftRename
import GaugeGeometry.QFT.HopfAlgebra.Phi4ForestRightFactor

/-!
# QFT-R1-body-580 — the canonical φ⁴ forest quotient graph is rename-invariant up to class

Body-578 built the φ⁴ forest coproduct index rename `Equiv`
(`FeynmanGraph.phi4ForestCoproductIndexEquiv`) and body-579 proved the left tensor factor
(`AdmissibleSubgraph.toPhi4HopfH`) rename-invariant.  This body proves the **right tensor factor**
fact: the canonical φ⁴ forest quotient graph `G/A` (body-573
`phi4CanonicalForestContractGraph`) is unchanged **as an isomorphism class** when the ambient
graph — and every component with it — is renamed by a vertex permutation `π`:

    (phi4CanonicalForestContractGraph (G.mapPerm π) Aπ hAπ).toClass
      = (phi4CanonicalForestContractGraph G A hA).toClass .

The strict labeled graphs are **not** equal — the canonical fresh stars of `G` and of `G.mapPerm π`
are chosen independently, so `targetStar (γ.mapPerm π) ≠ π (sourceStar γ)` in general.  A
**correcting permutation** `τ := σ * π` absorbs the star mismatch: `σ` fixes every visible vertex of
`G.mapPerm π` and sends each `π`-image of a source star to the matching target star.  The two action
laws (`τ = π` on ambient vertices, `τ (sourceStar γ) = targetStar (γ.mapPerm π)`) promote to the
whole-graph equality `Qπ = Q.mapPerm τ`, whence `Qπ.toClass = Q.toClass` by
`FeynmanGraph.toClass_eq_iff`.

The correcting-permutation engine `finite_visible_star_permutation` is the clean Mathlib-only
finite-support extension lemma (copied from `Coassoc.lean`); it consumes **no** divergence class.

Per the HALT: **no** strict canonical-star equality `targetStar (γ.mapPerm π) = π (sourceStar γ)` is
ever proved or stated — the whole construction routes through `σ`; no `Finset.sum_bij` / tensor
summand / coproduct sum / `Quotient.lift` / `aeval` / reflection / W″ / coassoc; zero new
`class`/`structure`/permanent `instance`; zero forbidden divergence classes in any decl's type.  The
only instance binder is the blanket `[∀ H, Fintype (FeynmanSubgraph H)]` — finite-sum infrastructure.
-/

namespace GaugeGeometry.QFT.Combinatorial

-- Finite-sum infrastructure as a blanket (so mapped/quotient graphs' `Fintype` resolves without
-- reducing deep terms).  NOT physics.
variable [∀ H : FeynmanGraph, Fintype (FeynmanSubgraph H)]
variable {G : FeynmanGraph}

/-! ## Re-derived instance-free permutation transports (body-578's copies are `private`) -/

private theorem mpsQR_vertices {G₁ G₂ : FeynmanGraph} {π : Equiv.Perm VertexId}
    (hπ : G₂ = G₁.mapPerm π) (γ : FeynmanSubgraph G₁) :
    (mapPermSubgraph hπ γ).vertices = γ.vertices.image π := by
  unfold mapPermSubgraph; subst hπ; exact FeynmanSubgraph.mapPerm_vertices π γ

private theorem mpsQR_internalEdges {G₁ G₂ : FeynmanGraph} {π : Equiv.Perm VertexId}
    (hπ : G₂ = G₁.mapPerm π) (γ : FeynmanSubgraph G₁) :
    (mapPermSubgraph hπ γ).internalEdges = γ.internalEdges.map (FeynmanEdge.map π) := by
  unfold mapPermSubgraph; subst hπ; exact FeynmanSubgraph.mapPerm_internalEdges π γ

/-- `mapPermSubgraph` transport is injective on subgraphs (re-derived instance-free from
`FeynmanSubgraph.ext_iff` + edge/leg map injectivity; body-578/579's copies are `private`). -/
private theorem mpsQR_injective
    {G₁ G₂ : FeynmanGraph} {π : Equiv.Perm VertexId} (hπ : G₂ = G₁.mapPerm π) :
    Function.Injective (mapPermSubgraph hπ : FeynmanSubgraph G₁ → FeynmanSubgraph G₂) := by
  subst hπ
  intro a b hab
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

private theorem mapPermAdmFor_elements_QR
    (D : DivergenceMeasureFamily) (Inv : PermInvariantDivergenceMeasureFamily D)
    {G₁ G₂ : FeynmanGraph} {π : Equiv.Perm VertexId}
    (hπ : G₂ = G₁.mapPerm π) (A : AdmissibleSubgraphFor D G₁) :
    (mapPermAdmissibleSubgraphFor D Inv hπ A).elements =
      A.elements.image (mapPermSubgraph hπ) := rfl

/-- `Multiset.map` distributes over subtraction along an injective map. -/
private theorem multiset_map_sub_inj_QR {α β : Type*}
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

private theorem mapPermAdmFor_internalEdges_QR
    (D : DivergenceMeasureFamily) (Inv : PermInvariantDivergenceMeasureFamily D)
    {G₁ G₂ : FeynmanGraph} {π : Equiv.Perm VertexId}
    (hπ : G₂ = G₁.mapPerm π) (A : AdmissibleSubgraphFor D G₁) :
    (@AdmissibleSubgraph.internalEdges G₂ (D G₂) (mapPermAdmissibleSubgraphFor D Inv hπ A)) =
      (@AdmissibleSubgraph.internalEdges G₁ (D G₁) A).map (FeynmanEdge.map π) := by
  classical
  simp only [AdmissibleSubgraph.internalEdges]
  rw [mapPermAdmFor_elements_QR, Finset.sum_image (mpsQR_injective hπ).injOn]
  simp only [mpsQR_internalEdges]
  rw [← Multiset.coe_mapAddMonoidHom (FeynmanEdge.map π),
    map_sum (Multiset.mapAddMonoidHom (FeynmanEdge.map π))]

private theorem mapPermAdmFor_complementEdges_QR
    (D : DivergenceMeasureFamily) (Inv : PermInvariantDivergenceMeasureFamily D)
    {G₁ G₂ : FeynmanGraph} {π : Equiv.Perm VertexId}
    (hπ : G₂ = G₁.mapPerm π) (A : AdmissibleSubgraphFor D G₁) :
    (@AdmissibleSubgraph.complementEdges G₂ (D G₂) (mapPermAdmissibleSubgraphFor D Inv hπ A)) =
      (@AdmissibleSubgraph.complementEdges G₁ (D G₁) A).map (FeynmanEdge.map π) := by
  simp only [AdmissibleSubgraph.complementEdges]
  rw [mapPermAdmFor_internalEdges_QR,
    multiset_map_sub_inj_QR (FeynmanGraph.FeynmanEdge_map_injective π)]
  congr 1
  subst hπ
  rw [FeynmanGraph.mapPerm_internalEdges]

/-! ## The correcting-permutation engine (Mathlib-only finite-support extension) -/

/-- A finite partial vertex relabeling can be extended to a permutation of `VertexId`: fix the finite
set `S` and send the finite injective family `src` to the finite injective family `dst`, provided both
star families are disjoint from `S`.  Copied verbatim from `Coassoc.lean`; uses only Mathlib
primitives (`Finset.exists_equiv_extend_of_card_eq`, `Equiv.Perm.extendDomain`,
`Equiv.Perm.extendDomain_apply_image`, `Finset.equivToSet`) — no divergence class. -/
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

/-! ## Target — the canonical φ⁴ forest quotient graph is rename-invariant up to class -/

/-- **body-580 (TARGET) — the canonical φ⁴ forest quotient graph is rename-invariant up to
isomorphism class.**  Renaming the ambient graph by `π` (transporting the forest to `Aπ`) leaves the
canonical forest quotient `G/A` unchanged as an isomorphism class.  The strict labeled graphs differ
only in their canonical fresh stars; the correcting permutation `τ = σ * π` transports one to the
other, giving `Qπ = Q.mapPerm τ`, hence equal classes.  No strict canonical-star equality is used. -/
theorem phi4CanonicalForestContractGraph_mapPerm_toClass_eq
    (hGWF : G.WellFormed) (π : Equiv.Perm VertexId)
    (A : AdmissibleSubgraphFor phi4DivergenceMeasureFamily G)
    (hA : A ∈ G.phi4ProperDisjointAdmissibleDivergentSubgraphs)
    (hAπ : mapPermAdmissibleSubgraphFor phi4DivergenceMeasureFamily
        phi4PermInvariantDivergenceMeasureFamily (rfl : G.mapPerm π = G.mapPerm π) A
        ∈ (G.mapPerm π).phi4ProperDisjointAdmissibleDivergentSubgraphs) :
    (phi4CanonicalForestContractGraph (G.mapPerm π)
        (mapPermAdmissibleSubgraphFor phi4DivergenceMeasureFamily
          phi4PermInvariantDivergenceMeasureFamily (rfl : G.mapPerm π = G.mapPerm π) A) hAπ).toClass
      = (phi4CanonicalForestContractGraph G A hA).toClass := by
  classical
  letI : DivergenceMeasure G := phi4DivergenceMeasureFamily G
  letI : DivergenceMeasure (G.mapPerm π) := phi4DivergenceMeasureFamily (G.mapPerm π)
  set Aπ := mapPermAdmissibleSubgraphFor phi4DivergenceMeasureFamily
    phi4PermInvariantDivergenceMeasureFamily (rfl : G.mapPerm π = G.mapPerm π) A with hAπdef
  -- element / vertex / complement transports for `Aπ`
  have hAπelem : Aπ.elements =
      A.elements.image (mapPermSubgraph (rfl : G.mapPerm π = G.mapPerm π)) := by
    rw [hAπdef]
    exact mapPermAdmFor_elements_QR phi4DivergenceMeasureFamily
      phi4PermInvariantDivergenceMeasureFamily (rfl : G.mapPerm π = G.mapPerm π) A
  have hAπcompl : Aπ.complementEdges = A.complementEdges.map (FeynmanEdge.map π) := by
    rw [hAπdef]
    exact mapPermAdmFor_complementEdges_QR phi4DivergenceMeasureFamily
      phi4PermInvariantDivergenceMeasureFamily (rfl : G.mapPerm π = G.mapPerm π) A
  have hAπ_vertices : Aπ.vertices = A.vertices.image π := by
    ext u
    rw [AdmissibleSubgraph.mem_vertices, Finset.mem_image]
    constructor
    · rintro ⟨γ', hγ', huγ'⟩
      rw [hAπelem] at hγ'
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hγ'
      rw [mpsQR_vertices] at huγ'
      obtain ⟨w, hwγ, rfl⟩ := Finset.mem_image.mp huγ'
      exact ⟨w, AdmissibleSubgraph.mem_vertices.mpr ⟨γ, hγ, hwγ⟩, rfl⟩
    · rintro ⟨w, hwA, rfl⟩
      obtain ⟨γ, hγ, hwγ⟩ := AdmissibleSubgraph.mem_vertices.mp hwA
      refine ⟨mapPermSubgraph (rfl : G.mapPerm π = G.mapPerm π) γ, ?_, ?_⟩
      · rw [hAπelem]; exact Finset.mem_image.mpr ⟨γ, hγ, rfl⟩
      · rw [mpsQR_vertices]; exact Finset.mem_image_of_mem π hwγ
  -- pairwise disjointness both sides
  have hADisj : @AdmissibleSubgraph.IsPairwiseDisjoint G (phi4DivergenceMeasureFamily G) A :=
    FeynmanGraph.properDisjointAdmissibleDivergentSubgraphsFor_isPairwiseDisjoint
      phi4DivergenceMeasureFamily G hA
  have hAπDisj : @AdmissibleSubgraph.IsPairwiseDisjoint (G.mapPerm π)
      (phi4DivergenceMeasureFamily (G.mapPerm π)) Aπ :=
    FeynmanGraph.properDisjointAdmissibleDivergentSubgraphsFor_isPairwiseDisjoint
      phi4DivergenceMeasureFamily (G.mapPerm π) hAπ
  -- ==== Step A : the correcting permutation τ = σ * π ====
  have hsrcInj : Function.Injective
      (fun γ : {x // x ∈ A.elements} => π (A.componentFreshStar γ.1)) := by
    intro γ₁ γ₂ h
    have hcfs : A.componentFreshStar γ₁.1 = A.componentFreshStar γ₂.1 := π.injective h
    exact Subtype.ext (AdmissibleSubgraph.componentFreshStar_eq_of_eq γ₁.2 hcfs)
  have hdstInj : Function.Injective
      (fun γ : {x // x ∈ A.elements} =>
        Aπ.componentFreshStar (mapPermSubgraph (rfl : G.mapPerm π = G.mapPerm π) γ.1)) := by
    intro γ₁ γ₂ h
    have hmem₁ : mapPermSubgraph (rfl : G.mapPerm π = G.mapPerm π) γ₁.1 ∈ Aπ.elements := by
      rw [hAπelem]; exact Finset.mem_image.mpr ⟨γ₁.1, γ₁.2, rfl⟩
    have hmps : mapPermSubgraph (rfl : G.mapPerm π = G.mapPerm π) γ₁.1
              = mapPermSubgraph (rfl : G.mapPerm π = G.mapPerm π) γ₂.1 :=
      AdmissibleSubgraph.componentFreshStar_eq_of_eq hmem₁ h
    exact Subtype.ext (mpsQR_injective (rfl : G.mapPerm π = G.mapPerm π) hmps)
  have hsrcS : ∀ γ : {x // x ∈ A.elements},
      π (A.componentFreshStar γ.1) ∉ (G.mapPerm π).vertices := by
    intro γ hc
    rw [FeynmanGraph.mapPerm_vertices, π.injective.mem_finset_image] at hc
    exact A.componentFreshStar_not_mem_vertices γ.1 hc
  have hdstS : ∀ γ : {x // x ∈ A.elements},
      Aπ.componentFreshStar (mapPermSubgraph (rfl : G.mapPerm π = G.mapPerm π) γ.1)
        ∉ (G.mapPerm π).vertices := by
    intro γ
    exact Aπ.componentFreshStar_not_mem_vertices
      (mapPermSubgraph (rfl : G.mapPerm π = G.mapPerm π) γ.1)
  obtain ⟨σ, hσfix, hσmap⟩ := finite_visible_star_permutation
    (ι := {x // x ∈ A.elements})
    (G.mapPerm π).vertices
    (fun γ => π (A.componentFreshStar γ.1))
    (fun γ => Aπ.componentFreshStar (mapPermSubgraph (rfl : G.mapPerm π = G.mapPerm π) γ.1))
    hsrcInj hdstInj hsrcS hdstS
  set τ : Equiv.Perm VertexId := σ * π with hτdef
  have hτ_ambient : ∀ v, v ∈ G.vertices → τ v = π v := by
    intro v hv
    rw [hτdef, Equiv.Perm.mul_apply]
    exact hσfix (π v) (by rw [FeynmanGraph.mapPerm_vertices]; exact Finset.mem_image_of_mem π hv)
  have hτ_star : ∀ γ, γ ∈ A.elements →
      τ (A.componentFreshStar γ)
        = Aπ.componentFreshStar (mapPermSubgraph (rfl : G.mapPerm π = G.mapPerm π) γ) := by
    intro γ hγ
    rw [hτdef, Equiv.Perm.mul_apply]
    exact hσmap ⟨γ, hγ⟩
  -- ==== Step B : the retarget coordinate law ====
  have hcoord : ∀ v, v ∈ G.vertices →
      τ (A.retargetVertex A.componentFreshStar v)
        = Aπ.retargetVertex Aπ.componentFreshStar (π v) := by
    intro v hvG
    by_cases hvA : v ∈ A.vertices
    · obtain ⟨γ, hγ, hvγ⟩ := AdmissibleSubgraph.mem_vertices.mp hvA
      have hmpsγ : mapPermSubgraph (rfl : G.mapPerm π = G.mapPerm π) γ ∈ Aπ.elements := by
        rw [hAπelem]; exact Finset.mem_image.mpr ⟨γ, hγ, rfl⟩
      have hπvγ : π v ∈ (mapPermSubgraph (rfl : G.mapPerm π = G.mapPerm π) γ).vertices := by
        rw [mpsQR_vertices]; exact Finset.mem_image_of_mem π hvγ
      rw [AdmissibleSubgraph.retargetVertex_of_mem_component hADisj A.componentFreshStar hγ hvγ,
        hτ_star γ hγ,
        AdmissibleSubgraph.retargetVertex_of_mem_component hAπDisj Aπ.componentFreshStar
          hmpsγ hπvγ]
    · have hπvA : π v ∉ Aπ.vertices := by
        rw [hAπ_vertices, π.injective.mem_finset_image]; exact hvA
      rw [AdmissibleSubgraph.retargetVertex_of_not_mem A A.componentFreshStar hvA,
        hτ_ambient v hvG,
        AdmissibleSubgraph.retargetVertex_of_not_mem Aπ Aπ.componentFreshStar hπvA]
  -- ==== Step C : the three field equalities → Qπ = Q.mapPerm τ ====
  have hv : (Aπ.contractWithStars Aπ.componentFreshStar).vertices
          = ((A.contractWithStars A.componentFreshStar).mapPerm τ).vertices := by
    rw [FeynmanGraph.mapPerm_vertices, AdmissibleSubgraph.contractWithStars_vertices,
        AdmissibleSubgraph.contractWithStars_vertices, Finset.image_union]
    congr 1
    · have himg : (G.vertices \ A.vertices).image τ = (G.vertices \ A.vertices).image π :=
        Finset.image_congr (fun w hw => hτ_ambient w (Finset.mem_sdiff.mp hw).1)
      rw [himg, Finset.image_sdiff G.vertices A.vertices π.injective,
        FeynmanGraph.mapPerm_vertices, hAπ_vertices]
    · show Aπ.elements.image Aπ.componentFreshStar
         = (A.elements.image A.componentFreshStar).image τ
      rw [hAπelem, Finset.image_image, Finset.image_image]
      exact Finset.image_congr (fun γ hγ => (hτ_star γ hγ).symm)
  have hi : (Aπ.contractWithStars Aπ.componentFreshStar).internalEdges
          = ((A.contractWithStars A.componentFreshStar).mapPerm τ).internalEdges := by
    rw [FeynmanGraph.mapPerm_internalEdges,
        AdmissibleSubgraph.contractWithStars_internalEdges,
        AdmissibleSubgraph.contractWithStars_internalEdges,
        hAπcompl, Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl (fun e he => ?_)
    have heG : e ∈ G.internalEdges := A.mem_ambientInternalEdges_of_mem_complementEdges he
    have hsupp : e.source ∈ G.vertices ∧ e.target ∈ G.vertices := hGWF.1 e heG
    show Aπ.retargetEdge Aπ.componentFreshStar (FeynmanEdge.map π e)
       = FeynmanEdge.map τ (A.retargetEdge A.componentFreshStar e)
    show FeynmanEdge.mk (Aπ.retargetVertex Aπ.componentFreshStar (π e.source))
          (Aπ.retargetVertex Aπ.componentFreshStar (π e.target)) e.sector
       = FeynmanEdge.mk (τ (A.retargetVertex A.componentFreshStar e.source))
          (τ (A.retargetVertex A.componentFreshStar e.target)) e.sector
    exact (FeynmanEdge.mk.injEq _ _ _ _ _ _).mpr
      ⟨(hcoord e.source hsupp.1).symm, (hcoord e.target hsupp.2).symm, rfl⟩
  have hlegs : (Aπ.contractWithStars Aπ.componentFreshStar).externalLegs
          = ((A.contractWithStars A.componentFreshStar).mapPerm τ).externalLegs := by
    rw [FeynmanGraph.mapPerm_externalLegs,
        AdmissibleSubgraph.contractWithStars_externalLegs,
        AdmissibleSubgraph.contractWithStars_externalLegs,
        FeynmanGraph.mapPerm_externalLegs, Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl (fun ℓ hℓmem => ?_)
    have hℓ : ℓ.attachedTo ∈ G.vertices := hGWF.2 ℓ hℓmem
    show Aπ.retargetExternalLeg Aπ.componentFreshStar (ExternalLeg.map π ℓ)
       = ExternalLeg.map τ (A.retargetExternalLeg A.componentFreshStar ℓ)
    show ExternalLeg.mk (Aπ.retargetVertex Aπ.componentFreshStar (π ℓ.attachedTo)) ℓ.sector
       = ExternalLeg.mk (τ (A.retargetVertex A.componentFreshStar ℓ.attachedTo)) ℓ.sector
    exact (ExternalLeg.mk.injEq _ _ _ _).mpr ⟨(hcoord ℓ.attachedTo hℓ).symm, rfl⟩
  have hτcontract : Aπ.contractWithStars Aπ.componentFreshStar
          = (A.contractWithStars A.componentFreshStar).mapPerm τ :=
    congr (congr (congrArg FeynmanGraph.mk hv) hi) hlegs
  -- ==== Step D : whole-graph iso class equality ====
  rw [phi4CanonicalForestContractGraph_eq_contractWithStars (G.mapPerm π) Aπ hAπ,
      phi4CanonicalForestContractGraph_eq_contractWithStars G A hA]
  exact ((FeynmanGraph.toClass_eq_iff (A.contractWithStars A.componentFreshStar)
      (Aπ.contractWithStars Aπ.componentFreshStar)).mpr ⟨τ, hτcontract⟩).symm

end GaugeGeometry.QFT.Combinatorial
