import GaugeGeometry.QFT.HopfAlgebra.Phi4WTriplePrimeRightSurvivor

/-!
# QFT-R1-body-604 — remnant decompletion + contract-twice raw equality

This body builds the **decompleted remnant** of a forest-chosen outer component of a W‴ filtered split
choice and proves the genuine-decontraction HEADLINE: boundary-completing the decompleted remnant on the
global quotient `Q` reconstructs the local contracted graph up to the correcting permutation `τ`.

```
(remnantComponent s o).boundaryCompletedResolvedGraph = (localContractGraph s o).mapPerm τ
```

HALT compliance: axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); ZERO forbidden divergence
classes in any declaration's type (the survivor-embed / `resolvedComponentGen` helpers are NOT consumed;
the correcting-permutation engine is reproduced clean here, and the star/coordinate lemmas are re-derived
from instance-free primitives).  No `sorry` / `admit` / `native_decide`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

open ResolvedFeynmanSubgraph

variable {G : ResolvedFeynmanGraph}

set_option maxHeartbeats 3200000

/-- The concrete φ⁴ divergence measure family, registered file-locally (providable instance, NO forbidden
class). -/
noncomputable local instance phi4Inst604 : (H : FeynmanGraph) → DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

/-! ## Step 0a — the correcting-permutation engine (Mathlib-only, reproduced clean) -/

/-- A finite partial vertex relabeling extends to a permutation of `VertexId`: fix `S`, send the finite
injective family `src` to the finite injective family `dst`, both disjoint from `S`.  Reproduced verbatim
from the `private` copies in `Phi4ForestQuotientRename.lean` / `Phi4WDoublePrimeFullSupply.lean`; uses only
Mathlib primitives — no divergence class. -/
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
        have hi : hxsrc.choose = hysrc.choose := hdstInj hxy
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
        have hi : h.choose = i := hsrcInj h.choose_spec
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

/-! ## Step 0b — generic star reduction + freshness + injectivity + `retargetVertex_eq_star` -/

/-- The canonical W‴ supply star reduces to `cleanStarOf` on a proper forest. -/
theorem phi4WTriplePrime_gen_starOf_eq {H : ResolvedFeynmanGraph}
    (A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily H)
    (hpf : @ResolvedAdmissibleSubgraph.IsProperForest phi4DivergenceMeasureFamily H A)
    (δ : ResolvedFeynmanSubgraph H) :
    phi4WTriplePrimeCanonicalSupply.starOf H A δ = cleanStarOf phi4DivergenceMeasureFamily A hpf δ := by
  show cleanStarOfTotal phi4DivergenceMeasureFamily H A δ = _
  unfold cleanStarOfTotal
  rw [dif_pos hpf]

/-- Freshness: the canonical star lies outside the ambient's vertex set. -/
theorem phi4WTriplePrime_gen_star_not_mem {H : ResolvedFeynmanGraph}
    (A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily H)
    (hpf : @ResolvedAdmissibleSubgraph.IsProperForest phi4DivergenceMeasureFamily H A)
    {δ : ResolvedFeynmanSubgraph H} (hδ : δ ∈ A.elements) :
    phi4WTriplePrimeCanonicalSupply.starOf H A δ ∉ H.vertices := by
  rw [phi4WTriplePrime_gen_starOf_eq A hpf δ]
  exact cleanStarOf_not_mem_vertices A hpf hδ

/-- Injectivity of the canonical star on the forest's components. -/
theorem phi4WTriplePrime_gen_star_injOn {H : ResolvedFeynmanGraph}
    (A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily H)
    (hpf : @ResolvedAdmissibleSubgraph.IsProperForest phi4DivergenceMeasureFamily H A)
    {δ₁ : ResolvedFeynmanSubgraph H} (h₁ : δ₁ ∈ A.elements)
    {δ₂ : ResolvedFeynmanSubgraph H} (h₂ : δ₂ ∈ A.elements)
    (h : phi4WTriplePrimeCanonicalSupply.starOf H A δ₁
        = phi4WTriplePrimeCanonicalSupply.starOf H A δ₂) : δ₁ = δ₂ := by
  rw [phi4WTriplePrime_gen_starOf_eq A hpf δ₁, phi4WTriplePrime_gen_starOf_eq A hpf δ₂] at h
  exact cleanStarOf_injOn A hpf h₁ h₂ h

/-- A carrier vertex retargets to its element's star (clean re-derivation). -/
theorem phi4WTriplePrime_retargetVertex_eq_star {H : ResolvedFeynmanGraph}
    (A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily H)
    (starOf : ResolvedFeynmanSubgraph H → VertexId)
    {η : ResolvedFeynmanSubgraph H} (hη : η ∈ A.elements)
    {u : VertexId} (hu : u ∈ η.vertices) :
    A.retargetVertex starOf u = starOf η := by
  have huA : u ∈ A.vertices := ResolvedAdmissibleSubgraph.mem_vertices.mpr ⟨η, hη, hu⟩
  rw [ResolvedAdmissibleSubgraph.retargetVertex, ResolvedAdmissibleSubgraph.componentAt?_of_mem A huA]
  show starOf (A.componentAt huA) = starOf η
  congr 1
  by_contra hne
  exact Finset.disjoint_left.mp (A.pairwiseDisjoint (A.componentAt_mem huA) hη hne)
    (A.componentAt_vertex_mem huA) hu

/-! ## Step 1 — ForestChoiceOccurrence -/

/-- A forest-chosen outer component of a W‴ filtered split choice, with its live inner W‴ forest `B`
carried explicitly (to sidestep the dependent codomain). -/
structure Phi4WTriplePrime_ForestChoiceOccurrence
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) where
  γ : {x : ResolvedFeynmanSubgraph G //
        x ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G s.outer}
  B : (phi4WTriplePrimeCanonicalSupply.summandSupply γ.1.boundaryCompletedResolvedGraph).ForestIdx
  hchoice : s.choice γ (Finset.mem_attach _ γ) = Sum.inr B

variable {s : Phi4EdgeCompleteFilteredCoassocSplitChoice G}

/-- `B.1` (the inner forest) is a proper forest. -/
theorem phi4WTriplePrime_occ_B_isProperForest (o : Phi4WTriplePrime_ForestChoiceOccurrence s) :
    @ResolvedAdmissibleSubgraph.IsProperForest phi4DivergenceMeasureFamily
      o.γ.1.boundaryCompletedResolvedGraph o.B.1 :=
  ((mem_phi4WTriplePrimeIndex _ o.B.1).mp o.B.2).2.2.2.2.1

/-- Each inner component `δ ∈ B.1.elements` is externally-leg saturated on the inner ambient. -/
theorem phi4WTriplePrime_occ_B_saturated (o : Phi4WTriplePrime_ForestChoiceOccurrence s)
    {δ : ResolvedFeynmanSubgraph o.γ.1.boundaryCompletedResolvedGraph}
    (hδ : δ ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily
            o.γ.1.boundaryCompletedResolvedGraph o.B.1) :
    ResolvedExternalLegSaturated o.γ.1.boundaryCompletedResolvedGraph δ :=
  (((mem_phi4WTriplePrimeIndex _ o.B.1).mp o.B.2).2.2.2.2.2.1) δ hδ

/-! ## Step 2 — localContractGraph -/

/-- The LOCAL star-contraction of the inner forest `B.1` on the inner ambient `γ.boundaryCompletedResolvedGraph`. -/
noncomputable def phi4WTriplePrime_localContractGraph
    (o : Phi4WTriplePrime_ForestChoiceOccurrence s) : ResolvedFeynmanGraph :=
  o.B.1.contractWithStars
    (phi4WTriplePrimeCanonicalSupply.starOf o.γ.1.boundaryCompletedResolvedGraph o.B.1)

/-! ## Step 2b — promotion membership + rootRelativeInner injectivity -/

/-- A promoted inner component lands in `selectedOuter`. -/
theorem phi4WTriplePrime_remnant_promoted_mem (o : Phi4WTriplePrime_ForestChoiceOccurrence s)
    {δ : ResolvedFeynmanSubgraph o.γ.1.boundaryCompletedResolvedGraph}
    (hδ : δ ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily
            o.γ.1.boundaryCompletedResolvedGraph o.B.1) :
    rootRelativeInner o.γ.1 δ ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G
      (phi4WTriplePrime_selectedOuter s) := by
  rw [phi4WTriplePrime_selectedOuter_elements, Finset.mem_union]
  refine Or.inr ?_
  rw [phi4WTriplePrime_promotedOf_elements, Finset.mem_biUnion]
  refine ⟨o.γ, Finset.mem_attach _ _, ?_⟩
  rw [phi4WTriplePrime_mem_promotedElemsAt]
  exact ⟨o.B, o.hchoice, δ, hδ, rfl⟩

/-- `rootRelativeInner o.γ.1` is injective on `B.1.elements` (saturation determines legs from vertices). -/
theorem phi4WTriplePrime_rootRelativeInner_injOn (o : Phi4WTriplePrime_ForestChoiceOccurrence s)
    {δ₁ : ResolvedFeynmanSubgraph o.γ.1.boundaryCompletedResolvedGraph}
    (h₁ : δ₁ ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily
            o.γ.1.boundaryCompletedResolvedGraph o.B.1)
    {δ₂ : ResolvedFeynmanSubgraph o.γ.1.boundaryCompletedResolvedGraph}
    (h₂ : δ₂ ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily
            o.γ.1.boundaryCompletedResolvedGraph o.B.1)
    (h : rootRelativeInner o.γ.1 δ₁ = rootRelativeInner o.γ.1 δ₂) : δ₁ = δ₂ := by
  have hv : δ₁.vertices = δ₂.vertices := by
    have := congrArg ResolvedFeynmanSubgraph.vertices h
    simpa only [rootRelativeInner_vertices] using this
  apply ResolvedFeynmanSubgraph.ext
  · exact hv
  · have := congrArg ResolvedFeynmanSubgraph.internalEdges h
    simpa only [rootRelativeInner_internalEdges] using this
  · rw [externalLegs_eq_filter_of_saturated δ₁ (phi4WTriplePrime_occ_B_saturated o h₁),
      externalLegs_eq_filter_of_saturated δ₂ (phi4WTriplePrime_occ_B_saturated o h₂), hv]

/-! ## Step 3 — the correcting permutation τ -/

/-- The correcting-permutation existence for the remnant: fix the surviving inner-forest complement,
send each LOCAL star to the GLOBAL star of the corresponding promoted component. -/
theorem phi4WTriplePrime_remnantTau_exists (o : Phi4WTriplePrime_ForestChoiceOccurrence s) :
    ∃ τ : Equiv.Perm VertexId,
      (∀ v, v ∈ o.γ.1.vertices \ o.B.1.vertices → τ v = v) ∧
      (∀ i : {x // x ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily
                  o.γ.1.boundaryCompletedResolvedGraph o.B.1},
        τ (phi4WTriplePrimeCanonicalSupply.starOf o.γ.1.boundaryCompletedResolvedGraph o.B.1 i.1)
          = phi4WTriplePrimeCanonicalSupply.starOf G (phi4WTriplePrime_selectedOuter s)
              (rootRelativeInner o.γ.1 i.1)) := by
  have hpfB := phi4WTriplePrime_occ_B_isProperForest o
  have hpfSel := phi4WTriplePrime_selectedOuter_isProperForest s
  refine finite_visible_star_permutation
    (ι := {x // x ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily
                  o.γ.1.boundaryCompletedResolvedGraph o.B.1})
    (o.γ.1.vertices \ o.B.1.vertices)
    (fun i => phi4WTriplePrimeCanonicalSupply.starOf o.γ.1.boundaryCompletedResolvedGraph o.B.1 i.1)
    (fun i => phi4WTriplePrimeCanonicalSupply.starOf G (phi4WTriplePrime_selectedOuter s)
        (rootRelativeInner o.γ.1 i.1))
    ?_ ?_ ?_ ?_
  · -- hsrcInj
    intro i j hij
    exact Subtype.ext (phi4WTriplePrime_gen_star_injOn o.B.1 hpfB i.2 j.2 hij)
  · -- hdstInj
    intro i j hij
    have := phi4WTriplePrime_gen_star_injOn (phi4WTriplePrime_selectedOuter s) hpfSel
      (phi4WTriplePrime_remnant_promoted_mem o i.2) (phi4WTriplePrime_remnant_promoted_mem o j.2) hij
    exact Subtype.ext (phi4WTriplePrime_rootRelativeInner_injOn o i.2 j.2 this)
  · -- hsrcS
    intro i hc
    exact phi4WTriplePrime_gen_star_not_mem o.B.1 hpfB i.2 (Finset.mem_sdiff.mp hc).1
  · -- hdstS
    intro i hc
    exact phi4WTriplePrime_gen_star_not_mem (phi4WTriplePrime_selectedOuter s) hpfSel
      (phi4WTriplePrime_remnant_promoted_mem o i.2)
      (o.γ.1.vertices_subset (Finset.mem_sdiff.mp hc).1)

/-- The correcting permutation `τ` for the remnant. -/
noncomputable def phi4WTriplePrime_remnantTau (o : Phi4WTriplePrime_ForestChoiceOccurrence s) :
    Equiv.Perm VertexId :=
  (phi4WTriplePrime_remnantTau_exists o).choose

theorem phi4WTriplePrime_remnantTau_fix (o : Phi4WTriplePrime_ForestChoiceOccurrence s)
    {v : VertexId} (hv : v ∈ o.γ.1.vertices \ o.B.1.vertices) :
    phi4WTriplePrime_remnantTau o v = v :=
  (phi4WTriplePrime_remnantTau_exists o).choose_spec.1 v hv

theorem phi4WTriplePrime_remnantTau_map (o : Phi4WTriplePrime_ForestChoiceOccurrence s)
    (i : {x // x ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily
            o.γ.1.boundaryCompletedResolvedGraph o.B.1}) :
    phi4WTriplePrime_remnantTau o
        (phi4WTriplePrimeCanonicalSupply.starOf o.γ.1.boundaryCompletedResolvedGraph o.B.1 i.1)
      = phi4WTriplePrimeCanonicalSupply.starOf G (phi4WTriplePrime_selectedOuter s)
          (rootRelativeInner o.γ.1 i.1) :=
  (phi4WTriplePrime_remnantTau_exists o).choose_spec.2 i

/-! ## Step 3b — origin cases for a selectedOuter component -/

/-- Every `selectedOuter` component is either disjoint from `γ` or is a `γ`-promotion. -/
theorem phi4WTriplePrime_selectedOuter_elt_cases (o : Phi4WTriplePrime_ForestChoiceOccurrence s)
    {c : ResolvedFeynmanSubgraph G}
    (hc : c ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G
        (phi4WTriplePrime_selectedOuter s)) :
    _root_.Disjoint o.γ.1.vertices c.vertices ∨
      (∃ δ ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily
            o.γ.1.boundaryCompletedResolvedGraph o.B.1, c = rootRelativeInner o.γ.1 δ) := by
  rcases phi4WTriplePrime_selectedOuter_component_origin s hc with ⟨hcmem, hleft⟩ | hP
  · refine Or.inl ?_
    have hne : o.γ.1 ≠ c := by
      rintro rfl
      obtain ⟨h', hc_true⟩ := hleft
      exact absurd (hc_true.symm.trans o.hchoice) (by simp)
    exact s.outer.pairwiseDisjoint o.γ.2 hcmem hne
  · obtain ⟨γ', hγ', B', hchoice', δ', hδ', rfl⟩ := hP
    by_cases hγeq : γ' = o.γ.1
    · subst hγeq
      have hBeq : B' = o.B := Sum.inr.inj (hchoice'.symm.trans o.hchoice)
      exact Or.inr ⟨δ', hBeq ▸ hδ', rfl⟩
    · refine Or.inl ?_
      have hne : o.γ.1 ≠ γ' := fun h => hγeq h.symm
      have hdd : o.γ.1.Disjoint γ' := s.outer.pairwiseDisjoint o.γ.2 hγ' hne
      exact Finset.disjoint_of_subset_right
        (phi4WTriplePrime_rootRelativeInner_vertices_subset γ' δ') hdd

/-- A `γ`-vertex outside the inner forest is outside `selectedOuter`. -/
theorem phi4WTriplePrime_not_mem_selectedOuter (o : Phi4WTriplePrime_ForestChoiceOccurrence s)
    {v : VertexId} (hvγ : v ∈ o.γ.1.vertices) (hvB : v ∉ o.B.1.vertices) :
    v ∉ @ResolvedAdmissibleSubgraph.vertices phi4DivergenceMeasureFamily G
      (phi4WTriplePrime_selectedOuter s) := by
  intro hv
  rw [ResolvedAdmissibleSubgraph.mem_vertices] at hv
  obtain ⟨c, hc, hvc⟩ := hv
  rcases phi4WTriplePrime_selectedOuter_elt_cases o hc with hdisj | ⟨δ, hδ, rfl⟩
  · exact Finset.disjoint_left.mp hdisj hvγ hvc
  · apply hvB
    rw [rootRelativeInner_vertices] at hvc
    exact ResolvedAdmissibleSubgraph.mem_vertices.mpr ⟨δ, hδ, hvc⟩

/-! ## Step 3c — the coordinate lemma (τ ∘ local retarget = global retarget on γ) -/

/-- **The coordinate lemma.**  On `γ`'s vertices, `τ` composed with the LOCAL retarget equals the GLOBAL
retarget. -/
theorem phi4WTriplePrime_coord (o : Phi4WTriplePrime_ForestChoiceOccurrence s)
    {v : VertexId} (hvγ : v ∈ o.γ.1.vertices) :
    phi4WTriplePrime_remnantTau o
        (o.B.1.retargetVertex
          (phi4WTriplePrimeCanonicalSupply.starOf o.γ.1.boundaryCompletedResolvedGraph o.B.1) v)
      = (phi4WTriplePrime_selectedOuter s).retargetVertex
          (phi4WTriplePrimeCanonicalSupply.starOf G (phi4WTriplePrime_selectedOuter s)) v := by
  by_cases hvB : v ∈ o.B.1.vertices
  · obtain ⟨δ₀, hδ₀, hvδ₀⟩ := ResolvedAdmissibleSubgraph.mem_vertices.mp hvB
    have hvR : v ∈ (rootRelativeInner o.γ.1 δ₀).vertices := by
      rw [rootRelativeInner_vertices]; exact hvδ₀
    rw [phi4WTriplePrime_retargetVertex_eq_star o.B.1 _ hδ₀ hvδ₀,
        phi4WTriplePrime_remnantTau_map o ⟨δ₀, hδ₀⟩,
        phi4WTriplePrime_retargetVertex_eq_star (phi4WTriplePrime_selectedOuter s) _
          (phi4WTriplePrime_remnant_promoted_mem o hδ₀) hvR]
  · rw [o.B.1.retargetVertex_of_not_mem _ hvB,
        phi4WTriplePrime_remnantTau_fix o (Finset.mem_sdiff.mpr ⟨hvγ, hvB⟩),
        (phi4WTriplePrime_selectedOuter s).retargetVertex_of_not_mem _
          (phi4WTriplePrime_not_mem_selectedOuter o hvγ hvB)]

/-! ## Step 3d — complement-edge inclusion -/

/-- The inner forest's complement edges embed (with multiplicity) into `selectedOuter`'s. -/
theorem phi4WTriplePrime_complementEdges_le (o : Phi4WTriplePrime_ForestChoiceOccurrence s) :
    o.B.1.complementEdges
      ≤ (phi4WTriplePrime_selectedOuter s).complementEdges := by
  set P : Finset (ResolvedFeynmanSubgraph G) :=
    (@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily
        o.γ.1.boundaryCompletedResolvedGraph o.B.1).image (rootRelativeInner o.γ.1) with hPdef
  have hPsub : P ⊆ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G
      (phi4WTriplePrime_selectedOuter s) := by
    rw [hPdef, Finset.image_subset_iff]
    intro δ hδ
    exact phi4WTriplePrime_remnant_promoted_mem o hδ
  set Rest : Multiset ResolvedFeynmanEdge :=
    ((@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G
        (phi4WTriplePrime_selectedOuter s)) \ P).sum (fun c => c.internalEdges) with hRestdef
  have hPsum : P.sum (fun c => c.internalEdges) = o.B.1.internalEdges := by
    rw [hPdef, Finset.sum_image
      (fun δ₁ h₁ δ₂ h₂ h => phi4WTriplePrime_rootRelativeInner_injOn o h₁ h₂ h)]
    show (@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily
            o.γ.1.boundaryCompletedResolvedGraph o.B.1).sum
          (fun δ => (rootRelativeInner o.γ.1 δ).internalEdges)
        = o.B.1.internalEdges
    exact Finset.sum_congr rfl (fun δ _ => rootRelativeInner_internalEdges o.γ.1 δ)
  have hSelI : (phi4WTriplePrime_selectedOuter s).internalEdges = o.B.1.internalEdges + Rest := by
    have hsum : Rest + P.sum (fun c => c.internalEdges)
        = (phi4WTriplePrime_selectedOuter s).internalEdges := by
      rw [hRestdef]; exact Finset.sum_sdiff hPsub
    rw [hPsum] at hsum
    rw [← hsum, add_comm]
  rw [Multiset.le_iff_count]
  intro e
  have hcompB : Multiset.count e o.B.1.complementEdges
      = Multiset.count e o.γ.1.internalEdges - Multiset.count e o.B.1.internalEdges := by
    show Multiset.count e ((o.γ.1.boundaryCompletedResolvedGraph).internalEdges
          - o.B.1.internalEdges) = _
    rw [Multiset.count_sub, boundaryCompletedResolvedGraph_internalEdges]
  have hcompSel : Multiset.count e (phi4WTriplePrime_selectedOuter s).complementEdges
      = Multiset.count e G.internalEdges
        - Multiset.count e (phi4WTriplePrime_selectedOuter s).internalEdges := by
    show Multiset.count e (G.internalEdges - (phi4WTriplePrime_selectedOuter s).internalEdges) = _
    rw [Multiset.count_sub]
  rw [hcompB, hcompSel, hSelI, Multiset.count_add]
  have hle : Multiset.count e o.γ.1.internalEdges ≤ Multiset.count e G.internalEdges :=
    Multiset.count_le_of_le e o.γ.1.internalEdges_le
  by_cases hpos : 0 < Multiset.count e o.γ.1.internalEdges
  · have hR0 : Multiset.count e Rest = 0 := by
      rw [hRestdef, phi4WTriplePrime_count_finset_sum]
      refine Finset.sum_eq_zero (fun c hc => ?_)
      rw [Finset.mem_sdiff] at hc
      rcases phi4WTriplePrime_selectedOuter_elt_cases o hc.1 with hdisj | ⟨δ, hδ, rfl⟩
      · by_contra hne
        have hec : e ∈ c.internalEdges := Multiset.count_pos.mp (Nat.pos_of_ne_zero hne)
        have heγ : e ∈ o.γ.1.internalEdges := Multiset.count_pos.mp hpos
        obtain ⟨hsγ, _⟩ := o.γ.1.edges_supported e heγ
        obtain ⟨hsc, _⟩ := c.edges_supported e hec
        exact Finset.disjoint_left.mp hdisj hsγ hsc
      · exact absurd (show rootRelativeInner o.γ.1 δ ∈ P by
          rw [hPdef]; exact Finset.mem_image.mpr ⟨δ, hδ, rfl⟩) hc.2
    omega
  · have hz : Multiset.count e o.γ.1.internalEdges = 0 := Nat.eq_zero_of_not_pos hpos
    omega

/-! ## Step 4 — the decompleted remnant component -/

/-- The endpoints of a local contracted edge lie in the local contracted vertex set. -/
theorem phi4WTriplePrime_localContract_edge_endpoints
    (o : Phi4WTriplePrime_ForestChoiceOccurrence s)
    {f : ResolvedFeynmanEdge} (hf : f ∈ (phi4WTriplePrime_localContractGraph o).internalEdges) :
    f.source ∈ (phi4WTriplePrime_localContractGraph o).vertices
      ∧ f.target ∈ (phi4WTriplePrime_localContractGraph o).vertices := by
  rw [phi4WTriplePrime_localContractGraph,
    ResolvedAdmissibleSubgraph.contractWithStars_internalEdges] at hf
  obtain ⟨e, he, rfl⟩ := Multiset.mem_map.mp hf
  have heγ : e ∈ (o.γ.1.boundaryCompletedResolvedGraph).internalEdges := by
    have hle : o.B.1.complementEdges ≤ (o.γ.1.boundaryCompletedResolvedGraph).internalEdges :=
      Multiset.sub_le_self _ _
    exact Multiset.mem_of_le hle he
  rw [boundaryCompletedResolvedGraph_internalEdges] at heγ
  obtain ⟨hs, ht⟩ := o.γ.1.edges_supported e heγ
  refine ⟨?_, ?_⟩
  · rw [phi4WTriplePrime_localContractGraph]
    exact o.B.1.retargetVertex_mem_contractWithStars_vertices _
      (by rw [boundaryCompletedResolvedGraph_vertices]; exact hs)
  · rw [phi4WTriplePrime_localContractGraph]
    exact o.B.1.retargetVertex_mem_contractWithStars_vertices _
      (by rw [boundaryCompletedResolvedGraph_vertices]; exact ht)

/-- `Ltau.vertices ⊆ Q.vertices`. -/
theorem phi4WTriplePrime_remnant_vertices_subset
    (o : Phi4WTriplePrime_ForestChoiceOccurrence s) :
    ((phi4WTriplePrime_localContractGraph o).mapPerm (phi4WTriplePrime_remnantTau o)).vertices
      ⊆ (phi4WTriplePrime_selectedOuterContractGraph s).vertices := by
  intro w hw
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hw
  rw [phi4WTriplePrime_localContractGraph,
    ResolvedAdmissibleSubgraph.contractWithStars_vertices, Finset.mem_union] at hx
  rw [phi4WTriplePrime_selectedOuterContractGraph,
    ResolvedAdmissibleSubgraph.contractWithStars_vertices, Finset.mem_union]
  rcases hx with hxsdiff | hxstar
  · rw [Finset.mem_sdiff, boundaryCompletedResolvedGraph_vertices] at hxsdiff
    obtain ⟨hxγ, hxB⟩ := hxsdiff
    rw [phi4WTriplePrime_remnantTau_fix o (Finset.mem_sdiff.mpr ⟨hxγ, hxB⟩)]
    exact Or.inl (Finset.mem_sdiff.mpr
      ⟨o.γ.1.vertices_subset hxγ, phi4WTriplePrime_not_mem_selectedOuter o hxγ hxB⟩)
  · rw [ResolvedAdmissibleSubgraph.mem_starVertices] at hxstar
    obtain ⟨δ₀, hδ₀, rfl⟩ := hxstar
    rw [phi4WTriplePrime_remnantTau_map o ⟨δ₀, hδ₀⟩]
    exact Or.inr (ResolvedAdmissibleSubgraph.mem_starVertices.mpr
      ⟨rootRelativeInner o.γ.1 δ₀, phi4WTriplePrime_remnant_promoted_mem o hδ₀, rfl⟩)

/-- `Ltau.internalEdges = B.1.complementEdges` retargeted globally (the coordinate rewrite). -/
theorem phi4WTriplePrime_remnant_internalEdges_eq
    (o : Phi4WTriplePrime_ForestChoiceOccurrence s) :
    ((phi4WTriplePrime_localContractGraph o).mapPerm (phi4WTriplePrime_remnantTau o)).internalEdges
      = o.B.1.complementEdges.map
          ((phi4WTriplePrime_selectedOuter s).retargetEdge
            (phi4WTriplePrimeCanonicalSupply.starOf G (phi4WTriplePrime_selectedOuter s))) := by
  show (phi4WTriplePrime_localContractGraph o).internalEdges.map
      (ResolvedFeynmanEdge.map (phi4WTriplePrime_remnantTau o)) = _
  rw [phi4WTriplePrime_localContractGraph,
    ResolvedAdmissibleSubgraph.contractWithStars_internalEdges, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro e he
  have heγ : e ∈ (o.γ.1.boundaryCompletedResolvedGraph).internalEdges := by
    have hle : o.B.1.complementEdges ≤ (o.γ.1.boundaryCompletedResolvedGraph).internalEdges :=
      Multiset.sub_le_self _ _
    exact Multiset.mem_of_le hle he
  rw [boundaryCompletedResolvedGraph_internalEdges] at heγ
  obtain ⟨hs, ht⟩ := o.γ.1.edges_supported e heγ
  have hsrc := phi4WTriplePrime_coord o hs
  have htgt := phi4WTriplePrime_coord o ht
  simp only [Function.comp, ResolvedAdmissibleSubgraph.retargetEdge, ResolvedFeynmanEdge.retarget,
    ResolvedFeynmanEdge.map]
  rw [hsrc, htgt]

/-- `Ltau.internalEdges ≤ Q.internalEdges`. -/
theorem phi4WTriplePrime_remnant_internalEdges_le
    (o : Phi4WTriplePrime_ForestChoiceOccurrence s) :
    ((phi4WTriplePrime_localContractGraph o).mapPerm (phi4WTriplePrime_remnantTau o)).internalEdges
      ≤ (phi4WTriplePrime_selectedOuterContractGraph s).internalEdges := by
  rw [phi4WTriplePrime_remnant_internalEdges_eq, phi4WTriplePrime_selectedOuterContractGraph,
    ResolvedAdmissibleSubgraph.contractWithStars_internalEdges]
  exact Multiset.map_le_map (phi4WTriplePrime_complementEdges_le o)

/-- **body-604 (Step 4) — the decompleted remnant component** in the global quotient `Q`.  Its external
legs are the DECOMPLETED genuine ambient legs (`Q.externalLegs.filter`), never the synthetic legs. -/
noncomputable def phi4WTriplePrime_remnantComponent
    (o : Phi4WTriplePrime_ForestChoiceOccurrence s) :
    ResolvedFeynmanSubgraph (phi4WTriplePrime_selectedOuterContractGraph s) where
  vertices := ((phi4WTriplePrime_localContractGraph o).mapPerm (phi4WTriplePrime_remnantTau o)).vertices
  internalEdges :=
    ((phi4WTriplePrime_localContractGraph o).mapPerm (phi4WTriplePrime_remnantTau o)).internalEdges
  externalLegs := (phi4WTriplePrime_selectedOuterContractGraph s).externalLegs.filter
    (fun ℓ => ℓ.attachedTo ∈
      ((phi4WTriplePrime_localContractGraph o).mapPerm (phi4WTriplePrime_remnantTau o)).vertices)
  vertices_subset := phi4WTriplePrime_remnant_vertices_subset o
  internalEdges_le := phi4WTriplePrime_remnant_internalEdges_le o
  externalLegs_le := Multiset.filter_le _ _
  edges_supported := by
    intro e' he'
    obtain ⟨f, hf, rfl⟩ := Multiset.mem_map.mp he'
    obtain ⟨hfs, hft⟩ := phi4WTriplePrime_localContract_edge_endpoints o hf
    exact ⟨Finset.mem_image.mpr ⟨f.source, hfs, rfl⟩, Finset.mem_image.mpr ⟨f.target, hft, rfl⟩⟩
  legs_supported := fun ℓ hℓ => (Multiset.mem_filter.mp hℓ).2

@[simp] theorem phi4WTriplePrime_remnantComponent_vertices
    (o : Phi4WTriplePrime_ForestChoiceOccurrence s) :
    (phi4WTriplePrime_remnantComponent o).vertices
      = ((phi4WTriplePrime_localContractGraph o).mapPerm (phi4WTriplePrime_remnantTau o)).vertices :=
  rfl

@[simp] theorem phi4WTriplePrime_remnantComponent_internalEdges
    (o : Phi4WTriplePrime_ForestChoiceOccurrence s) :
    (phi4WTriplePrime_remnantComponent o).internalEdges
      = ((phi4WTriplePrime_localContractGraph o).mapPerm (phi4WTriplePrime_remnantTau o)).internalEdges :=
  rfl

@[simp] theorem phi4WTriplePrime_remnantComponent_externalLegs
    (o : Phi4WTriplePrime_ForestChoiceOccurrence s) :
    (phi4WTriplePrime_remnantComponent o).externalLegs
      = (phi4WTriplePrime_selectedOuterContractGraph s).externalLegs.filter
          (fun ℓ => ℓ.attachedTo ∈
            ((phi4WTriplePrime_localContractGraph o).mapPerm (phi4WTriplePrime_remnantTau o)).vertices) :=
  rfl

/-! ## Step 5a — ambient support, saturation, freshness, and the KEY membership iff -/

/-- Ambient endpoint/leg support of `G` (from W‴ membership). -/
theorem phi4WTriplePrime_ambient (o : Phi4WTriplePrime_ForestChoiceOccurrence s) :
    ResolvedAmbientSupported G :=
  ((mem_phi4WTriplePrimeIndex G s.outer).mp s.outer_mem).1

/-- `γ` is externally-leg saturated on `G`. -/
theorem phi4WTriplePrime_gamma_saturated (o : Phi4WTriplePrime_ForestChoiceOccurrence s) :
    ResolvedExternalLegSaturated G o.γ.1 :=
  (((mem_phi4WTriplePrimeIndex G s.outer).mp s.outer_mem).2.2.2.2.2.1) o.γ.1 o.γ.2

/-- The global retarget of a `selectedOuter`-vertex is fresh (outside `G`). -/
theorem phi4WTriplePrime_phi_not_mem_G (o : Phi4WTriplePrime_ForestChoiceOccurrence s)
    {v : VertexId}
    (hv : v ∈ @ResolvedAdmissibleSubgraph.vertices phi4DivergenceMeasureFamily G
        (phi4WTriplePrime_selectedOuter s)) :
    (phi4WTriplePrime_selectedOuter s).retargetVertex
        (phi4WTriplePrimeCanonicalSupply.starOf G (phi4WTriplePrime_selectedOuter s)) v ∉ G.vertices := by
  obtain ⟨c, hc, hvc⟩ := ResolvedAdmissibleSubgraph.mem_vertices.mp hv
  rw [phi4WTriplePrime_retargetVertex_eq_star (phi4WTriplePrime_selectedOuter s) _ hc hvc]
  exact phi4WTriplePrime_gen_star_not_mem (phi4WTriplePrime_selectedOuter s)
    (phi4WTriplePrime_selectedOuter_isProperForest s) hc

/-- **KEY membership iff.**  For an ambient vertex `v`, its global retarget lands in `Ltau.vertices` iff
`v ∈ γ.vertices`. -/
theorem phi4WTriplePrime_phi_mem_Ltau_iff (o : Phi4WTriplePrime_ForestChoiceOccurrence s)
    {v : VertexId} (hvG : v ∈ G.vertices) :
    (phi4WTriplePrime_selectedOuter s).retargetVertex
        (phi4WTriplePrimeCanonicalSupply.starOf G (phi4WTriplePrime_selectedOuter s)) v
      ∈ ((phi4WTriplePrime_localContractGraph o).mapPerm (phi4WTriplePrime_remnantTau o)).vertices
      ↔ v ∈ o.γ.1.vertices := by
  constructor
  · intro hmem
    obtain ⟨x, hx, hxeq⟩ := Finset.mem_image.mp hmem
    rw [phi4WTriplePrime_localContractGraph,
      ResolvedAdmissibleSubgraph.contractWithStars_vertices, Finset.mem_union] at hx
    rcases hx with hxsdiff | hxstar
    · rw [Finset.mem_sdiff, boundaryCompletedResolvedGraph_vertices] at hxsdiff
      rw [phi4WTriplePrime_remnantTau_fix o (Finset.mem_sdiff.mpr hxsdiff)] at hxeq
      by_cases hvSel : v ∈ @ResolvedAdmissibleSubgraph.vertices phi4DivergenceMeasureFamily G
          (phi4WTriplePrime_selectedOuter s)
      · exact absurd (hxeq ▸ o.γ.1.vertices_subset hxsdiff.1)
          (phi4WTriplePrime_phi_not_mem_G o hvSel)
      · rw [(phi4WTriplePrime_selectedOuter s).retargetVertex_of_not_mem _ hvSel] at hxeq
        rw [← hxeq]; exact hxsdiff.1
    · rw [ResolvedAdmissibleSubgraph.mem_starVertices] at hxstar
      obtain ⟨δ₀, hδ₀, hδ₀eq⟩ := hxstar
      rw [← hδ₀eq, phi4WTriplePrime_remnantTau_map o ⟨δ₀, hδ₀⟩] at hxeq
      by_cases hvSel : v ∈ @ResolvedAdmissibleSubgraph.vertices phi4DivergenceMeasureFamily G
          (phi4WTriplePrime_selectedOuter s)
      · obtain ⟨c, hc, hvc⟩ := ResolvedAdmissibleSubgraph.mem_vertices.mp hvSel
        rw [phi4WTriplePrime_retargetVertex_eq_star (phi4WTriplePrime_selectedOuter s) _ hc hvc] at hxeq
        have hceq : rootRelativeInner o.γ.1 δ₀ = c :=
          phi4WTriplePrime_gen_star_injOn (phi4WTriplePrime_selectedOuter s)
            (phi4WTriplePrime_selectedOuter_isProperForest s)
            (phi4WTriplePrime_remnant_promoted_mem o hδ₀) hc hxeq
        rw [← hceq, rootRelativeInner_vertices] at hvc
        exact δ₀.vertices_subset hvc
      · rw [(phi4WTriplePrime_selectedOuter s).retargetVertex_of_not_mem _ hvSel] at hxeq
        exact absurd (hxeq.symm ▸ hvG)
          (phi4WTriplePrime_gen_star_not_mem (phi4WTriplePrime_selectedOuter s)
            (phi4WTriplePrime_selectedOuter_isProperForest s)
            (phi4WTriplePrime_remnant_promoted_mem o hδ₀))
  · intro hvγ
    rw [← phi4WTriplePrime_coord o hvγ]
    apply Finset.mem_image.mpr
    refine ⟨o.B.1.retargetVertex
      (phi4WTriplePrimeCanonicalSupply.starOf o.γ.1.boundaryCompletedResolvedGraph o.B.1) v, ?_, rfl⟩
    rw [phi4WTriplePrime_localContractGraph]
    exact o.B.1.retargetVertex_mem_contractWithStars_vertices _
      (by rw [boundaryCompletedResolvedGraph_vertices]; exact hvγ)

/-- An edge of `selectedOuter.internalEdges` lies in one of its components. -/
theorem phi4WTriplePrime_mem_selectedOuter_internalEdges
    (o : Phi4WTriplePrime_ForestChoiceOccurrence s)
    {e : ResolvedFeynmanEdge} (he : e ∈ (phi4WTriplePrime_selectedOuter s).internalEdges) :
    ∃ c ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G
      (phi4WTriplePrime_selectedOuter s), e ∈ c.internalEdges := by
  have hpos : 0 < Multiset.count e
      ((@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G
          (phi4WTriplePrime_selectedOuter s)).sum (fun c => c.internalEdges)) :=
    Multiset.count_pos.mpr he
  rw [phi4WTriplePrime_count_finset_sum] at hpos
  by_contra hcon
  push_neg at hcon
  have hz : (∑ c ∈ (@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G
        (phi4WTriplePrime_selectedOuter s)), Multiset.count e c.internalEdges) = 0 :=
    Finset.sum_eq_zero (fun c hc => Multiset.count_eq_zero.mpr (fun hec => hcon c hc hec))
  omega

/-! ## Step 5b — EVEN part -/

/-- Step A: the DECOMPLETED genuine `Q`-legs equal `γ`'s genuine legs retargeted globally. -/
theorem phi4WTriplePrime_decompleted_legs (o : Phi4WTriplePrime_ForestChoiceOccurrence s) :
    (phi4WTriplePrime_selectedOuterContractGraph s).externalLegs.filter
        (fun ℓ => ℓ.attachedTo ∈
          ((phi4WTriplePrime_localContractGraph o).mapPerm (phi4WTriplePrime_remnantTau o)).vertices)
      = o.γ.1.externalLegs.map ((phi4WTriplePrime_selectedOuter s).retargetExternalLeg
          (phi4WTriplePrimeCanonicalSupply.starOf G (phi4WTriplePrime_selectedOuter s))) := by
  rw [phi4WTriplePrime_selectedOuterContractGraph,
    ResolvedAdmissibleSubgraph.contractWithStars_externalLegs,
    ← Multiset.map_filter_of_iff
        ((phi4WTriplePrime_selectedOuter s).retargetExternalLeg
          (phi4WTriplePrimeCanonicalSupply.starOf G (phi4WTriplePrime_selectedOuter s)))
        G.externalLegs
        (fun ℓ => ((phi4WTriplePrime_selectedOuter s).retargetExternalLeg
          (phi4WTriplePrimeCanonicalSupply.starOf G (phi4WTriplePrime_selectedOuter s)) ℓ).attachedTo ∈
          ((phi4WTriplePrime_localContractGraph o).mapPerm (phi4WTriplePrime_remnantTau o)).vertices)
        (fun ℓ => ℓ.attachedTo ∈
          ((phi4WTriplePrime_localContractGraph o).mapPerm (phi4WTriplePrime_remnantTau o)).vertices)
        (fun _ => Iff.rfl)]
  congr 1
  rw [externalLegs_eq_filter_of_saturated o.γ.1 (phi4WTriplePrime_gamma_saturated o)]
  apply Multiset.filter_congr
  intro ℓ hℓ
  exact phi4WTriplePrime_phi_mem_Ltau_iff o ((phi4WTriplePrime_ambient o).2 ℓ hℓ)

/-- The EVEN correspondence. -/
theorem phi4WTriplePrime_even_eq (o : Phi4WTriplePrime_ForestChoiceOccurrence s) :
    (phi4WTriplePrime_remnantComponent o).externalLegs.map encodeExistingLeg
      = (o.γ.1.externalLegs.map encodeExistingLeg).map
          (fun ℓ => ResolvedExternalLeg.map (phi4WTriplePrime_remnantTau o)
            (o.B.1.retargetExternalLeg
              (phi4WTriplePrimeCanonicalSupply.starOf o.γ.1.boundaryCompletedResolvedGraph o.B.1) ℓ)) := by
  rw [phi4WTriplePrime_remnantComponent_externalLegs, phi4WTriplePrime_decompleted_legs o,
    Multiset.map_map, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro ℓ hℓ
  have hattach : ℓ.attachedTo ∈ o.γ.1.vertices := o.γ.1.legs_supported ℓ hℓ
  have hcoord := phi4WTriplePrime_coord o hattach
  simp only [Function.comp, ResolvedAdmissibleSubgraph.retargetExternalLeg,
    ResolvedExternalLeg.retarget, ResolvedExternalLeg.map, encodeExistingLeg, existingLegId]
  rw [hcoord]

/-! ## Step 5c — ODD part -/

/-- The boundary predicate transports across the global retarget on complement edges. -/
theorem phi4WTriplePrime_remnantBd_iff (o : Phi4WTriplePrime_ForestChoiceOccurrence s)
    {e : ResolvedFeynmanEdge} (hsG : e.source ∈ G.vertices) (htG : e.target ∈ G.vertices) :
    (phi4WTriplePrime_remnantComponent o).resolvedIsBoundaryEdge
        ((phi4WTriplePrime_selectedOuter s).retargetEdge
          (phi4WTriplePrimeCanonicalSupply.starOf G (phi4WTriplePrime_selectedOuter s)) e)
      ↔ o.γ.1.resolvedIsBoundaryEdge e := by
  have hs := phi4WTriplePrime_phi_mem_Ltau_iff o hsG
  have ht := phi4WTriplePrime_phi_mem_Ltau_iff o htG
  unfold ResolvedFeynmanSubgraph.resolvedIsBoundaryEdge
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨hs.mp h1, fun hc => h2 (ht.mpr hc)⟩
    · exact Or.inr ⟨fun hc => h1 (hs.mpr hc), ht.mp h2⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨hs.mpr h1, fun hc => h2 (ht.mp hc)⟩
    · exact Or.inr ⟨fun hc => h1 (hs.mp hc), ht.mpr h2⟩

/-- The remnant's induced boundary edges equal `γ`'s boundary edges retargeted globally. -/
theorem phi4WTriplePrime_remnant_resolvedBoundaryEdges
    (o : Phi4WTriplePrime_ForestChoiceOccurrence s) :
    (phi4WTriplePrime_remnantComponent o).resolvedBoundaryEdges
      = o.γ.1.resolvedBoundaryEdges.map ((phi4WTriplePrime_selectedOuter s).retargetEdge
          (phi4WTriplePrimeCanonicalSupply.starOf G (phi4WTriplePrime_selectedOuter s))) := by
  have hQI : (phi4WTriplePrime_selectedOuterContractGraph s).internalEdges
      = (phi4WTriplePrime_selectedOuter s).complementEdges.map
          ((phi4WTriplePrime_selectedOuter s).retargetEdge
            (phi4WTriplePrimeCanonicalSupply.starOf G (phi4WTriplePrime_selectedOuter s))) := by
    rw [phi4WTriplePrime_selectedOuterContractGraph,
      ResolvedAdmissibleSubgraph.contractWithStars_internalEdges]
  show (phi4WTriplePrime_selectedOuterContractGraph s).internalEdges.filter
      (phi4WTriplePrime_remnantComponent o).resolvedIsBoundaryEdge = _
  rw [hQI, ← Multiset.map_filter_of_iff
        ((phi4WTriplePrime_selectedOuter s).retargetEdge
          (phi4WTriplePrimeCanonicalSupply.starOf G (phi4WTriplePrime_selectedOuter s)))
        (phi4WTriplePrime_selectedOuter s).complementEdges
        (fun e => (phi4WTriplePrime_remnantComponent o).resolvedIsBoundaryEdge
          ((phi4WTriplePrime_selectedOuter s).retargetEdge
            (phi4WTriplePrimeCanonicalSupply.starOf G (phi4WTriplePrime_selectedOuter s)) e))
        (phi4WTriplePrime_remnantComponent o).resolvedIsBoundaryEdge (fun _ => Iff.rfl)]
  congr 1
  have hzero : (phi4WTriplePrime_selectedOuter s).internalEdges.filter o.γ.1.resolvedIsBoundaryEdge
      = 0 := by
    rw [Multiset.filter_eq_nil]
    intro e he
    obtain ⟨c, hc, hec⟩ := phi4WTriplePrime_mem_selectedOuter_internalEdges o he
    rcases phi4WTriplePrime_selectedOuter_elt_cases o hc with hdisj | ⟨δ, hδ, rfl⟩
    · obtain ⟨hs, ht⟩ := c.edges_supported e hec
      rintro (⟨h1, _⟩ | ⟨_, h2⟩)
      · exact Finset.disjoint_left.mp hdisj h1 hs
      · exact Finset.disjoint_left.mp hdisj h2 ht
    · rw [rootRelativeInner_internalEdges] at hec
      obtain ⟨hs, ht⟩ := δ.edges_supported e hec
      rintro (⟨_, h2⟩ | ⟨h1, _⟩)
      · exact h2 (δ.vertices_subset ht)
      · exact h1 (δ.vertices_subset hs)
  have hfilt : (phi4WTriplePrime_selectedOuter s).complementEdges.filter o.γ.1.resolvedIsBoundaryEdge
      = o.γ.1.resolvedBoundaryEdges := by
    show (G.internalEdges - (phi4WTriplePrime_selectedOuter s).internalEdges).filter
        o.γ.1.resolvedIsBoundaryEdge = _
    rw [Multiset.filter_sub, hzero, Multiset.sub_zero]
    rfl
  have hcongr : (phi4WTriplePrime_selectedOuter s).complementEdges.filter
        (fun e => (phi4WTriplePrime_remnantComponent o).resolvedIsBoundaryEdge
          ((phi4WTriplePrime_selectedOuter s).retargetEdge
            (phi4WTriplePrimeCanonicalSupply.starOf G (phi4WTriplePrime_selectedOuter s)) e))
      = (phi4WTriplePrime_selectedOuter s).complementEdges.filter o.γ.1.resolvedIsBoundaryEdge := by
    apply Multiset.filter_congr
    intro e he
    exact phi4WTriplePrime_remnantBd_iff o
      ((phi4WTriplePrime_ambient o).1 e (Multiset.mem_of_le (Multiset.sub_le_self _ _) he)).1
      ((phi4WTriplePrime_ambient o).1 e (Multiset.mem_of_le (Multiset.sub_le_self _ _) he)).2
  rw [hcongr, hfilt]

/-- The ODD correspondence. -/
theorem phi4WTriplePrime_odd_eq (o : Phi4WTriplePrime_ForestChoiceOccurrence s) :
    (phi4WTriplePrime_remnantComponent o).resolvedBoundaryEdges.map
        (phi4WTriplePrime_remnantComponent o).boundaryExternalLeg
      = (o.γ.1.resolvedBoundaryEdges.map o.γ.1.boundaryExternalLeg).map
          (fun ℓ => ResolvedExternalLeg.map (phi4WTriplePrime_remnantTau o)
            (o.B.1.retargetExternalLeg
              (phi4WTriplePrimeCanonicalSupply.starOf o.γ.1.boundaryCompletedResolvedGraph o.B.1) ℓ)) := by
  rw [phi4WTriplePrime_remnant_resolvedBoundaryEdges o, Multiset.map_map, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro e he
  have he_mem := (ResolvedFeynmanSubgraph.resolvedBoundaryEdges_mem).mp he
  have hesupp := (phi4WTriplePrime_ambient o).1 e he_mem.1
  have hinside : o.γ.1.resolvedInsideEndpoint e ∈ o.γ.1.vertices :=
    o.γ.1.resolvedInsideEndpoint_mem e he_mem.2
  have hcoord := phi4WTriplePrime_coord o hinside
  -- endpoint agreement
  have hend : (phi4WTriplePrime_remnantComponent o).resolvedInsideEndpoint
        ((phi4WTriplePrime_selectedOuter s).retargetEdge
          (phi4WTriplePrimeCanonicalSupply.starOf G (phi4WTriplePrime_selectedOuter s)) e)
      = (phi4WTriplePrime_selectedOuter s).retargetVertex
          (phi4WTriplePrimeCanonicalSupply.starOf G (phi4WTriplePrime_selectedOuter s))
          (o.γ.1.resolvedInsideEndpoint e) := by
    show (if (phi4WTriplePrime_selectedOuter s).retargetVertex _ e.source
            ∈ (phi4WTriplePrime_remnantComponent o).vertices
          then (phi4WTriplePrime_selectedOuter s).retargetVertex _ e.source
          else (phi4WTriplePrime_selectedOuter s).retargetVertex _ e.target)
      = (phi4WTriplePrime_selectedOuter s).retargetVertex _
          (if e.source ∈ o.γ.1.vertices then e.source else e.target)
    rw [phi4WTriplePrime_remnantComponent_vertices]
    by_cases hsγ : e.source ∈ o.γ.1.vertices
    · rw [if_pos hsγ, if_pos ((phi4WTriplePrime_phi_mem_Ltau_iff o hesupp.1).mpr hsγ)]
    · rw [if_neg hsγ, if_neg (fun hc => hsγ ((phi4WTriplePrime_phi_mem_Ltau_iff o hesupp.1).mp hc))]
  show (phi4WTriplePrime_remnantComponent o).boundaryExternalLeg
      ((phi4WTriplePrime_selectedOuter s).retargetEdge
        (phi4WTriplePrimeCanonicalSupply.starOf G (phi4WTriplePrime_selectedOuter s)) e)
    = ResolvedExternalLeg.map (phi4WTriplePrime_remnantTau o)
        (o.B.1.retargetExternalLeg
          (phi4WTriplePrimeCanonicalSupply.starOf o.γ.1.boundaryCompletedResolvedGraph o.B.1)
          (o.γ.1.boundaryExternalLeg e))
  unfold ResolvedFeynmanSubgraph.boundaryExternalLeg ResolvedAdmissibleSubgraph.retargetExternalLeg
    ResolvedExternalLeg.retarget ResolvedExternalLeg.map
  rw [hend, hcoord]
  simp only [ResolvedFeynmanSubgraph.boundaryLegId, ResolvedAdmissibleSubgraph.retargetEdge,
    ResolvedFeynmanEdge.retarget]

/-! ## Step 5d — HEADLINE: the contract-twice raw graph equality -/

/-- **body-604 (Step 5, HEADLINE) — the decompleted-remnant boundary-completion reconstructs the local
contracted graph up to the correcting permutation `τ`.**  A RAW `ResolvedFeynmanGraph` equality (all three
fields, exact IDs / sectors / multiplicities). -/
theorem phi4WTriplePrime_remnant_contractTwice (o : Phi4WTriplePrime_ForestChoiceOccurrence s) :
    (phi4WTriplePrime_remnantComponent o).boundaryCompletedResolvedGraph
      = (phi4WTriplePrime_localContractGraph o).mapPerm (phi4WTriplePrime_remnantTau o) := by
  simp only [ResolvedFeynmanSubgraph.boundaryCompletedResolvedGraph, ResolvedFeynmanGraph.mapPerm,
    ResolvedFeynmanGraph.mk.injEq]
  refine ⟨rfl, rfl, ?_⟩
  rw [ResolvedFeynmanSubgraph.boundaryCompletedResolvedExternalLegs,
    phi4WTriplePrime_even_eq o, phi4WTriplePrime_odd_eq o,
    phi4WTriplePrime_localContractGraph, ResolvedAdmissibleSubgraph.contractWithStars_externalLegs,
    boundaryCompletedResolvedGraph_externalLegs,
    ResolvedFeynmanSubgraph.boundaryCompletedResolvedExternalLegs]
  simp only [Multiset.map_add, Multiset.map_map, Function.comp]

end GaugeGeometry.QFT.Combinatorial
