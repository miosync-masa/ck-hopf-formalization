import GaugeGeometry.QFT.HopfAlgebra.Phi4StableTwoStageStars

/-!
# QFT-R1-body-639c — the STABLE two-stage RETARGET COMPOSITION coordinate law (third sub-body of the
`quot_eq` campaign)

Body-639a delivered the EXACT two-stage residual geometry; body-639b delivered final-star ownership (the two
per-sector `starOf` injectivities and the two surviving-root freshnesses).  This body assembles those four points
into the **single global correcting permutation** `stableTwoStageTau` and proves the **two-stage retarget
composition coordinate law**: composing the two contraction retargets and correcting by `τ` reproduces the
one-stage outer retarget on every ambient vertex.  Body-639d projects this coordinate law plus 639a's exact
residual onto the three graph fields (raw graph / class equality / the HEADLINE third factor).

With `s : StablePhi4MixedSplitChoice G hSt` and `Q := stableSelectedOuterContractGraph s.1`:

## Steps
* **Step 1 — the global correcting permutation.**  `stableTwoStageTau` is the permutation of `VertexId` that
  sends every **final two-stage star** to the corresponding **one-stage outer star**, fixing the surviving roots.
  Its existence is `stableTwoStage_finite_visible_star_permutation` (re-derived `private` from Mathlib primitives
  — `Finset.exists_equiv_extend_of_card_eq` + `Equiv.Perm.extendDomain`, mirroring body-635's engine, NO
  divergence class), fed body-639b's four points DIRECTLY: `stableFinalTwoStageStar_injective` (source
  injective), `stableOneStageOuterStar_injective` (target injective),
  `stableFinalTwoStageStar_not_mem_survivors` (source fresh), `stableOneStageOuterStar_not_mem_survivors` (target
  fresh).  Direction is `final two-stage star ──τ──▶ one-stage outer star`.
* **Step 2 — τ's two action laws.**  `stableTwoStageTau_of_survivor` (fixes surviving roots) and
  `stableTwoStageTau_finalStar` (sends the final star to the one-stage star).
* **Step 3 — route ownership** (where the two-stage retarget intermediate point lands).
  `stableTwoStage_route_survivor` (an outer-outside root is fixed by BOTH stages), `stableTwoStage_route_left`
  (the first-stage star is inside `Q` but OUTSIDE the quotient forest, so the second stage fixes it),
  `stableTwoStage_route_right` (the first-stage coordinate lands in the matching `stableRightSurvivor`
  component), `stableTwoStage_route_forest` (the first-stage coordinate lands in the matching
  `stableRemnantComponent` — routed by REMNANT MEMBERSHIP `stableRemnant_phi_mem_Ltau_iff` ONLY, NOTHING from the
  local `stableRemnantTau`).
* **Step 4 — branchwise composition.**  `stableTwoStage_retarget_of_left` / `_of_right` / `_of_forest` /
  `_of_survivor`: for each `γ ∈ s.1.outer.elements` and `v ∈ γ.vertices` (and the surviving roots), the
  τ-corrected two-stage retarget equals the one-stage outer retarget.  `stableTwoStageTau_finalStar` is the ONLY
  coordinate correction; NO strict star equality is claimed.
* **Step 5 (HEADLINE) — the coordinate law.**  `stableTwoStage_retarget_comp`: for every `v ∈ G.vertices`,
  `τ (Q-retarget (A-retarget v)) = outer-retarget v`.

## HALT / red lines (639c scope: the coordinate law ONLY)
`stableTwoStageTau = stableRemnantTau` is PERMANENTLY NOT claimed; there is NO global composition of the local
per-occurrence τ's — `stableTwoStageTau` is built independently from body-639b's four points.  NOT entered here
(they belong to 639d): the raw graph / class / rightTerm equality; the exact-residual re-proof (READ 639a);
`sum_bij` / alpha / coassoc.  NO strict canonical-star equality; NO orbit quotient / dedup.  ZERO new `structure`
/ `class` / permanent `instance` (one file-local `local instance` for the φ⁴ family; the perm engine is
`private`); ZERO forbidden divergence class in any declaration TYPE; ZERO `sorry` / `admit` / `native_decide`;
NO `HEq` / `cast` / graph-data `▸` (Prop-membership `▸` only).  Body-625's no-go and bodies 629-639b / the old
carrier are UNEDITED.  Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

open ResolvedFeynmanSubgraph

variable {G : ResolvedFeynmanGraph}

/-- The concrete φ⁴ divergence measure family, registered file-locally (providable instance, NO forbidden
class). -/
noncomputable local instance instPhi4DivergenceMeasureFamily639c : (H : FeynmanGraph) → DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

variable {hSt : StableResolvedBoundaryIds G}

/-! ## Step 1 — the correcting-permutation engine (Mathlib-only, re-derived clean, `private`) -/

/-- A finite partial vertex relabeling extends to a permutation of `VertexId`: fix `S`, send the finite
injective family `src` to the finite injective family `dst`, both disjoint from `S`.  Re-derived clean from
Mathlib primitives (mirrors body-635's `stableRemnant_finite_visible_star_permutation`) — no divergence
class. -/
private theorem stableTwoStage_finite_visible_star_permutation
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

/-- **body-639c (Step 1) — the global correcting-permutation existence.**  Fed body-639b's four points
DIRECTLY: source = the final two-stage stars (injective, fresh), target = the one-stage outer stars (injective,
fresh); fixed on the two-stage surviving roots.  Direction: `final two-stage star ──τ──▶ one-stage outer
star`. -/
theorem stableTwoStageTau_exists (s : StablePhi4MixedSplitChoice G hSt) :
    ∃ τ : Equiv.Perm VertexId,
      (∀ v, v ∈ stableTwoStageSurvivingVertices s → τ v = v) ∧
      ∀ γ : StableOuterComponent s,
        τ (stableFinalTwoStageStar s γ) = stableOneStageOuterStar s γ :=
  stableTwoStage_finite_visible_star_permutation
    (stableTwoStageSurvivingVertices s)
    (stableFinalTwoStageStar s)
    (stableOneStageOuterStar s)
    (stableFinalTwoStageStar_injective s)
    (stableOneStageOuterStar_injective s)
    (stableFinalTwoStageStar_not_mem_survivors s)
    (stableOneStageOuterStar_not_mem_survivors s)

/-- **body-639c (Step 1) — the single global correcting permutation** `τ`.  Sends every final two-stage star to
the corresponding one-stage outer star, fixing the surviving roots.  Built INDEPENDENTLY from body-639b's four
points — NOT a composition of the local `stableRemnantTau`. -/
noncomputable def stableTwoStageTau (s : StablePhi4MixedSplitChoice G hSt) : Equiv.Perm VertexId :=
  (stableTwoStageTau_exists s).choose

/-! ## Step 2 — τ's two action laws -/

/-- **body-639c (Step 2) — τ fixes the two-stage surviving roots.** -/
theorem stableTwoStageTau_of_survivor (s : StablePhi4MixedSplitChoice G hSt)
    {v : VertexId} (hv : v ∈ stableTwoStageSurvivingVertices s) :
    stableTwoStageTau s v = v :=
  (stableTwoStageTau_exists s).choose_spec.1 v hv

/-- **body-639c (Step 2) — τ sends the final two-stage star to the one-stage outer star.**  This is the ONLY
coordinate correction used in the composition law. -/
theorem stableTwoStageTau_finalStar (s : StablePhi4MixedSplitChoice G hSt)
    (γ : StableOuterComponent s) :
    stableTwoStageTau s (stableFinalTwoStageStar s γ) = stableOneStageOuterStar s γ :=
  (stableTwoStageTau_exists s).choose_spec.2 γ

/-! ## Step 3 — route ownership (where the two-stage retarget intermediate point lands) -/

/-- **body-639c (Step 3, SURVIVOR) — an outer-outside root is fixed by BOTH contraction stages.**  Such a `v`
lies outside `stableSelectedOuter` (first stage fixes it) and outside the quotient forest (a survivor component
sits inside `s.1.outer`; a remnant vertex is either an `s.1.outer`-vertex or a fresh promoted star), so the
second stage fixes it too. -/
theorem stableTwoStage_route_survivor (s : StablePhi4MixedSplitChoice G hSt)
    {v : VertexId} (hvG : v ∈ G.vertices) (hvOut : v ∉ s.1.outer.vertices) :
    (stableQuotientForest s).retargetVertex
        (phi4WTriplePrimeCanonicalSupply.starOf (stableSelectedOuterContractGraph s.1)
          (stableQuotientForest s))
        ((stableSelectedOuter s.1).retargetVertex
          (phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1)) v)
      = v := by
  have hvA : v ∉ (stableSelectedOuter s.1).vertices :=
    fun hc => hvOut (stableSelectedOuter_vertices_subset_outer s hc)
  rw [(stableSelectedOuter s.1).retargetVertex_of_not_mem _ hvA]
  apply (stableQuotientForest s).retargetVertex_of_not_mem
  intro hmem
  obtain ⟨δ, hδ, hvδ⟩ := ResolvedAdmissibleSubgraph.mem_vertices.mp hmem
  rcases stableQuotientForest_element_cases s hδ with ⟨g, hgR, rfl⟩ | ⟨o, rfl⟩
  · rw [stableRightSurvivor_vertices] at hvδ
    exact hvOut (ResolvedAdmissibleSubgraph.mem_vertices.mpr ⟨g, hgR.choose, hvδ⟩)
  · rcases stableRemnant_origin o hvδ with hvγF | ⟨δ0, hδ0, hveq⟩
    · exact hvOut (ResolvedAdmissibleSubgraph.mem_vertices.mpr ⟨o.γ.1, o.γ.2, hvγF⟩)
    · exact stableRemnant_gen_star_not_mem (stableSelectedOuter s.1)
        (stableSelectedOuter_isProperForest s.1)
        (stableRemnant_promoted_mem o hδ0) (hveq ▸ hvG)

/-- **body-639c (Step 3, LEFT) — the second stage fixes a LEFT first-stage star.**  For a LEFT-chosen outer
component `γ` and `v ∈ γ.vertices`, the first stage sends `v` to `γ`'s `stableSelectedOuter` star — a `Q`
star-vertex that is OUTSIDE the quotient forest (fresh vs. survivors; and a landing in a remnant would force `v`
into a distinct-owner forest component, contradicting outer disjointness), so the second stage fixes it. -/
theorem stableTwoStage_route_left (s : StablePhi4MixedSplitChoice G hSt)
    (γ : StableOuterComponent s)
    (hc : s.1.choice γ (Finset.mem_attach _ γ) = Sum.inl true)
    {v : VertexId} (hv : v ∈ γ.1.vertices) :
    (stableQuotientForest s).retargetVertex
        (phi4WTriplePrimeCanonicalSupply.starOf (stableSelectedOuterContractGraph s.1)
          (stableQuotientForest s))
        ((stableSelectedOuter s.1).retargetVertex
          (phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1)) v)
      = stableFinalTwoStageStar s γ := by
  have hγA : γ.1 ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G
      (stableSelectedOuter s.1) := stableOuterComponent_mem_selectedOuter_of_left s γ hc
  have h1 : (stableSelectedOuter s.1).retargetVertex
        (phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1)) v
      = phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1) γ.1 :=
    stableRemnant_retargetVertex_eq_star (stableSelectedOuter s.1) _ hγA hv
  rw [h1, stableFinalTwoStageStar_left s γ hc]
  apply (stableQuotientForest s).retargetVertex_of_not_mem
  intro hmem
  obtain ⟨δ, hδ, hstarδ⟩ := ResolvedAdmissibleSubgraph.mem_vertices.mp hmem
  have hvG : v ∈ G.vertices := γ.1.vertices_subset hv
  rcases stableQuotientForest_element_cases s hδ with ⟨g, hgR, rfl⟩ | ⟨o, rfl⟩
  · rw [stableRightSurvivor_vertices] at hstarδ
    exact stableRemnant_gen_star_not_mem (stableSelectedOuter s.1)
      (stableSelectedOuter_isProperForest s.1) hγA (g.vertices_subset hstarδ)
  · rw [← h1] at hstarδ
    have hvoγ : v ∈ o.γ.1.vertices := (stableRemnant_phi_mem_Ltau_iff o hvG).mp hstarδ
    have hne : γ.1 ≠ o.γ.1 := by
      intro heq
      have hγo : (γ : StableOuterComponent s) = o.γ := Subtype.ext heq
      subst hγo
      exact absurd (hc.symm.trans o.hchoice) (by simp)
    exact Finset.disjoint_left.mp (s.1.outer.pairwiseDisjoint γ.2 o.γ.2 hne) hv hvoγ

/-- **body-639c (Step 3, RIGHT) — the first-stage coordinate lands in the matching survivor.**  For a
RIGHT-chosen outer component `γ` and `v ∈ γ.vertices`, the first stage keeps `v` inside `γ = stableRightSurvivor`
(disjoint from `stableSelectedOuter`), so the second stage sends it to the RIGHT survivor's canonical
quotient-forest star — the final two-stage star. -/
theorem stableTwoStage_route_right (s : StablePhi4MixedSplitChoice G hSt)
    (γ : StableOuterComponent s)
    (hc : s.1.choice γ (Finset.mem_attach _ γ) = Sum.inl false)
    {v : VertexId} (hv : v ∈ γ.1.vertices) :
    (stableQuotientForest s).retargetVertex
        (phi4WTriplePrimeCanonicalSupply.starOf (stableSelectedOuterContractGraph s.1)
          (stableQuotientForest s))
        ((stableSelectedOuter s.1).retargetVertex
          (phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1)) v)
      = stableFinalTwoStageStar s γ := by
  have hγR : stableIsRightComponent s.1 γ.1 := ⟨γ.2, hc⟩
  have hdisj : Disjoint γ.1.vertices (stableSelectedOuter s.1).vertices :=
    stableRightComponent_disjoint_selectedOuter s.1 hγR
  have hmem : (stableSelectedOuter s.1).retargetVertex
        (phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1)) v
      ∈ (stableRightSurvivor s.1 (⟨γ.2, hc⟩ : stableIsRightComponent s.1 γ.1)).vertices := by
    rw [stableRightSurvivor_vertices]
    exact (stableRetargetVertex_mem_iff s.1 hdisj v).mpr hv
  rw [stableRemnant_retargetVertex_eq_star (stableQuotientForest s) _
        (stableFinalRightSurvivor_mem_quotientForest s γ hc) hmem,
      stableFinalTwoStageStar_right s γ hc]

/-- **body-639c (Step 3, FOREST) — the first-stage coordinate lands in the matching remnant.**  For a
FOREST-chosen outer component `γ` (inner forest `B`) and `v ∈ γ.vertices`, the first stage sends `v` into the
decompleted remnant `stableRemnantComponent ⟨γ, B, hc⟩` — routed by the REMNANT MEMBERSHIP characterization
`stableRemnant_phi_mem_Ltau_iff` ONLY (NOTHING from the local `stableRemnantTau`) — so the second stage sends it
to the remnant's canonical quotient-forest star, the final two-stage star. -/
theorem stableTwoStage_route_forest (s : StablePhi4MixedSplitChoice G hSt)
    (γ : StableOuterComponent s) (B : StableLocalForestIdx γ.1)
    (hc : s.1.choice γ (Finset.mem_attach _ γ) = Sum.inr B)
    {v : VertexId} (hv : v ∈ γ.1.vertices) :
    (stableQuotientForest s).retargetVertex
        (phi4WTriplePrimeCanonicalSupply.starOf (stableSelectedOuterContractGraph s.1)
          (stableQuotientForest s))
        ((stableSelectedOuter s.1).retargetVertex
          (phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1)) v)
      = stableFinalTwoStageStar s γ := by
  have hvG : v ∈ G.vertices := γ.1.vertices_subset hv
  have hmem : (stableSelectedOuter s.1).retargetVertex
        (phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1)) v
      ∈ (stableRemnantComponent (⟨γ, B, hc⟩ : StableForestChoiceOccurrence s)).vertices := by
    rw [stableRemnantComponent_vertices]
    exact (stableRemnant_phi_mem_Ltau_iff (⟨γ, B, hc⟩ : StableForestChoiceOccurrence s) hvG).mpr hv
  rw [stableRemnant_retargetVertex_eq_star (stableQuotientForest s) _
        (stableRemnantComponent_mem_quotientForest s ⟨γ, B, hc⟩) hmem,
      stableFinalTwoStageStar_forest s γ B hc]

/-! ## Step 4 — branchwise composition (`stableTwoStageTau_finalStar` the ONLY coordinate correction) -/

/-- **body-639c (Step 4, LEFT) — the τ-corrected two-stage retarget equals the outer retarget** on a LEFT
component. -/
theorem stableTwoStage_retarget_of_left (s : StablePhi4MixedSplitChoice G hSt)
    (γ : StableOuterComponent s)
    (hc : s.1.choice γ (Finset.mem_attach _ γ) = Sum.inl true)
    {v : VertexId} (hv : v ∈ γ.1.vertices) :
    stableTwoStageTau s
        ((stableQuotientForest s).retargetVertex
          (phi4WTriplePrimeCanonicalSupply.starOf (stableSelectedOuterContractGraph s.1)
            (stableQuotientForest s))
          ((stableSelectedOuter s.1).retargetVertex
            (phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1)) v))
      = s.1.outer.retargetVertex (phi4WTriplePrimeCanonicalSupply.starOf G s.1.outer) v := by
  rw [stableTwoStage_route_left s γ hc hv, stableTwoStageTau_finalStar s γ]
  show phi4WTriplePrimeCanonicalSupply.starOf G s.1.outer γ.1 = _
  rw [← stableRemnant_retargetVertex_eq_star s.1.outer
        (phi4WTriplePrimeCanonicalSupply.starOf G s.1.outer) γ.2 hv]

/-- **body-639c (Step 4, RIGHT) — the τ-corrected two-stage retarget equals the outer retarget** on a RIGHT
component. -/
theorem stableTwoStage_retarget_of_right (s : StablePhi4MixedSplitChoice G hSt)
    (γ : StableOuterComponent s)
    (hc : s.1.choice γ (Finset.mem_attach _ γ) = Sum.inl false)
    {v : VertexId} (hv : v ∈ γ.1.vertices) :
    stableTwoStageTau s
        ((stableQuotientForest s).retargetVertex
          (phi4WTriplePrimeCanonicalSupply.starOf (stableSelectedOuterContractGraph s.1)
            (stableQuotientForest s))
          ((stableSelectedOuter s.1).retargetVertex
            (phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1)) v))
      = s.1.outer.retargetVertex (phi4WTriplePrimeCanonicalSupply.starOf G s.1.outer) v := by
  rw [stableTwoStage_route_right s γ hc hv, stableTwoStageTau_finalStar s γ]
  show phi4WTriplePrimeCanonicalSupply.starOf G s.1.outer γ.1 = _
  rw [← stableRemnant_retargetVertex_eq_star s.1.outer
        (phi4WTriplePrimeCanonicalSupply.starOf G s.1.outer) γ.2 hv]

/-- **body-639c (Step 4, FOREST) — the τ-corrected two-stage retarget equals the outer retarget** on a FOREST
component. -/
theorem stableTwoStage_retarget_of_forest (s : StablePhi4MixedSplitChoice G hSt)
    (γ : StableOuterComponent s) (B : StableLocalForestIdx γ.1)
    (hc : s.1.choice γ (Finset.mem_attach _ γ) = Sum.inr B)
    {v : VertexId} (hv : v ∈ γ.1.vertices) :
    stableTwoStageTau s
        ((stableQuotientForest s).retargetVertex
          (phi4WTriplePrimeCanonicalSupply.starOf (stableSelectedOuterContractGraph s.1)
            (stableQuotientForest s))
          ((stableSelectedOuter s.1).retargetVertex
            (phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1)) v))
      = s.1.outer.retargetVertex (phi4WTriplePrimeCanonicalSupply.starOf G s.1.outer) v := by
  rw [stableTwoStage_route_forest s γ B hc hv, stableTwoStageTau_finalStar s γ]
  show phi4WTriplePrimeCanonicalSupply.starOf G s.1.outer γ.1 = _
  rw [← stableRemnant_retargetVertex_eq_star s.1.outer
        (phi4WTriplePrimeCanonicalSupply.starOf G s.1.outer) γ.2 hv]

/-- **body-639c (Step 4, SURVIVOR) — the τ-corrected two-stage retarget equals the outer retarget** on an
outer-outside surviving root (both stages and `τ` fix it). -/
theorem stableTwoStage_retarget_of_survivor (s : StablePhi4MixedSplitChoice G hSt)
    {v : VertexId} (hvG : v ∈ G.vertices) (hvOut : v ∉ s.1.outer.vertices) :
    stableTwoStageTau s
        ((stableQuotientForest s).retargetVertex
          (phi4WTriplePrimeCanonicalSupply.starOf (stableSelectedOuterContractGraph s.1)
            (stableQuotientForest s))
          ((stableSelectedOuter s.1).retargetVertex
            (phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1)) v))
      = s.1.outer.retargetVertex (phi4WTriplePrimeCanonicalSupply.starOf G s.1.outer) v := by
  rw [stableTwoStage_route_survivor s hvG hvOut,
      stableTwoStageTau_of_survivor s
        (show v ∈ stableTwoStageSurvivingVertices s from Finset.mem_sdiff.mpr ⟨hvG, hvOut⟩),
      s.1.outer.retargetVertex_of_not_mem _ hvOut]

/-! ## Step 5 — HEADLINE: the two-stage retarget composition coordinate law -/

/-- **body-639c (Step 5, HEADLINE) — the two-stage retarget composition coordinate law.**  For every ambient
vertex `v ∈ G.vertices`, correcting the composed two-stage contraction retarget (first `stableSelectedOuter`, then
the quotient forest on `Q`) by the single global permutation `τ = stableTwoStageTau` reproduces the one-stage
`s.1.outer` retarget.  The proof dispatches on whether `v` sits in an outer component (LEFT / RIGHT / FOREST via
the choice tag) or is a surviving root (`v ∉ s.1.outer.vertices`); `stableTwoStageTau_finalStar` supplies the
ONLY coordinate correction, and NO strict canonical-star equality is claimed. -/
theorem stableTwoStage_retarget_comp (s : StablePhi4MixedSplitChoice G hSt)
    {v : VertexId} (hv : v ∈ G.vertices) :
    stableTwoStageTau s
        ((stableQuotientForest s).retargetVertex
          (phi4WTriplePrimeCanonicalSupply.starOf (stableSelectedOuterContractGraph s.1)
            (stableQuotientForest s))
          ((stableSelectedOuter s.1).retargetVertex
            (phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1)) v))
      = s.1.outer.retargetVertex (phi4WTriplePrimeCanonicalSupply.starOf G s.1.outer) v := by
  by_cases hvOut : v ∈ s.1.outer.vertices
  · obtain ⟨c, hc, hvc⟩ := ResolvedAdmissibleSubgraph.mem_vertices.mp hvOut
    cases hcase : s.1.choice (⟨c, hc⟩ : StableOuterComponent s)
        (Finset.mem_attach _ (⟨c, hc⟩ : StableOuterComponent s)) with
    | inl b =>
      cases b with
      | true => exact stableTwoStage_retarget_of_left s ⟨c, hc⟩ hcase hvc
      | false => exact stableTwoStage_retarget_of_right s ⟨c, hc⟩ hcase hvc
    | inr B => exact stableTwoStage_retarget_of_forest s ⟨c, hc⟩ B hcase hvc
  · exact stableTwoStage_retarget_of_survivor s hv hvOut

end GaugeGeometry.QFT.Combinatorial
