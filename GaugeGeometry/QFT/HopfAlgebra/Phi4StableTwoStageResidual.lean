import GaugeGeometry.QFT.HopfAlgebra.Phi4StableRightFactorAggregate

/-!
# QFT-R1-body-639a — the STABLE two-stage EXACT RESIDUAL (first sub-body of the `quot_eq` campaign)

The stable two-stage quotient class equality (`quot_eq`) is the stable-carrier version of the abstract R-4-full
`contract_class_eq` campaign (bodies 511–529, ~18 files); it does NOT fit one body. It is split into
639a–639d, each an independent verification unit:
* **639a (THIS FILE)** — the EXACT residual geometry (upgrades body-637's `≤` to `=`) by Multiset owner
  classification, NO card-only weakening, NO retarget-injectivity assumption. Delivered here:
  `stableSelectedOuter_add_residual_eq_outer` (the exact additive owner identity
  `A.internalEdges + (baseRight + baseForest) = outer.internalEdges`) and `stableOuter_residual_eq`
  (`outer.internalEdges − A.internalEdges = baseRight + baseForest`, an exact Multiset `Eq`), plus the two
  fixed graphs `stableOneStageRightGraph` / `stableTwoStageRightGraph` (Step 1) and a `private`
  correcting-permutation engine for the later sub-bodies.
* **639b** (`Phi4StableTwoStageStars.lean`) — final-star ownership: `stableFinalTwoStageStar` + sector/cross
  injectivity + LEFT-vs-second-stage disjointness + surviving-root freshness + the global target-star injectivity.
* **639c** (`Phi4StableTwoStageRetarget.lean`) — the single global correcting permutation `stableTwoStageTau`
  + the retarget composition coordinate law `τ (retarget₂ (retarget₁ v)) = retargetOuter v`.
* **639d** (`Phi4StableTwoStageQuotientEq.lean`) — the RAW graph equality, the class equality
  `stableTwoStage_contract_class_eq`, and the HEADLINE third factor `stableForestRightTerm_outer_eq_quotientForest`.

Because the stable carrier keeps inherited legs VERBATIM (no re-encode), only vertex-coordinate differences
need the correcting permutation — so the residual here is EXACT (not the mapPerm-orbit no-go of body-625).

## HALT / red lines (639a scope: exact residual only)
NOT entered here (they belong to 639b–639d): the star classifier / final star; the global permutation
`stableTwoStageTau`; the retarget composition law; any class / rightTerm equality.

## HALT / red lines
STRICT canonical-star equality is PERMANENTLY FORBIDDEN — we never claim `stableTwoStageTau = stableRemnantTau`;
only ACTION agreement is proved.  NO polluted abstract contract-twice supply is consumed; summand agreement /
`sum_bij` / alpha / coassoc are NOT entered.  Step 2 is an EXACT Multiset `Eq` (owner count, no card / `toFinset`
/ dedup).  ZERO new `structure` / `class` / permanent `instance` (one file-local `local instance` for the φ⁴
family; the perm engine is `private`); ZERO forbidden divergence class in any declaration TYPE; ZERO
`sorry` / `admit` / `native_decide`; NO `HEq` / `cast` / graph-data `▸` (Prop-membership `▸` only).  Body-625's
no-go and bodies 629-638 / the old carrier are UNEDITED.  Axiom-clean (`propext`, `Classical.choice`,
`Quot.sound`).
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

open ResolvedFeynmanSubgraph

variable {G : ResolvedFeynmanGraph}

set_option maxHeartbeats 3200000

/-- The concrete φ⁴ divergence measure family, registered file-locally (providable instance, NO forbidden
class). -/
noncomputable local instance instPhi4DivergenceMeasureFamily639 : (H : FeynmanGraph) → DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

variable {hSt : StableResolvedBoundaryIds G} {s : StablePhi4MixedSplitChoice G hSt}

/-! ## Step 0 — the correcting-permutation engine (Mathlib-only, re-derived clean, `private`) -/

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

/-! ## Step 1 — the two fixed graphs -/

/-- **body-639 (Step 1) — the one-stage right graph.**  `s.1.outer` star-contracted to its canonical stars. -/
noncomputable def stableOneStageRightGraph (s : StablePhi4MixedSplitChoice G hSt) : ResolvedFeynmanGraph :=
  s.1.outer.contractWithStars (phi4WTriplePrimeCanonicalSupply.starOf G s.1.outer)

/-- **body-639 (Step 1) — the two-stage right graph.**  The live quotient forest star-contracted on the stable
quotient ambient `Q`. -/
noncomputable def stableTwoStageRightGraph (s : StablePhi4MixedSplitChoice G hSt) : ResolvedFeynmanGraph :=
  (stableQuotientForest s).contractWithStars
    (phi4WTriplePrimeCanonicalSupply.starOf (stableSelectedOuterContractGraph s.1) (stableQuotientForest s))

/-! ## Step 2 — the EXACT residual geometry (upgrades body-637's `≤` to `=`).

Let `A := stableSelectedOuter s.1`, `rA := A.retargetEdge (starOf G A)`, `R := s.1.outer.internalEdges − A.internalEdges`.
The proof is an owner-tagged additive Multiset identity (NO card weakening, NO retarget injectivity):
`A.internalEdges + (baseRight + baseForest) = s.1.outer.internalEdges`, with `baseRight`/`baseForest` the RIGHT /
inner-FOREST-complement residual sums; then `qF.internalEdges = baseRight + baseForest.map rA = R.map rA`. -/

/-- **body-639 (Step 2) — the RIGHT-sector residual** (a Multiset over `G`-edges, owner-indexed): the internal
edges of the RIGHT-chosen (`Sum.inl false`) outer components, `0` elsewhere. -/
noncomputable def stableBaseRightResidual (s : StablePhi4MixedSplitChoice G hSt) : Multiset ResolvedFeynmanEdge :=
  ∑ a ∈ s.1.outer.elements.attach,
    (s.1.choice a (Finset.mem_attach _ a)).elim
      (fun b => bif b then (0 : Multiset ResolvedFeynmanEdge) else a.1.internalEdges)
      (fun _ => (0 : Multiset ResolvedFeynmanEdge))

/-- **body-639 (Step 2) — the inner-FOREST-complement residual** (a Multiset over `G`-edges, owner-indexed): the
inner-forest complement edges of the FOREST-chosen (`Sum.inr B`) outer components, `0` elsewhere. -/
noncomputable def stableBaseForestResidual (s : StablePhi4MixedSplitChoice G hSt) : Multiset ResolvedFeynmanEdge :=
  ∑ a ∈ s.1.outer.elements.attach,
    (s.1.choice a (Finset.mem_attach _ a)).elim
      (fun _ => (0 : Multiset ResolvedFeynmanEdge))
      (fun B => B.1.complementEdges)

/-- The promoted forest's internal edges, summed per outer component (0 off the FOREST sector, `B.internalEdges`
on it).  Via `sum_biUnion` on the promoted images (pairwise disjoint) + per-owner `sum_image`. -/
theorem stablePromotedOf_internalEdges_eq_sum (s : StablePhi4MixedSplitChoice G hSt) :
    (stablePromotedOf s.1).internalEdges
      = ∑ a ∈ s.1.outer.elements.attach,
          (s.1.choice a (Finset.mem_attach _ a)).elim
            (fun _ => (0 : Multiset ResolvedFeynmanEdge))
            (fun B => B.1.internalEdges) := by
  show (stablePromotedOf s.1).elements.sum (fun c => c.internalEdges) = _
  rw [stablePromotedOf_elements]
  rw [Finset.sum_biUnion]
  · refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [stablePromotedElemsAt]
    cases hc : s.1.choice a (Finset.mem_attach _ a) with
    | inl b =>
      simp only [Sum.elim_inl, Finset.sum_empty]
    | inr B =>
      simp only [Sum.elim_inr]
      rw [Finset.sum_image (fun δ₁ h₁ δ₂ h₂ h =>
        stableRootRelativeInner_injOn_elements a.1 B.1
          ((mem_phi4WTriplePrimeIndex _ B.1).mp B.2).2.2.2.2.1.2.1
          (Finset.mem_coe.mpr h₁) (Finset.mem_coe.mpr h₂) h)]
      show (@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily
            (stableLocalBoundaryCompletedGraph a.1) B.1).sum
            (fun δ => (stableRootRelativeInner a.1 δ).internalEdges) = B.1.internalEdges
      rw [Finset.sum_congr rfl (fun δ _ => stableRootRelativeInner_internalEdges a.1 δ)]
      rfl
  · -- pairwise disjoint promoted images
    intro a₁ _ a₂ _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro c hc₁ hc₂
    rw [mem_stablePromotedElemsAt] at hc₁ hc₂
    obtain ⟨B₁, _, δ₁, hδ₁, rfl⟩ := hc₁
    obtain ⟨B₂, _, δ₂, hδ₂, hce⟩ := hc₂
    have ha : a₁.1 ≠ a₂.1 := fun h => hne (Subtype.ext h)
    have hdd : a₁.1.Disjoint a₂.1 := s.1.outer.pairwiseDisjoint a₁.2 a₂.2 ha
    have hBproper₁ : B₁.1.IsProperForest := ((mem_phi4WTriplePrimeIndex _ B₁.1).mp B₁.2).2.2.2.2.1
    obtain ⟨u, hu⟩ := Finset.card_pos.mp (hBproper₁.2.1 δ₁ hδ₁)
    have hu1 : u ∈ a₁.1.vertices :=
      stableRootRelativeInner_vertices_subset a₁.1 δ₁
        (by rw [stableRootRelativeInner_vertices]; exact hu)
    have hu2 : u ∈ a₂.1.vertices :=
      stableRootRelativeInner_vertices_subset a₂.1 δ₂
        (hce ▸ (by rw [stableRootRelativeInner_vertices]; exact hu))
    exact Finset.disjoint_left.mp hdd hu1 hu2

/-- The LEFT-selected forest's internal edges, summed per outer component (`a.internalEdges` on the LEFT
sector, 0 elsewhere). -/
theorem stableLeftOf_internalEdges_eq_sum (s : StablePhi4MixedSplitChoice G hSt) :
    (stableLeftOf s.1).internalEdges
      = ∑ a ∈ s.1.outer.elements.attach,
          (s.1.choice a (Finset.mem_attach _ a)).elim
            (fun b => bif b then a.1.internalEdges else (0 : Multiset ResolvedFeynmanEdge))
            (fun _ => (0 : Multiset ResolvedFeynmanEdge)) := by
  have h1 : (stableLeftOf s.1).internalEdges
      = ∑ a ∈ s.1.outer.elements.attach,
          (if stableLeftPred s.1 a.1 then a.1.internalEdges else 0) := by
    show (s.1.outer.elements.filter (stableLeftPred s.1)).sum (fun c => c.internalEdges) = _
    rw [Finset.sum_filter]
    exact (Finset.sum_attach s.1.outer.elements
      (fun c => if stableLeftPred s.1 c then c.internalEdges else 0)).symm
  rw [h1]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  cases hc : s.1.choice a (Finset.mem_attach _ a) with
  | inl b =>
    cases b with
    | false =>
      simp only [Sum.elim_inl, cond_false]
      rw [if_neg]
      intro hlp
      obtain ⟨h', hlt⟩ := hlp
      rw [hc] at hlt; simp at hlt
    | true =>
      simp only [Sum.elim_inl, cond_true]
      rw [if_pos ⟨a.2, hc⟩]
  | inr B =>
    simp only [Sum.elim_inr]
    rw [if_neg]
    intro hlp
    obtain ⟨h', hlt⟩ := hlp
    rw [hc] at hlt; simp at hlt

/-- `stableSelectedOuter`'s internal edges split into the LEFT and PROMOTED forests' (Finset-disjoint elements:
a LEFT component sits in `s.1.outer`, a promoted lift sits inside a distinct FOREST component). -/
theorem stableSelectedOuter_internalEdges_eq_union (s : StablePhi4MixedSplitChoice G hSt) :
    (stableSelectedOuter s.1).internalEdges
      = (stableLeftOf s.1).internalEdges + (stablePromotedOf s.1).internalEdges := by
  have hdisj : Disjoint (stableLeftOf s.1).elements (stablePromotedOf s.1).elements := by
    rw [Finset.disjoint_left]
    intro c hcL hcP
    rw [stableLeftOf_elements, Finset.mem_filter] at hcL
    obtain ⟨hcOuter, hcleft⟩ := hcL
    rw [stablePromotedOf_elements, Finset.mem_biUnion] at hcP
    obtain ⟨a, -, hca⟩ := hcP
    rw [mem_stablePromotedElemsAt] at hca
    obtain ⟨B, hchoice, δ, hδ, hce⟩ := hca
    have hBproper : B.1.IsProperForest := ((mem_phi4WTriplePrimeIndex _ B.1).mp B.2).2.2.2.2.1
    obtain ⟨u, hu⟩ := Finset.card_pos.mp (hBproper.2.1 δ hδ)
    have huc : u ∈ c.vertices := by rw [hce, stableRootRelativeInner_vertices]; exact hu
    by_cases hEq : c = a.1
    · subst hEq
      obtain ⟨h, hct⟩ := hcleft
      have hsub : (⟨a.1, h⟩ :
          {x // x ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G s.1.outer}) = a :=
        Subtype.ext rfl
      have hchoicea : s.1.choice a (Finset.mem_attach _ a) = Sum.inl true := hsub ▸ hct
      exact absurd (hchoicea.symm.trans hchoice) (by simp)
    · have hdd : c.Disjoint a.1 := s.1.outer.pairwiseDisjoint hcOuter a.2 hEq
      have hua : u ∈ a.1.vertices := by
        rw [hce] at huc; exact stableRootRelativeInner_vertices_subset a.1 δ huc
      exact Finset.disjoint_left.mp hdd huc hua
  show (stableSelectedOuter s.1).elements.sum (fun c => c.internalEdges)
      = (stableLeftOf s.1).elements.sum (fun c => c.internalEdges)
        + (stablePromotedOf s.1).elements.sum (fun c => c.internalEdges)
  rw [stableSelectedOuter_elements]
  exact Finset.sum_union hdisj

/-- **body-639 (Step 2, owner identity) — the additive owner decomposition.**  Every outer component's internal
edges split as its `stableSelectedOuter`-contribution (LEFT: itself; FOREST: the inner forest `B`) plus its
residual contribution (RIGHT: itself; FOREST: the inner complement).  Summed over `s.1.outer`, this is the exact
`A + residual = outer` identity — NO card weakening, NO retarget injectivity. -/
theorem stableSelectedOuter_add_residual_eq_outer (s : StablePhi4MixedSplitChoice G hSt) :
    (stableSelectedOuter s.1).internalEdges
        + (stableBaseRightResidual s + stableBaseForestResidual s)
      = s.1.outer.internalEdges := by
  rw [stableSelectedOuter_internalEdges_eq_union, stableLeftOf_internalEdges_eq_sum,
    stablePromotedOf_internalEdges_eq_sum, stableBaseRightResidual, stableBaseForestResidual]
  have hOut : s.1.outer.internalEdges
      = ∑ a ∈ s.1.outer.elements.attach, a.1.internalEdges := by
    show s.1.outer.elements.sum (fun c => c.internalEdges) = _
    exact (Finset.sum_attach s.1.outer.elements (fun c => c.internalEdges)).symm
  rw [hOut, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  cases hc : s.1.choice a (Finset.mem_attach _ a) with
  | inl b =>
    cases b with
    | false => simp only [Sum.elim_inl, cond_false, add_zero, zero_add]
    | true => simp only [Sum.elim_inl, cond_true, add_zero]
  | inr B =>
    simp only [Sum.elim_inr, zero_add, add_zero]
    have hBle : B.1.internalEdges ≤ a.1.internalEdges := by
      have h := phi4WTriplePrime_internalEdges_le_of_components_le B.1
        (fun c _ => c.internalEdges_le)
      rwa [stableLocalBoundaryCompletedGraph_internalEdges] at h
    have hcompl : B.1.complementEdges
        = a.1.internalEdges - B.1.internalEdges := by
      show (stableLocalBoundaryCompletedGraph a.1).internalEdges - B.1.internalEdges = _
      rw [stableLocalBoundaryCompletedGraph_internalEdges]
    rw [hcompl, add_tsub_cancel_of_le hBle]

/-- **body-639 (Step 2, exact residual) — the owner-decomposed input residual.**  `R = outer.internalEdges −
stableSelectedOuter.internalEdges` is EXACTLY the RIGHT-sector internal edges plus the inner-FOREST-complement
edges (an exact Multiset `Eq`, from the additive owner identity — NO card weakening). -/
theorem stableOuter_residual_eq (s : StablePhi4MixedSplitChoice G hSt) :
    s.1.outer.internalEdges - (stableSelectedOuter s.1).internalEdges
      = stableBaseRightResidual s + stableBaseForestResidual s := by
  rw [← stableSelectedOuter_add_residual_eq_outer s, add_tsub_cancel_left]

end GaugeGeometry.QFT.Combinatorial
