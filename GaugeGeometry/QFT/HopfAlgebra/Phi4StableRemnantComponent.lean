import GaugeGeometry.QFT.HopfAlgebra.Phi4StableRightSurvivor

/-!
# QFT-R1-body-635 — STABLE remnant decompletion + contract-twice raw equality

This body restores **not-all-LEFT** ownership on the STABLE split choice and builds the **decompleted stable
remnant** of a forest-chosen outer component, proving the genuine-decontraction HEADLINE on the STABLE carrier:
boundary-completing the decompleted stable remnant on the stable quotient `Q` reconstructs the local contracted
graph up to the per-occurrence correcting permutation `τ`.

```
stableLocalBoundaryCompletedGraph (stableRemnantComponent o) = (stableLocalContractGraph o).mapPerm τ
```

This is the STABLE mirror of body-604 — reproduced CLEAN on the stable carrier `stableLocalBoundaryCompletedGraph`
(ZERO re-encode: inherited leg IDs are kept VERBATIM, never `encodeExistingLeg`-re-encoded).  Body-604's
old-choice-keyed decls are NOT consumed; the argument is mirrored.

## Steps
* **Step 0a** — the correcting-permutation engine (Mathlib-only, reproduced clean, `private`).
* **Step 0b** — generic star reduction / freshness / injectivity / `retargetVertex_eq_star` (re-derived clean).
* **Step 1** — mixed-choice ownership `StablePhi4MixedSplitChoice` (`def`/subtype, NOT a structure): base owns
  not-all-RIGHT (`choice_nontrivial`), the subtype property owns not-all-LEFT.  `stableMixedChoice_not_all_right`
  / `_not_all_left`.
* **Step 2** — the FOREST occurrence owner `StableForestChoiceOccurrence` (the ONLY new `structure`) + accessors.
* **Step 3** — `stableLocalContractGraph` + the per-occurrence LOCAL correcting permutation `stableRemnantTau`
  (source: inner forest's local canonical stars; target: the global selectedOuter stars of the promoted lifts;
  FIXED on visible root vertices; source/target injectivity + freshness).  LOCAL τ only.
* **Step 4** — the decompleted stable remnant `stableRemnantComponent : ResolvedFeynmanSubgraph Q` (genuine
  `Q`-legs by filter, NEVER synthetic legs) + raw anchors.
* **Step 5** — exact external-leg reconstruction: `stableRemnant_genuineLegs_eq`,
  `stableRemnant_resolvedBoundaryEdges`, `stableRemnant_boundaryExternalLeg_retarget`,
  `stableRemnant_inheritedBoundaryLegs_eq`.  Inherited IDs VERBATIM (NO `encodeExistingLeg`).
* **Step 6 (HEADLINE)** — `stableRemnant_contractTwice`, a raw `ResolvedFeynmanGraph` equality (all three
  fields) + `stableRemnant_completed_class_eq` (τ-erasing class corollary).

## HALT / red lines
Body-625's no-go and bodies 629-634 / the old carrier are UNEDITED.  NO global correcting permutation
(per-occurrence τ only); NO old-choice / old-remnant (604) adapter consumed; NO cross-ambient homogeneous
subgraph equality; NO external residual hypothesis.  The remnant CD / saturation / edge-completeness (636),
remnantForest / quotientForest (636/637), the right-factor aggregate / `quot_eq` (638/639) are NOT entered;
NO quotient W‴ membership claim.  EXACTLY ONE new `structure` (`StableForestChoiceOccurrence`); ZERO new
`class` / permanent `instance` (one file-local `local instance` for the φ⁴ family); ZERO forbidden divergence
class in any declaration TYPE; ZERO `sorry` / `admit` / `native_decide`; NO `HEq` / `cast` / graph-data `▸`;
NO `toFinset` / dedup / orbit quotient.  Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

open ResolvedFeynmanSubgraph

variable {G : ResolvedFeynmanGraph}

set_option maxHeartbeats 3200000

/-- The concrete φ⁴ divergence measure family, registered file-locally (providable instance, NO forbidden
class). -/
noncomputable local instance instPhi4DivergenceMeasureFamily635 : (H : FeynmanGraph) → DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

/-! ## Step 0a — the correcting-permutation engine (Mathlib-only, reproduced clean) -/

/-- A finite partial vertex relabeling extends to a permutation of `VertexId`: fix `S`, send the finite
injective family `src` to the finite injective family `dst`, both disjoint from `S`.  Reproduced clean from
Mathlib primitives — no divergence class. -/
private theorem stableRemnant_finite_visible_star_permutation
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
theorem stableRemnant_gen_starOf_eq {H : ResolvedFeynmanGraph}
    (A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily H)
    (hpf : @ResolvedAdmissibleSubgraph.IsProperForest phi4DivergenceMeasureFamily H A)
    (δ : ResolvedFeynmanSubgraph H) :
    phi4WTriplePrimeCanonicalSupply.starOf H A δ = cleanStarOf phi4DivergenceMeasureFamily A hpf δ := by
  show cleanStarOfTotal phi4DivergenceMeasureFamily H A δ = _
  unfold cleanStarOfTotal
  rw [dif_pos hpf]

/-- Freshness: the canonical star lies outside the ambient's vertex set. -/
theorem stableRemnant_gen_star_not_mem {H : ResolvedFeynmanGraph}
    (A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily H)
    (hpf : @ResolvedAdmissibleSubgraph.IsProperForest phi4DivergenceMeasureFamily H A)
    {δ : ResolvedFeynmanSubgraph H} (hδ : δ ∈ A.elements) :
    phi4WTriplePrimeCanonicalSupply.starOf H A δ ∉ H.vertices := by
  rw [stableRemnant_gen_starOf_eq A hpf δ]
  exact cleanStarOf_not_mem_vertices A hpf hδ

/-- Injectivity of the canonical star on the forest's components. -/
theorem stableRemnant_gen_star_injOn {H : ResolvedFeynmanGraph}
    (A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily H)
    (hpf : @ResolvedAdmissibleSubgraph.IsProperForest phi4DivergenceMeasureFamily H A)
    {δ₁ : ResolvedFeynmanSubgraph H} (h₁ : δ₁ ∈ A.elements)
    {δ₂ : ResolvedFeynmanSubgraph H} (h₂ : δ₂ ∈ A.elements)
    (h : phi4WTriplePrimeCanonicalSupply.starOf H A δ₁
        = phi4WTriplePrimeCanonicalSupply.starOf H A δ₂) : δ₁ = δ₂ := by
  rw [stableRemnant_gen_starOf_eq A hpf δ₁, stableRemnant_gen_starOf_eq A hpf δ₂] at h
  exact cleanStarOf_injOn A hpf h₁ h₂ h

/-- A carrier vertex retargets to its element's star (clean re-derivation). -/
theorem stableRemnant_retargetVertex_eq_star {H : ResolvedFeynmanGraph}
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

/-! ## Step 1 — mixed-choice ownership (not-all-RIGHT and not-all-LEFT) -/

/-- **body-635 (Step 1) — mixed-choice ownership.**  A stable split choice whose base owns not-all-RIGHT
(`choice_nontrivial`) and whose subtype property owns not-all-LEFT.  A `def`/subtype, NOT a new structure. -/
def StablePhi4MixedSplitChoice (G : ResolvedFeynmanGraph) (hSt : StableResolvedBoundaryIds G) : Type :=
  { s : StablePhi4ResolvedSplitChoice G hSt //
      ∃ a hatt, s.choice a hatt ≠ Sum.inl true }

/-- **body-635 (Step 1) — the mixed choice owns not-all-RIGHT** (base `choice_nontrivial`). -/
theorem stableMixedChoice_not_all_right {hSt : StableResolvedBoundaryIds G}
    (s : StablePhi4MixedSplitChoice G hSt) :
    ∃ a hatt, s.1.choice a hatt ≠ Sum.inl false :=
  s.1.choice_nontrivial

/-- **body-635 (Step 1) — the mixed choice owns not-all-LEFT** (the subtype property). -/
theorem stableMixedChoice_not_all_left {hSt : StableResolvedBoundaryIds G}
    (s : StablePhi4MixedSplitChoice G hSt) :
    ∃ a hatt, s.1.choice a hatt ≠ Sum.inl true :=
  s.2

/-! ## Step 2 — the FOREST occurrence owner (the ONLY new structure) -/

/-- **body-635 (Step 2) — a forest-chosen outer component of a stable mixed split choice**, with its live
stable inner W‴ forest `B` carried explicitly (to sidestep the dependent codomain). -/
structure StableForestChoiceOccurrence {hSt : StableResolvedBoundaryIds G}
    (s : StablePhi4MixedSplitChoice G hSt) where
  /-- The outer component. -/
  γ : {x : ResolvedFeynmanSubgraph G //
        x ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G s.1.outer}
  /-- The live stable inner W‴ forest chosen at `γ`. -/
  B : StableLocalForestIdx γ.1
  /-- `s` chooses the inner forest `B` at `γ`. -/
  hchoice : s.1.choice γ (Finset.mem_attach _ γ) = Sum.inr B

variable {hSt : StableResolvedBoundaryIds G} {s : StablePhi4MixedSplitChoice G hSt}

/-- `B.1` (the stable inner forest) is a proper forest. -/
theorem stableForestOcc_B_isProperForest (o : StableForestChoiceOccurrence s) :
    @ResolvedAdmissibleSubgraph.IsProperForest phi4DivergenceMeasureFamily
      (stableLocalBoundaryCompletedGraph o.γ.1) o.B.1 :=
  ((mem_phi4WTriplePrimeIndex _ o.B.1).mp o.B.2).2.2.2.2.1

/-- Each inner component `δ ∈ B.1.elements` is externally-leg saturated on the stable inner ambient. -/
theorem stableForestOcc_B_saturated (o : StableForestChoiceOccurrence s)
    {δ : ResolvedFeynmanSubgraph (stableLocalBoundaryCompletedGraph o.γ.1)}
    (hδ : δ ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily
            (stableLocalBoundaryCompletedGraph o.γ.1) o.B.1) :
    ResolvedExternalLegSaturated (stableLocalBoundaryCompletedGraph o.γ.1) δ :=
  (((mem_phi4WTriplePrimeIndex _ o.B.1).mp o.B.2).2.2.2.2.2.1) δ hδ

/-- Each inner component `δ ∈ B.1.elements` is internal-edge complete on the stable inner ambient. -/
theorem stableForestOcc_B_edgeComplete (o : StableForestChoiceOccurrence s)
    {δ : ResolvedFeynmanSubgraph (stableLocalBoundaryCompletedGraph o.γ.1)}
    (hδ : δ ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily
            (stableLocalBoundaryCompletedGraph o.γ.1) o.B.1) :
    ResolvedInternalEdgeComplete δ :=
  (((mem_phi4WTriplePrimeIndex _ o.B.1).mp o.B.2).2.2.2.2.2.2) δ hδ

/-! ## Step 3 — the LOCAL contracted graph -/

/-- **body-635 (Step 3) — the LOCAL star-contraction of the stable inner forest `B.1`** on the stable inner
ambient `stableLocalBoundaryCompletedGraph γ.1`. -/
noncomputable def stableLocalContractGraph
    (o : StableForestChoiceOccurrence s) : ResolvedFeynmanGraph :=
  o.B.1.contractWithStars
    (phi4WTriplePrimeCanonicalSupply.starOf (stableLocalBoundaryCompletedGraph o.γ.1) o.B.1)

/-! ## Step 3b — promotion membership + rootRelativeInner injectivity -/

/-- A promoted stable inner component lands in `stableSelectedOuter`. -/
theorem stableRemnant_promoted_mem (o : StableForestChoiceOccurrence s)
    {δ : ResolvedFeynmanSubgraph (stableLocalBoundaryCompletedGraph o.γ.1)}
    (hδ : δ ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily
            (stableLocalBoundaryCompletedGraph o.γ.1) o.B.1) :
    stableRootRelativeInner o.γ.1 δ ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G
      (stableSelectedOuter s.1) := by
  rw [stableSelectedOuter_elements, Finset.mem_union]
  refine Or.inr ?_
  rw [stablePromotedOf_elements, Finset.mem_biUnion]
  refine ⟨o.γ, Finset.mem_attach _ _, ?_⟩
  rw [mem_stablePromotedElemsAt]
  exact ⟨o.B, o.hchoice, δ, hδ, rfl⟩

/-- `stableRootRelativeInner o.γ.1` is injective on `B.1.elements` (nonempty-component forest). -/
theorem stableRemnant_rootRelativeInner_injOn (o : StableForestChoiceOccurrence s)
    {δ₁ : ResolvedFeynmanSubgraph (stableLocalBoundaryCompletedGraph o.γ.1)}
    (h₁ : δ₁ ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily
            (stableLocalBoundaryCompletedGraph o.γ.1) o.B.1)
    {δ₂ : ResolvedFeynmanSubgraph (stableLocalBoundaryCompletedGraph o.γ.1)}
    (h₂ : δ₂ ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily
            (stableLocalBoundaryCompletedGraph o.γ.1) o.B.1)
    (h : stableRootRelativeInner o.γ.1 δ₁ = stableRootRelativeInner o.γ.1 δ₂) : δ₁ = δ₂ :=
  stableRootRelativeInner_injOn_elements o.γ.1 o.B.1
    ((stableForestOcc_B_isProperForest o).2.1) (Finset.mem_coe.mpr h₁) (Finset.mem_coe.mpr h₂) h

/-! ## Step 3c — the per-occurrence LOCAL correcting permutation τ -/

/-- The correcting-permutation existence for the stable remnant: fix the surviving inner-forest complement,
send each LOCAL star to the GLOBAL star of the corresponding promoted component.  Per-occurrence / LOCAL. -/
theorem stableRemnantTau_exists (o : StableForestChoiceOccurrence s) :
    ∃ τ : Equiv.Perm VertexId,
      (∀ v, v ∈ o.γ.1.vertices \ o.B.1.vertices → τ v = v) ∧
      (∀ i : {x // x ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily
                  (stableLocalBoundaryCompletedGraph o.γ.1) o.B.1},
        τ (phi4WTriplePrimeCanonicalSupply.starOf (stableLocalBoundaryCompletedGraph o.γ.1) o.B.1 i.1)
          = phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1)
              (stableRootRelativeInner o.γ.1 i.1)) := by
  have hpfB := stableForestOcc_B_isProperForest o
  have hpfSel := stableSelectedOuter_isProperForest s.1
  refine stableRemnant_finite_visible_star_permutation
    (ι := {x // x ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily
                  (stableLocalBoundaryCompletedGraph o.γ.1) o.B.1})
    (o.γ.1.vertices \ o.B.1.vertices)
    (fun i => phi4WTriplePrimeCanonicalSupply.starOf (stableLocalBoundaryCompletedGraph o.γ.1) o.B.1 i.1)
    (fun i => phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1)
        (stableRootRelativeInner o.γ.1 i.1))
    ?_ ?_ ?_ ?_
  · -- hsrcInj
    intro i j hij
    exact Subtype.ext (stableRemnant_gen_star_injOn o.B.1 hpfB i.2 j.2 hij)
  · -- hdstInj
    intro i j hij
    have := stableRemnant_gen_star_injOn (stableSelectedOuter s.1) hpfSel
      (stableRemnant_promoted_mem o i.2) (stableRemnant_promoted_mem o j.2) hij
    exact Subtype.ext (stableRemnant_rootRelativeInner_injOn o i.2 j.2 this)
  · -- hsrcS
    intro i hc
    exact stableRemnant_gen_star_not_mem o.B.1 hpfB i.2 (Finset.mem_sdiff.mp hc).1
  · -- hdstS
    intro i hc
    exact stableRemnant_gen_star_not_mem (stableSelectedOuter s.1) hpfSel
      (stableRemnant_promoted_mem o i.2)
      (o.γ.1.vertices_subset (Finset.mem_sdiff.mp hc).1)

/-- The per-occurrence LOCAL correcting permutation `τ` for the stable remnant. -/
noncomputable def stableRemnantTau (o : StableForestChoiceOccurrence s) : Equiv.Perm VertexId :=
  (stableRemnantTau_exists o).choose

theorem stableRemnantTau_fix (o : StableForestChoiceOccurrence s)
    {v : VertexId} (hv : v ∈ o.γ.1.vertices \ o.B.1.vertices) :
    stableRemnantTau o v = v :=
  (stableRemnantTau_exists o).choose_spec.1 v hv

theorem stableRemnantTau_map (o : StableForestChoiceOccurrence s)
    (i : {x // x ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily
            (stableLocalBoundaryCompletedGraph o.γ.1) o.B.1}) :
    stableRemnantTau o
        (phi4WTriplePrimeCanonicalSupply.starOf (stableLocalBoundaryCompletedGraph o.γ.1) o.B.1 i.1)
      = phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1)
          (stableRootRelativeInner o.γ.1 i.1) :=
  (stableRemnantTau_exists o).choose_spec.2 i

/-! ## Step 3d — origin cases for a stableSelectedOuter component -/

/-- Every `stableSelectedOuter` component is either disjoint from `γ` or is a `γ`-promotion. -/
theorem stableRemnant_selectedOuter_elt_cases (o : StableForestChoiceOccurrence s)
    {c : ResolvedFeynmanSubgraph G}
    (hc : c ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G
        (stableSelectedOuter s.1)) :
    _root_.Disjoint o.γ.1.vertices c.vertices ∨
      (∃ δ ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily
            (stableLocalBoundaryCompletedGraph o.γ.1) o.B.1, c = stableRootRelativeInner o.γ.1 δ) := by
  rcases stableSelectedOuter_component_origin s.1 hc with ⟨hcmem, hleft⟩ | hP
  · refine Or.inl ?_
    have hne : o.γ.1 ≠ c := by
      rintro rfl
      obtain ⟨h', hc_true⟩ := hleft
      exact absurd (hc_true.symm.trans o.hchoice) (by simp)
    exact s.1.outer.pairwiseDisjoint o.γ.2 hcmem hne
  · obtain ⟨γ', hγ', B', hchoice', δ', hδ', rfl⟩ := hP
    by_cases hγeq : γ' = o.γ.1
    · subst hγeq
      have hBeq : B' = o.B := Sum.inr.inj (hchoice'.symm.trans o.hchoice)
      exact Or.inr ⟨δ', hBeq ▸ hδ', rfl⟩
    · refine Or.inl ?_
      have hne : o.γ.1 ≠ γ' := fun h => hγeq h.symm
      have hdd : o.γ.1.Disjoint γ' := s.1.outer.pairwiseDisjoint o.γ.2 hγ' hne
      exact Finset.disjoint_of_subset_right
        (stableRootRelativeInner_vertices_subset γ' δ') hdd

/-- A `γ`-vertex outside the inner forest is outside `stableSelectedOuter`. -/
theorem stableRemnant_not_mem_selectedOuter (o : StableForestChoiceOccurrence s)
    {v : VertexId} (hvγ : v ∈ o.γ.1.vertices) (hvB : v ∉ o.B.1.vertices) :
    v ∉ @ResolvedAdmissibleSubgraph.vertices phi4DivergenceMeasureFamily G
      (stableSelectedOuter s.1) := by
  intro hv
  rw [ResolvedAdmissibleSubgraph.mem_vertices] at hv
  obtain ⟨c, hc, hvc⟩ := hv
  rcases stableRemnant_selectedOuter_elt_cases o hc with hdisj | ⟨δ, hδ, rfl⟩
  · exact Finset.disjoint_left.mp hdisj hvγ hvc
  · apply hvB
    rw [stableRootRelativeInner_vertices] at hvc
    exact ResolvedAdmissibleSubgraph.mem_vertices.mpr ⟨δ, hδ, hvc⟩

/-! ## Step 3e — the coordinate lemma (τ ∘ local retarget = global retarget on γ) -/

/-- **The coordinate lemma.**  On `γ`'s vertices, `τ` composed with the LOCAL retarget equals the GLOBAL
retarget. -/
theorem stableRemnant_coord (o : StableForestChoiceOccurrence s)
    {v : VertexId} (hvγ : v ∈ o.γ.1.vertices) :
    stableRemnantTau o
        (o.B.1.retargetVertex
          (phi4WTriplePrimeCanonicalSupply.starOf (stableLocalBoundaryCompletedGraph o.γ.1) o.B.1) v)
      = (stableSelectedOuter s.1).retargetVertex
          (phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1)) v := by
  by_cases hvB : v ∈ o.B.1.vertices
  · obtain ⟨δ₀, hδ₀, hvδ₀⟩ := ResolvedAdmissibleSubgraph.mem_vertices.mp hvB
    have hvR : v ∈ (stableRootRelativeInner o.γ.1 δ₀).vertices := by
      rw [stableRootRelativeInner_vertices]; exact hvδ₀
    rw [stableRemnant_retargetVertex_eq_star o.B.1 _ hδ₀ hvδ₀,
        stableRemnantTau_map o ⟨δ₀, hδ₀⟩,
        stableRemnant_retargetVertex_eq_star (stableSelectedOuter s.1) _
          (stableRemnant_promoted_mem o hδ₀) hvR]
  · rw [o.B.1.retargetVertex_of_not_mem _ hvB,
        stableRemnantTau_fix o (Finset.mem_sdiff.mpr ⟨hvγ, hvB⟩),
        (stableSelectedOuter s.1).retargetVertex_of_not_mem _
          (stableRemnant_not_mem_selectedOuter o hvγ hvB)]

/-! ## Step 3f — complement-edge inclusion -/

/-- The stable inner forest's complement edges embed (with multiplicity) into `stableSelectedOuter`'s. -/
theorem stableRemnant_complementEdges_le (o : StableForestChoiceOccurrence s) :
    o.B.1.complementEdges ≤ (stableSelectedOuter s.1).complementEdges := by
  set P : Finset (ResolvedFeynmanSubgraph G) :=
    (@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily
        (stableLocalBoundaryCompletedGraph o.γ.1) o.B.1).image (stableRootRelativeInner o.γ.1) with hPdef
  have hPsub : P ⊆ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G
      (stableSelectedOuter s.1) := by
    rw [hPdef, Finset.image_subset_iff]
    intro δ hδ
    exact stableRemnant_promoted_mem o hδ
  set Rest : Multiset ResolvedFeynmanEdge :=
    ((@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G
        (stableSelectedOuter s.1)) \ P).sum (fun c => c.internalEdges) with hRestdef
  have hPsum : P.sum (fun c => c.internalEdges) = o.B.1.internalEdges := by
    rw [hPdef, Finset.sum_image
      (fun δ₁ h₁ δ₂ h₂ h => stableRemnant_rootRelativeInner_injOn o h₁ h₂ h)]
    show (@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily
            (stableLocalBoundaryCompletedGraph o.γ.1) o.B.1).sum
          (fun δ => (stableRootRelativeInner o.γ.1 δ).internalEdges)
        = o.B.1.internalEdges
    exact Finset.sum_congr rfl (fun δ _ => stableRootRelativeInner_internalEdges o.γ.1 δ)
  have hSelI : (stableSelectedOuter s.1).internalEdges = o.B.1.internalEdges + Rest := by
    have hsum : Rest + P.sum (fun c => c.internalEdges)
        = (stableSelectedOuter s.1).internalEdges := by
      rw [hRestdef]; exact Finset.sum_sdiff hPsub
    rw [hPsum] at hsum
    rw [← hsum, add_comm]
  rw [Multiset.le_iff_count]
  intro e
  have hcompB : Multiset.count e o.B.1.complementEdges
      = Multiset.count e o.γ.1.internalEdges - Multiset.count e o.B.1.internalEdges := by
    show Multiset.count e ((stableLocalBoundaryCompletedGraph o.γ.1).internalEdges
          - o.B.1.internalEdges) = _
    rw [Multiset.count_sub, stableLocalBoundaryCompletedGraph_internalEdges]
  have hcompSel : Multiset.count e (stableSelectedOuter s.1).complementEdges
      = Multiset.count e G.internalEdges
        - Multiset.count e (stableSelectedOuter s.1).internalEdges := by
    show Multiset.count e (G.internalEdges - (stableSelectedOuter s.1).internalEdges) = _
    rw [Multiset.count_sub]
  rw [hcompB, hcompSel, hSelI, Multiset.count_add]
  have hle : Multiset.count e o.γ.1.internalEdges ≤ Multiset.count e G.internalEdges :=
    Multiset.count_le_of_le e o.γ.1.internalEdges_le
  by_cases hpos : 0 < Multiset.count e o.γ.1.internalEdges
  · have hR0 : Multiset.count e Rest = 0 := by
      rw [hRestdef, phi4WTriplePrime_count_finset_sum]
      refine Finset.sum_eq_zero (fun c hc => ?_)
      rw [Finset.mem_sdiff] at hc
      rcases stableRemnant_selectedOuter_elt_cases o hc.1 with hdisj | ⟨δ, hδ, rfl⟩
      · by_contra hne
        have hec : e ∈ c.internalEdges := Multiset.count_pos.mp (Nat.pos_of_ne_zero hne)
        have heγ : e ∈ o.γ.1.internalEdges := Multiset.count_pos.mp hpos
        obtain ⟨hsγ, _⟩ := o.γ.1.edges_supported e heγ
        obtain ⟨hsc, _⟩ := c.edges_supported e hec
        exact Finset.disjoint_left.mp hdisj hsγ hsc
      · exact absurd (show stableRootRelativeInner o.γ.1 δ ∈ P by
          rw [hPdef]; exact Finset.mem_image.mpr ⟨δ, hδ, rfl⟩) hc.2
    omega
  · have hz : Multiset.count e o.γ.1.internalEdges = 0 := Nat.eq_zero_of_not_pos hpos
    omega

/-! ## Step 4 — the decompleted stable remnant component -/

/-- The endpoints of a local contracted edge lie in the local contracted vertex set. -/
theorem stableRemnant_localContract_edge_endpoints
    (o : StableForestChoiceOccurrence s)
    {f : ResolvedFeynmanEdge} (hf : f ∈ (stableLocalContractGraph o).internalEdges) :
    f.source ∈ (stableLocalContractGraph o).vertices
      ∧ f.target ∈ (stableLocalContractGraph o).vertices := by
  rw [stableLocalContractGraph,
    ResolvedAdmissibleSubgraph.contractWithStars_internalEdges] at hf
  obtain ⟨e, he, rfl⟩ := Multiset.mem_map.mp hf
  have heγ : e ∈ (stableLocalBoundaryCompletedGraph o.γ.1).internalEdges := by
    have hle : o.B.1.complementEdges ≤ (stableLocalBoundaryCompletedGraph o.γ.1).internalEdges :=
      Multiset.sub_le_self _ _
    exact Multiset.mem_of_le hle he
  rw [stableLocalBoundaryCompletedGraph_internalEdges] at heγ
  obtain ⟨hs, ht⟩ := o.γ.1.edges_supported e heγ
  refine ⟨?_, ?_⟩
  · rw [stableLocalContractGraph]
    exact o.B.1.retargetVertex_mem_contractWithStars_vertices _
      (by rw [stableLocalBoundaryCompletedGraph_vertices]; exact hs)
  · rw [stableLocalContractGraph]
    exact o.B.1.retargetVertex_mem_contractWithStars_vertices _
      (by rw [stableLocalBoundaryCompletedGraph_vertices]; exact ht)

/-- `Ltau.vertices ⊆ Q.vertices`. -/
theorem stableRemnant_vertices_subset (o : StableForestChoiceOccurrence s) :
    ((stableLocalContractGraph o).mapPerm (stableRemnantTau o)).vertices
      ⊆ (stableSelectedOuterContractGraph s.1).vertices := by
  intro w hw
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hw
  rw [stableLocalContractGraph,
    ResolvedAdmissibleSubgraph.contractWithStars_vertices, Finset.mem_union] at hx
  rw [stableSelectedOuterContractGraph,
    ResolvedAdmissibleSubgraph.contractWithStars_vertices, Finset.mem_union]
  rcases hx with hxsdiff | hxstar
  · rw [Finset.mem_sdiff, stableLocalBoundaryCompletedGraph_vertices] at hxsdiff
    obtain ⟨hxγ, hxB⟩ := hxsdiff
    rw [stableRemnantTau_fix o (Finset.mem_sdiff.mpr ⟨hxγ, hxB⟩)]
    exact Or.inl (Finset.mem_sdiff.mpr
      ⟨o.γ.1.vertices_subset hxγ, stableRemnant_not_mem_selectedOuter o hxγ hxB⟩)
  · rw [ResolvedAdmissibleSubgraph.mem_starVertices] at hxstar
    obtain ⟨δ₀, hδ₀, rfl⟩ := hxstar
    rw [stableRemnantTau_map o ⟨δ₀, hδ₀⟩]
    exact Or.inr (ResolvedAdmissibleSubgraph.mem_starVertices.mpr
      ⟨stableRootRelativeInner o.γ.1 δ₀, stableRemnant_promoted_mem o hδ₀, rfl⟩)

/-- `Ltau.internalEdges = B.1.complementEdges` retargeted globally (the coordinate rewrite). -/
theorem stableRemnant_internalEdges_eq (o : StableForestChoiceOccurrence s) :
    ((stableLocalContractGraph o).mapPerm (stableRemnantTau o)).internalEdges
      = o.B.1.complementEdges.map
          ((stableSelectedOuter s.1).retargetEdge
            (phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1))) := by
  show (stableLocalContractGraph o).internalEdges.map
      (ResolvedFeynmanEdge.map (stableRemnantTau o)) = _
  rw [stableLocalContractGraph,
    ResolvedAdmissibleSubgraph.contractWithStars_internalEdges, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro e he
  have heγ : e ∈ (stableLocalBoundaryCompletedGraph o.γ.1).internalEdges := by
    have hle : o.B.1.complementEdges ≤ (stableLocalBoundaryCompletedGraph o.γ.1).internalEdges :=
      Multiset.sub_le_self _ _
    exact Multiset.mem_of_le hle he
  rw [stableLocalBoundaryCompletedGraph_internalEdges] at heγ
  obtain ⟨hs, ht⟩ := o.γ.1.edges_supported e heγ
  have hsrc := stableRemnant_coord o hs
  have htgt := stableRemnant_coord o ht
  simp only [Function.comp, ResolvedAdmissibleSubgraph.retargetEdge, ResolvedFeynmanEdge.retarget,
    ResolvedFeynmanEdge.map]
  rw [hsrc, htgt]

/-- `Ltau.internalEdges ≤ Q.internalEdges`. -/
theorem stableRemnant_internalEdges_le (o : StableForestChoiceOccurrence s) :
    ((stableLocalContractGraph o).mapPerm (stableRemnantTau o)).internalEdges
      ≤ (stableSelectedOuterContractGraph s.1).internalEdges := by
  rw [stableRemnant_internalEdges_eq, stableSelectedOuterContractGraph,
    ResolvedAdmissibleSubgraph.contractWithStars_internalEdges]
  exact Multiset.map_le_map (stableRemnant_complementEdges_le o)

/-- **body-635 (Step 4) — the decompleted stable remnant component** in the stable quotient `Q`.  Its external
legs are the DECOMPLETED genuine ambient legs (`Q.externalLegs.filter`), never the synthetic legs. -/
noncomputable def stableRemnantComponent (o : StableForestChoiceOccurrence s) :
    ResolvedFeynmanSubgraph (stableSelectedOuterContractGraph s.1) where
  vertices := ((stableLocalContractGraph o).mapPerm (stableRemnantTau o)).vertices
  internalEdges := ((stableLocalContractGraph o).mapPerm (stableRemnantTau o)).internalEdges
  externalLegs := (stableSelectedOuterContractGraph s.1).externalLegs.filter
    (fun ℓ => ℓ.attachedTo ∈
      ((stableLocalContractGraph o).mapPerm (stableRemnantTau o)).vertices)
  vertices_subset := stableRemnant_vertices_subset o
  internalEdges_le := stableRemnant_internalEdges_le o
  externalLegs_le := Multiset.filter_le _ _
  edges_supported := by
    intro e' he'
    obtain ⟨f, hf, rfl⟩ := Multiset.mem_map.mp he'
    obtain ⟨hfs, hft⟩ := stableRemnant_localContract_edge_endpoints o hf
    exact ⟨Finset.mem_image.mpr ⟨f.source, hfs, rfl⟩, Finset.mem_image.mpr ⟨f.target, hft, rfl⟩⟩
  legs_supported := fun ℓ hℓ => (Multiset.mem_filter.mp hℓ).2

@[simp] theorem stableRemnantComponent_vertices (o : StableForestChoiceOccurrence s) :
    (stableRemnantComponent o).vertices
      = ((stableLocalContractGraph o).mapPerm (stableRemnantTau o)).vertices :=
  rfl

@[simp] theorem stableRemnantComponent_internalEdges (o : StableForestChoiceOccurrence s) :
    (stableRemnantComponent o).internalEdges
      = ((stableLocalContractGraph o).mapPerm (stableRemnantTau o)).internalEdges :=
  rfl

@[simp] theorem stableRemnantComponent_externalLegs (o : StableForestChoiceOccurrence s) :
    (stableRemnantComponent o).externalLegs
      = (stableSelectedOuterContractGraph s.1).externalLegs.filter
          (fun ℓ => ℓ.attachedTo ∈
            ((stableLocalContractGraph o).mapPerm (stableRemnantTau o)).vertices) :=
  rfl

/-! ## Step 5a — ambient support, saturation, freshness, and the KEY membership iff -/

/-- Ambient endpoint/leg support of `G` (from W‴ membership). -/
theorem stableRemnant_ambient (o : StableForestChoiceOccurrence s) :
    ResolvedAmbientSupported G :=
  ((mem_phi4WTriplePrimeIndex G s.1.outer).mp s.1.outer_mem).1

/-- `γ` is externally-leg saturated on `G`. -/
theorem stableRemnant_gamma_saturated (o : StableForestChoiceOccurrence s) :
    ResolvedExternalLegSaturated G o.γ.1 :=
  (((mem_phi4WTriplePrimeIndex G s.1.outer).mp s.1.outer_mem).2.2.2.2.2.1) o.γ.1 o.γ.2

/-- The global retarget of a `stableSelectedOuter`-vertex is fresh (outside `G`). -/
theorem stableRemnant_phi_not_mem_G (o : StableForestChoiceOccurrence s)
    {v : VertexId}
    (hv : v ∈ @ResolvedAdmissibleSubgraph.vertices phi4DivergenceMeasureFamily G
        (stableSelectedOuter s.1)) :
    (stableSelectedOuter s.1).retargetVertex
        (phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1)) v ∉ G.vertices := by
  obtain ⟨c, hc, hvc⟩ := ResolvedAdmissibleSubgraph.mem_vertices.mp hv
  rw [stableRemnant_retargetVertex_eq_star (stableSelectedOuter s.1) _ hc hvc]
  exact stableRemnant_gen_star_not_mem (stableSelectedOuter s.1)
    (stableSelectedOuter_isProperForest s.1) hc

/-- **KEY membership iff.**  For an ambient vertex `v`, its global retarget lands in `Ltau.vertices` iff
`v ∈ γ.vertices`. -/
theorem stableRemnant_phi_mem_Ltau_iff (o : StableForestChoiceOccurrence s)
    {v : VertexId} (hvG : v ∈ G.vertices) :
    (stableSelectedOuter s.1).retargetVertex
        (phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1)) v
      ∈ ((stableLocalContractGraph o).mapPerm (stableRemnantTau o)).vertices
      ↔ v ∈ o.γ.1.vertices := by
  constructor
  · intro hmem
    obtain ⟨x, hx, hxeq⟩ := Finset.mem_image.mp hmem
    rw [stableLocalContractGraph,
      ResolvedAdmissibleSubgraph.contractWithStars_vertices, Finset.mem_union] at hx
    rcases hx with hxsdiff | hxstar
    · rw [Finset.mem_sdiff, stableLocalBoundaryCompletedGraph_vertices] at hxsdiff
      rw [stableRemnantTau_fix o (Finset.mem_sdiff.mpr hxsdiff)] at hxeq
      by_cases hvSel : v ∈ @ResolvedAdmissibleSubgraph.vertices phi4DivergenceMeasureFamily G
          (stableSelectedOuter s.1)
      · exact absurd (hxeq ▸ o.γ.1.vertices_subset hxsdiff.1)
          (stableRemnant_phi_not_mem_G o hvSel)
      · rw [(stableSelectedOuter s.1).retargetVertex_of_not_mem _ hvSel] at hxeq
        rw [← hxeq]; exact hxsdiff.1
    · rw [ResolvedAdmissibleSubgraph.mem_starVertices] at hxstar
      obtain ⟨δ₀, hδ₀, hδ₀eq⟩ := hxstar
      rw [← hδ₀eq, stableRemnantTau_map o ⟨δ₀, hδ₀⟩] at hxeq
      by_cases hvSel : v ∈ @ResolvedAdmissibleSubgraph.vertices phi4DivergenceMeasureFamily G
          (stableSelectedOuter s.1)
      · obtain ⟨c, hc, hvc⟩ := ResolvedAdmissibleSubgraph.mem_vertices.mp hvSel
        rw [stableRemnant_retargetVertex_eq_star (stableSelectedOuter s.1) _ hc hvc] at hxeq
        have hceq : stableRootRelativeInner o.γ.1 δ₀ = c :=
          stableRemnant_gen_star_injOn (stableSelectedOuter s.1)
            (stableSelectedOuter_isProperForest s.1)
            (stableRemnant_promoted_mem o hδ₀) hc hxeq
        rw [← hceq, stableRootRelativeInner_vertices] at hvc
        exact δ₀.vertices_subset hvc
      · rw [(stableSelectedOuter s.1).retargetVertex_of_not_mem _ hvSel] at hxeq
        exact absurd (hxeq.symm ▸ hvG)
          (stableRemnant_gen_star_not_mem (stableSelectedOuter s.1)
            (stableSelectedOuter_isProperForest s.1)
            (stableRemnant_promoted_mem o hδ₀))
  · intro hvγ
    rw [← stableRemnant_coord o hvγ]
    apply Finset.mem_image.mpr
    refine ⟨o.B.1.retargetVertex
      (phi4WTriplePrimeCanonicalSupply.starOf (stableLocalBoundaryCompletedGraph o.γ.1) o.B.1) v, ?_, rfl⟩
    rw [stableLocalContractGraph]
    exact o.B.1.retargetVertex_mem_contractWithStars_vertices _
      (by rw [stableLocalBoundaryCompletedGraph_vertices]; exact hvγ)

/-- An edge of `stableSelectedOuter.internalEdges` lies in one of its components. -/
theorem stableRemnant_mem_selectedOuter_internalEdges
    (o : StableForestChoiceOccurrence s)
    {e : ResolvedFeynmanEdge} (he : e ∈ (stableSelectedOuter s.1).internalEdges) :
    ∃ c ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G
      (stableSelectedOuter s.1), e ∈ c.internalEdges := by
  have hpos : 0 < Multiset.count e
      ((@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G
          (stableSelectedOuter s.1)).sum (fun c => c.internalEdges)) :=
    Multiset.count_pos.mpr he
  rw [phi4WTriplePrime_count_finset_sum] at hpos
  by_contra hcon
  push_neg at hcon
  have hz : (∑ c ∈ (@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G
        (stableSelectedOuter s.1)), Multiset.count e c.internalEdges) = 0 :=
    Finset.sum_eq_zero (fun c hc => Multiset.count_eq_zero.mpr (fun hec => hcon c hc hec))
  omega

/-! ## Step 5b — genuine quotient legs -/

/-- **body-635 (Step 5, GENUINE) — the DECOMPLETED genuine `Q`-legs equal `γ`'s genuine legs retargeted
globally.**  Inherited leg IDs / sectors VERBATIM (NO `encodeExistingLeg`). -/
theorem stableRemnant_genuineLegs_eq (o : StableForestChoiceOccurrence s) :
    (stableSelectedOuterContractGraph s.1).externalLegs.filter
        (fun ℓ => ℓ.attachedTo ∈
          ((stableLocalContractGraph o).mapPerm (stableRemnantTau o)).vertices)
      = o.γ.1.externalLegs.map ((stableSelectedOuter s.1).retargetExternalLeg
          (phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1))) := by
  rw [stableSelectedOuterContractGraph,
    ResolvedAdmissibleSubgraph.contractWithStars_externalLegs,
    ← Multiset.map_filter_of_iff
        ((stableSelectedOuter s.1).retargetExternalLeg
          (phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1)))
        G.externalLegs
        (fun ℓ => ((stableSelectedOuter s.1).retargetExternalLeg
          (phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1)) ℓ).attachedTo ∈
          ((stableLocalContractGraph o).mapPerm (stableRemnantTau o)).vertices)
        (fun ℓ => ℓ.attachedTo ∈
          ((stableLocalContractGraph o).mapPerm (stableRemnantTau o)).vertices)
        (fun _ => Iff.rfl)]
  congr 1
  rw [externalLegs_eq_filter_of_saturated o.γ.1 (stableRemnant_gamma_saturated o)]
  apply Multiset.filter_congr
  intro ℓ hℓ
  exact stableRemnant_phi_mem_Ltau_iff o ((stableRemnant_ambient o).2 ℓ hℓ)

/-- The GENUINE correspondence (no re-encode): the remnant's genuine legs are `γ`'s inherited legs pushed
through the local retarget and the correcting permutation. -/
theorem stableRemnant_even_eq (o : StableForestChoiceOccurrence s) :
    (stableRemnantComponent o).externalLegs
      = o.γ.1.externalLegs.map
          (fun ℓ => ResolvedExternalLeg.map (stableRemnantTau o)
            (o.B.1.retargetExternalLeg
              (phi4WTriplePrimeCanonicalSupply.starOf (stableLocalBoundaryCompletedGraph o.γ.1) o.B.1)
              ℓ)) := by
  rw [stableRemnantComponent_externalLegs, stableRemnant_genuineLegs_eq o]
  apply Multiset.map_congr rfl
  intro ℓ hℓ
  have hattach : ℓ.attachedTo ∈ o.γ.1.vertices := o.γ.1.legs_supported ℓ hℓ
  have hcoord := stableRemnant_coord o hattach
  simp only [ResolvedAdmissibleSubgraph.retargetExternalLeg,
    ResolvedExternalLeg.retarget, ResolvedExternalLeg.map]
  rw [hcoord]

/-! ## Step 5c — new remnant boundary legs -/

/-- The boundary predicate transports across the global retarget on complement edges. -/
theorem stableRemnant_remnantBd_iff (o : StableForestChoiceOccurrence s)
    {e : ResolvedFeynmanEdge} (hsG : e.source ∈ G.vertices) (htG : e.target ∈ G.vertices) :
    (stableRemnantComponent o).resolvedIsBoundaryEdge
        ((stableSelectedOuter s.1).retargetEdge
          (phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1)) e)
      ↔ o.γ.1.resolvedIsBoundaryEdge e := by
  have hs := stableRemnant_phi_mem_Ltau_iff o hsG
  have ht := stableRemnant_phi_mem_Ltau_iff o htG
  unfold ResolvedFeynmanSubgraph.resolvedIsBoundaryEdge
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨hs.mp h1, fun hc => h2 (ht.mpr hc)⟩
    · exact Or.inr ⟨fun hc => h1 (hs.mpr hc), ht.mp h2⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨hs.mpr h1, fun hc => h2 (ht.mp hc)⟩
    · exact Or.inr ⟨fun hc => h1 (hs.mp hc), ht.mpr h2⟩

/-- **body-635 (Step 5) — the remnant's induced boundary edges equal `γ`'s boundary edges retargeted
globally.** -/
theorem stableRemnant_resolvedBoundaryEdges (o : StableForestChoiceOccurrence s) :
    (stableRemnantComponent o).resolvedBoundaryEdges
      = o.γ.1.resolvedBoundaryEdges.map ((stableSelectedOuter s.1).retargetEdge
          (phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1))) := by
  have hQI : (stableSelectedOuterContractGraph s.1).internalEdges
      = (stableSelectedOuter s.1).complementEdges.map
          ((stableSelectedOuter s.1).retargetEdge
            (phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1))) := by
    rw [stableSelectedOuterContractGraph,
      ResolvedAdmissibleSubgraph.contractWithStars_internalEdges]
  show (stableSelectedOuterContractGraph s.1).internalEdges.filter
      (stableRemnantComponent o).resolvedIsBoundaryEdge = _
  rw [hQI, ← Multiset.map_filter_of_iff
        ((stableSelectedOuter s.1).retargetEdge
          (phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1)))
        (stableSelectedOuter s.1).complementEdges
        (fun e => (stableRemnantComponent o).resolvedIsBoundaryEdge
          ((stableSelectedOuter s.1).retargetEdge
            (phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1)) e))
        (stableRemnantComponent o).resolvedIsBoundaryEdge (fun _ => Iff.rfl)]
  congr 1
  have hzero : (stableSelectedOuter s.1).internalEdges.filter o.γ.1.resolvedIsBoundaryEdge
      = 0 := by
    rw [Multiset.filter_eq_nil]
    intro e he
    obtain ⟨c, hc, hec⟩ := stableRemnant_mem_selectedOuter_internalEdges o he
    rcases stableRemnant_selectedOuter_elt_cases o hc with hdisj | ⟨δ, hδ, rfl⟩
    · obtain ⟨hs, ht⟩ := c.edges_supported e hec
      rintro (⟨h1, _⟩ | ⟨_, h2⟩)
      · exact Finset.disjoint_left.mp hdisj h1 hs
      · exact Finset.disjoint_left.mp hdisj h2 ht
    · rw [stableRootRelativeInner_internalEdges] at hec
      obtain ⟨hs, ht⟩ := δ.edges_supported e hec
      rintro (⟨_, h2⟩ | ⟨h1, _⟩)
      · exact h2 (δ.vertices_subset ht)
      · exact h1 (δ.vertices_subset hs)
  have hfilt : (stableSelectedOuter s.1).complementEdges.filter o.γ.1.resolvedIsBoundaryEdge
      = o.γ.1.resolvedBoundaryEdges := by
    show (G.internalEdges - (stableSelectedOuter s.1).internalEdges).filter
        o.γ.1.resolvedIsBoundaryEdge = _
    rw [Multiset.filter_sub, hzero, Multiset.sub_zero]
    rfl
  have hcongr : (stableSelectedOuter s.1).complementEdges.filter
        (fun e => (stableRemnantComponent o).resolvedIsBoundaryEdge
          ((stableSelectedOuter s.1).retargetEdge
            (phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1)) e))
      = (stableSelectedOuter s.1).complementEdges.filter o.γ.1.resolvedIsBoundaryEdge := by
    apply Multiset.filter_congr
    intro e he
    exact stableRemnant_remnantBd_iff o
      ((stableRemnant_ambient o).1 e (Multiset.mem_of_le (Multiset.sub_le_self _ _) he)).1
      ((stableRemnant_ambient o).1 e (Multiset.mem_of_le (Multiset.sub_le_self _ _) he)).2
  rw [hcongr, hfilt]

/-- **body-635 (Step 5) — the retarget of a `γ`-boundary edge induces the SAME remnant boundary leg**, up to
the correcting permutation on the inside endpoint.  `edgeId` / `boundaryLegId` / `sector` are carried through
retarget VERBATIM. -/
theorem stableRemnant_boundaryExternalLeg_retarget (o : StableForestChoiceOccurrence s)
    {e : ResolvedFeynmanEdge} (he : e ∈ o.γ.1.resolvedBoundaryEdges) :
    (stableRemnantComponent o).boundaryExternalLeg
        ((stableSelectedOuter s.1).retargetEdge
          (phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1)) e)
      = ResolvedExternalLeg.map (stableRemnantTau o)
          (o.B.1.retargetExternalLeg
            (phi4WTriplePrimeCanonicalSupply.starOf (stableLocalBoundaryCompletedGraph o.γ.1) o.B.1)
            (o.γ.1.boundaryExternalLeg e)) := by
  have he_mem := (ResolvedFeynmanSubgraph.resolvedBoundaryEdges_mem).mp he
  have hesupp := (stableRemnant_ambient o).1 e he_mem.1
  have hinside : o.γ.1.resolvedInsideEndpoint e ∈ o.γ.1.vertices :=
    o.γ.1.resolvedInsideEndpoint_mem e he_mem.2
  have hcoord := stableRemnant_coord o hinside
  have hend : (stableRemnantComponent o).resolvedInsideEndpoint
        ((stableSelectedOuter s.1).retargetEdge
          (phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1)) e)
      = (stableSelectedOuter s.1).retargetVertex
          (phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1))
          (o.γ.1.resolvedInsideEndpoint e) := by
    show (if (stableSelectedOuter s.1).retargetVertex _ e.source
            ∈ (stableRemnantComponent o).vertices
          then (stableSelectedOuter s.1).retargetVertex _ e.source
          else (stableSelectedOuter s.1).retargetVertex _ e.target)
      = (stableSelectedOuter s.1).retargetVertex _
          (if e.source ∈ o.γ.1.vertices then e.source else e.target)
    rw [stableRemnantComponent_vertices]
    by_cases hsγ : e.source ∈ o.γ.1.vertices
    · rw [if_pos hsγ, if_pos ((stableRemnant_phi_mem_Ltau_iff o hesupp.1).mpr hsγ)]
    · rw [if_neg hsγ, if_neg (fun hc => hsγ ((stableRemnant_phi_mem_Ltau_iff o hesupp.1).mp hc))]
  show (stableRemnantComponent o).boundaryExternalLeg
      ((stableSelectedOuter s.1).retargetEdge
        (phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1)) e)
    = ResolvedExternalLeg.map (stableRemnantTau o)
        (o.B.1.retargetExternalLeg
          (phi4WTriplePrimeCanonicalSupply.starOf (stableLocalBoundaryCompletedGraph o.γ.1) o.B.1)
          (o.γ.1.boundaryExternalLeg e))
  unfold ResolvedFeynmanSubgraph.boundaryExternalLeg ResolvedAdmissibleSubgraph.retargetExternalLeg
    ResolvedExternalLeg.retarget ResolvedExternalLeg.map
  rw [hend, hcoord]
  simp only [ResolvedFeynmanSubgraph.boundaryLegId, ResolvedAdmissibleSubgraph.retargetEdge,
    ResolvedFeynmanEdge.retarget]

/-- **body-635 (Step 5, INHERITED BOUNDARY) — the remnant's NEW boundary legs equal `γ`'s inherited boundary
legs pushed through the local retarget and the correcting permutation.**  IDs / sectors VERBATIM. -/
theorem stableRemnant_inheritedBoundaryLegs_eq (o : StableForestChoiceOccurrence s) :
    (stableRemnantComponent o).resolvedBoundaryEdges.map
        (stableRemnantComponent o).boundaryExternalLeg
      = (o.γ.1.resolvedBoundaryEdges.map o.γ.1.boundaryExternalLeg).map
          (fun ℓ => ResolvedExternalLeg.map (stableRemnantTau o)
            (o.B.1.retargetExternalLeg
              (phi4WTriplePrimeCanonicalSupply.starOf (stableLocalBoundaryCompletedGraph o.γ.1) o.B.1)
              ℓ)) := by
  rw [stableRemnant_resolvedBoundaryEdges o, Multiset.map_map, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro e he
  show (stableRemnantComponent o).boundaryExternalLeg
      ((stableSelectedOuter s.1).retargetEdge
        (phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1)) e)
    = ResolvedExternalLeg.map (stableRemnantTau o)
        (o.B.1.retargetExternalLeg
          (phi4WTriplePrimeCanonicalSupply.starOf (stableLocalBoundaryCompletedGraph o.γ.1) o.B.1)
          (o.γ.1.boundaryExternalLeg e))
  exact stableRemnant_boundaryExternalLeg_retarget o he

/-! ## Step 6 — HEADLINE: the contract-twice raw graph equality -/

/-- **body-635 (Step 6, HEADLINE) — the decompleted stable remnant's boundary-completion reconstructs the
local contracted graph up to the per-occurrence correcting permutation `τ`.**  A RAW `ResolvedFeynmanGraph`
equality (all three fields, exact IDs / sectors / multiplicities; inherited legs VERBATIM). -/
theorem stableRemnant_contractTwice (o : StableForestChoiceOccurrence s) :
    stableLocalBoundaryCompletedGraph (stableRemnantComponent o)
      = (stableLocalContractGraph o).mapPerm (stableRemnantTau o) := by
  simp only [stableLocalBoundaryCompletedGraph, ResolvedFeynmanGraph.mapPerm,
    ResolvedFeynmanGraph.mk.injEq]
  refine ⟨rfl, rfl, ?_⟩
  rw [stableRemnant_even_eq o, stableRemnant_inheritedBoundaryLegs_eq o,
    stableLocalContractGraph, ResolvedAdmissibleSubgraph.contractWithStars_externalLegs,
    stableLocalBoundaryCompletedGraph_externalLegs]
  simp only [Multiset.map_add, Multiset.map_map, Function.comp]

/-- **body-635 (Step 6, COROLLARY) — the τ-erased class equality.** -/
theorem stableRemnant_completed_class_eq (o : StableForestChoiceOccurrence s) :
    (stableLocalBoundaryCompletedGraph (stableRemnantComponent o)).toResolvedClass
      = (stableLocalContractGraph o).toResolvedClass := by
  rw [stableRemnant_contractTwice o, ResolvedFeynmanGraph.toResolvedClass_mapPerm]

end GaugeGeometry.QFT.Combinatorial
