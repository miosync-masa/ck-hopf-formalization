import GaugeGeometry.QFT.HopfAlgebra.Phi4WTriplePrimeForestAlignedInnerForest

/-!
# QFT-R1-body-622b-3 — the FULL forest-block LEFT inverse `inverse ∘ forward = id`

body-622b-2 settled the hard FOREST **choice** payload
(`phi4WTriplePrime_forwardAligned_recoveredChoice_eq : recoveredChoice … = Sum.inr o.B`).  This body is the
ASSEMBLY: it reconstructs the source split choice `s` from `forestBlockForward s` and proves

    phi4WTriplePrime_recoveredSplitChoice (phi4WTriplePrime_forestBlockForward s) = s

## Ordered strategy (the ordering is load-bearing)
LEFT / RIGHT / FOREST recovery → `recoveredOuter … = s.outer` → ELIMINATE the outer equality (destructure a
GENERIC independent target `w`, `subst`) → choice `funext` (three branches) → structure equality.  The choice
is compared ONLY after the outer alignment.

* **Step 2 (RIGHT)** — `phi4WTriplePrime_forwardBlock_regionComponentOf_right`: a survivor
  `δ = componentEquiv s (Sum.inl γR)` is star-free, and `inv_regionComponentOf (forestBlockForward s) δ = γR.1`
  RAW (body-608 `recoveredRight` + body-603 `survivor` anchors, all `rfl`).
* **Step 3 (FOREST)** — `phi4WTriplePrime_forwardBlock_regionComponentOf_forest`: a remnant
  `δ = componentEquiv s (Sum.inr o)`, `inv_regionComponentOf (forestBlockForward s) δ = o.γ.1` via body-622a
  `forwardForest_recoveredParent_eq` (a thin membership adapter; NO re-proved geometry).
* **Step 1 (LEFT)** — `phi4WTriplePrime_forwardBlock_left_mem_selectedOuter` /
  `phi4WTriplePrime_forwardBlock_left_isLeftComponent`: a `Sum.inl true` component is kept in `selectedOuter`
  and is star-untouched.  The star-touching bridge (`phi4WTriplePrime_forwardBlock_star_mem_remnant_iff`) reuses
  body-604's `phi4WTriplePrime_phi_mem_Ltau_iff` (KEY membership iff) — NO new geometry.
* **Step 4 (OUTER)** — `phi4WTriplePrime_recoveredOuter_forestBlockForward : recoveredOuter … = s.outer`, a
  clean admissible element-set ext (body-620 `admissible_ext_elements`).  Forward inclusion classifies a
  recovered component as LEFT (`selectedOuter_component_origin`) or a quotient region (via
  `(componentEquiv s).symm`); reverse inclusion branches `s.choice` on `true / false / forest`.
* **Step 5 (CHOICE)** — `phi4WTriplePrime_recoveredChoice_forestBlockForward`: pointwise (transport-FREE, the
  value type `Bool ⊕ ForestIdx γ.bcrg` is membership-independent) recovered-choice = `s.choice`, three-branch.
* **Step 6 (HEADLINE)** — `phi4WTriplePrime_recoveredSplitChoice_forestBlockForward` via the generic
  independent-target assemble `phi4WTriplePrime_forestBlock_leftAssemble` (destructure `w` + `subst` the outer
  equality so the two choice domains become judgmentally identical, then `funext`; props by proof irrelevance).

## HALT compliance
Axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only); ZERO forbidden divergence classes in any
declaration TYPE.  NO public graph transport / cross-ambient equality / `HEq` / `cast` / graph-data `▸`
(the only `▸` is a Prop-membership rewrite).  NO corrected forward / global `τ` / orbit quotient / dedup; NO
new geometry / CD / degree / boundary lemma; NO whole `Equiv` (623); NO summand / `sum_bij` / alpha / coassoc;
NO polluted machinery.  No `sorry` / `admit` / `native_decide`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

open ResolvedFeynmanSubgraph

variable {G : ResolvedFeynmanGraph}

set_option maxHeartbeats 3200000

/-- The concrete φ⁴ divergence measure family, registered file-locally (providable instance, NO forbidden
class). -/
noncomputable local instance phi4Inst622b3 : (H : FeynmanGraph) → DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

/-! ## Shared star-touching bridge (reuses body-604's KEY membership iff — NO new geometry) -/

/-- **body-622b-3 (bridge) — a `selectedOuter` component's star lands in the remnant of `o` iff any of its
vertices lies in `o`'s owner.**  Pure membership transport of body-604's `phi4WTriplePrime_phi_mem_Ltau_iff`
across `retargetVertex_eq_star`; no geometry is re-proved. -/
theorem phi4WTriplePrime_forwardBlock_star_mem_remnant_iff
    {s : Phi4EdgeCompleteFilteredCoassocSplitChoice G}
    (o : Phi4WTriplePrime_ForestChoiceOccurrence s) {c : ResolvedFeynmanSubgraph G}
    (hc : c ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G
        (phi4WTriplePrime_selectedOuter s))
    {v : VertexId} (hvc : v ∈ c.vertices) :
    phi4WTriplePrimeCanonicalSupply.starOf G (phi4WTriplePrime_selectedOuter s) c
        ∈ (phi4WTriplePrime_remnantComponent o).vertices
      ↔ v ∈ o.γ.1.vertices := by
  rw [phi4WTriplePrime_remnantComponent_vertices,
      ← phi4WTriplePrime_retargetVertex_eq_star (phi4WTriplePrime_selectedOuter s)
        (phi4WTriplePrimeCanonicalSupply.starOf G (phi4WTriplePrime_selectedOuter s)) hc hvc]
  exact phi4WTriplePrime_phi_mem_Ltau_iff o (c.vertices_subset hvc)

/-! ## Step 2 — RIGHT owner recovery (the survivor recovers its original right component) -/

/-- **body-622b-3 (Step 2) — a survivor's recovered region component is its original right component.**  For
`γR : RightComponent s`, `δ = componentEquiv s (Sum.inl γR)` is star-free, so
`inv_regionComponentOf (forestBlockForward s) δ = recoveredRight … = γR.1` (all carrier fields `rfl`). -/
theorem phi4WTriplePrime_forwardBlock_regionComponentOf_right
    {s : Phi4EdgeCompleteFilteredCoassocSplitChoice G}
    (γR : phi4WTriplePrime_RightComponent s) :
    phi4WTriplePrime_inv_regionComponentOf (phi4WTriplePrime_forestBlockForward s)
        (phi4WTriplePrime_componentEquiv s (Sum.inl γR)) = γR.1 := by
  have hfree : ¬ phi4WTriplePrime_inv_isForestImage (phi4WTriplePrime_forestBlockForward s)
      (phi4WTriplePrime_componentEquiv s (Sum.inl γR)) :=
    phi4WTriplePrime_survivor_not_forestImage s γR
  rw [phi4WTriplePrime_inv_regionComponentOf_eq_right (phi4WTriplePrime_forestBlockForward s) hfree]
  exact ResolvedFeynmanSubgraph.ext rfl rfl rfl

/-! ## Step 3 — FOREST owner recovery (the remnant recovers its occurrence owner) -/

/-- **body-622b-3 (Step 3) — a remnant's recovered region component is its occurrence owner.**  For
`o : ForestChoiceOccurrence s`, `δ = componentEquiv s (Sum.inr o)` is a star-touching remnant, so
`inv_regionComponentOf (forestBlockForward s) δ = inv_recoveredParent … = o.γ.1` (body-622a).  A thin
membership adapter over the `δo`-form; NO re-proved geometry. -/
theorem phi4WTriplePrime_forwardBlock_regionComponentOf_forest
    {s : Phi4EdgeCompleteFilteredCoassocSplitChoice G}
    (o : Phi4WTriplePrime_ForestChoiceOccurrence s) :
    phi4WTriplePrime_inv_regionComponentOf (phi4WTriplePrime_forestBlockForward s)
        (phi4WTriplePrime_componentEquiv s (Sum.inr o)) = o.γ.1 := by
  show phi4WTriplePrime_inv_regionComponentOf (phi4WTriplePrime_forestBlockForward s)
      ⟨phi4WTriplePrime_remnantComponent o,
        phi4WTriplePrime_remnantComponent_mem_quotientForest o⟩ = o.γ.1
  have hsto : phi4WTriplePrime_inv_isForestImage (phi4WTriplePrime_forestBlockForward s)
      ⟨phi4WTriplePrime_remnantComponent o,
        phi4WTriplePrime_remnantComponent_mem_quotientForest o⟩ :=
    phi4WTriplePrime_remnant_star_touching o
  rw [phi4WTriplePrime_inv_regionComponentOf_eq_parent (phi4WTriplePrime_forestBlockForward s) hsto]
  exact phi4WTriplePrime_forwardForest_recoveredParent_eq s o

/-! ## Step 1 — LEFT: a `Sum.inl true` component is a star-untouched `selectedOuter` component -/

/-- **body-622b-3 (Step 1) — a `Sum.inl true` component stays in `selectedOuter`.** -/
theorem phi4WTriplePrime_forwardBlock_left_mem_selectedOuter
    {s : Phi4EdgeCompleteFilteredCoassocSplitChoice G} {γ : ResolvedFeynmanSubgraph G}
    (hγ : γ ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G s.outer)
    (htrue : s.choice ⟨γ, hγ⟩ (Finset.mem_attach _ _) = Sum.inl true) :
    γ ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G
      (phi4WTriplePrime_selectedOuter s) := by
  rw [phi4WTriplePrime_selectedOuter_elements, Finset.mem_union]
  refine Or.inl ?_
  rw [phi4WTriplePrime_leftOf_elements, Finset.mem_filter]
  exact ⟨hγ, ⟨hγ, htrue⟩⟩

/-- **body-622b-3 (Step 1) — a `Sum.inl true` component is a LEFT component of `forestBlockForward s`.**  Its
canonical star touches no quotient component: survivors are star-free (body-607), remnants only contain
promoted stars (star-touching bridge above + owner disjointness). -/
theorem phi4WTriplePrime_forwardBlock_left_isLeftComponent
    {s : Phi4EdgeCompleteFilteredCoassocSplitChoice G} {γ : ResolvedFeynmanSubgraph G}
    (hγ : γ ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G s.outer)
    (htrue : s.choice ⟨γ, hγ⟩ (Finset.mem_attach _ _) = Sum.inl true) :
    phi4WTriplePrime_inv_isLeftComponent (phi4WTriplePrime_forestBlockForward s) γ := by
  have hsel : γ ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G
      (phi4WTriplePrime_selectedOuter s) :=
    phi4WTriplePrime_forwardBlock_left_mem_selectedOuter hγ htrue
  intro δ' hmem
  rcases phi4WTriplePrime_quotientForest_element_cases s δ'.2 with ⟨γ'', hγ''R, hδeq⟩ | ⟨o, hδeq⟩
  · -- survivor: star-free
    rw [hδeq] at hmem
    exact phi4WTriplePrime_survivor_star_free s hγ''R _ hmem
      (ResolvedAdmissibleSubgraph.mem_starVertices.mpr ⟨γ, hsel, rfl⟩)
  · -- remnant: the star maps to the owner, forcing γ = o.γ.1 (impossible: choices differ)
    rw [hδeq] at hmem
    obtain ⟨v, hv⟩ := Finset.card_pos.mp
      (((mem_phi4WTriplePrimeIndex G s.outer).mp s.outer_mem).2.2.2.2.1.2.1 γ hγ)
    have hvowner := (phi4WTriplePrime_forwardBlock_star_mem_remnant_iff o hsel hv).mp hmem
    have hne : γ ≠ o.γ.1 := by
      intro h
      have hsub : (⟨γ, hγ⟩ : {x // x ∈ @ResolvedAdmissibleSubgraph.elements
          phi4DivergenceMeasureFamily G s.outer}) = o.γ := Subtype.ext h
      have e1 := hsub ▸ htrue
      rw [o.hchoice] at e1
      exact absurd e1 (by simp)
    exact Finset.disjoint_left.mp (s.outer.pairwiseDisjoint hγ o.γ.2 hne) hv hvowner

/-! ## Step 4 — TARGET: `recoveredOuter (forestBlockForward s) = s.outer` -/

/-- **body-622b-3 (Step 4, HEADLINE) — the recovered outer forest of `forestBlockForward s` is `s.outer`.**
A clean admissible element-set ext.  Forward inclusion classifies a recovered component as a LEFT
`selectedOuter` component (`selectedOuter_component_origin`; the promoted case is impossible by the
star-touching bridge) or a quotient region recovered via `(componentEquiv s).symm` (RIGHT → `γR.1`, FOREST →
`o.γ.1`).  Reverse inclusion branches `s.choice` on `true / false / forest`.  NO dedup, NO orbit quotient. -/
theorem phi4WTriplePrime_recoveredOuter_forestBlockForward
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) :
    phi4WTriplePrime_recoveredOuter (phi4WTriplePrime_forestBlockForward s) = s.outer := by
  apply phi4WTriplePrime_admissible_ext_elements
  apply Finset.ext
  intro γ
  constructor
  · -- forward: recovered component ⇒ s.outer component
    intro hγrec
    rcases phi4WTriplePrime_recoveredOuter_component_origin (phi4WTriplePrime_forestBlockForward s) hγrec
      with ⟨hγsel, hL⟩ | ⟨δ, hδeq⟩
    · -- LEFT selectedOuter component
      rcases phi4WTriplePrime_selectedOuter_component_origin s hγsel with ⟨hγouter, -⟩ | hP
      · exact hγouter
      · exfalso
        obtain ⟨γ', hγ', B, hchoice, δ, hδ, hγeq⟩ := hP
        have hδne : δ.vertices.Nonempty := Finset.card_pos.mp
          ((phi4WTriplePrime_occ_B_isProperForest
            (⟨⟨γ', hγ'⟩, B, hchoice⟩ : Phi4WTriplePrime_ForestChoiceOccurrence s)).2.1 δ hδ)
        obtain ⟨v, hv⟩ := hδne
        have hvc : v ∈ (rootRelativeInner γ' δ).vertices := by rw [rootRelativeInner_vertices]; exact hv
        have hstar := (phi4WTriplePrime_forwardBlock_star_mem_remnant_iff
            (⟨⟨γ', hγ'⟩, B, hchoice⟩ : Phi4WTriplePrime_ForestChoiceOccurrence s)
            (phi4WTriplePrime_remnant_promoted_mem
              (⟨⟨γ', hγ'⟩, B, hchoice⟩ : Phi4WTriplePrime_ForestChoiceOccurrence s) hδ) hvc).mpr
            (phi4WTriplePrime_rootRelativeInner_vertices_subset γ' δ hvc)
        have hcontra := hL ⟨phi4WTriplePrime_remnantComponent
            (⟨⟨γ', hγ'⟩, B, hchoice⟩ : Phi4WTriplePrime_ForestChoiceOccurrence s),
            phi4WTriplePrime_remnantComponent_mem_quotientForest
              (⟨⟨γ', hγ'⟩, B, hchoice⟩ : Phi4WTriplePrime_ForestChoiceOccurrence s)⟩
        rw [hγeq] at hcontra
        exact hcontra hstar
    · -- quotient region component: classify via componentEquiv.symm
      rw [← hδeq]
      rcases hsymm : (phi4WTriplePrime_componentEquiv s).symm δ with γR | o
      · have hd : phi4WTriplePrime_componentEquiv s (Sum.inl γR) = δ := by
          rw [← hsymm]; exact (phi4WTriplePrime_componentEquiv s).apply_symm_apply δ
        rw [← hd, phi4WTriplePrime_forwardBlock_regionComponentOf_right]
        obtain ⟨hmem, -⟩ := γR.2
        exact hmem
      · have hd : phi4WTriplePrime_componentEquiv s (Sum.inr o) = δ := by
          rw [← hsymm]; exact (phi4WTriplePrime_componentEquiv s).apply_symm_apply δ
        rw [← hd, phi4WTriplePrime_forwardBlock_regionComponentOf_forest]
        exact o.γ.2
  · -- reverse: s.outer component ⇒ recovered component
    intro hγ
    rcases hbr : s.choice ⟨γ, hγ⟩ (Finset.mem_attach _ _) with b | B
    · rcases b with _ | _
      · -- Sum.inl false → RIGHT
        have hγR : phi4WTriplePrime_isRightComponent s γ := ⟨hγ, hbr⟩
        refine (phi4WTriplePrime_mem_recoveredOuter_elements
          (phi4WTriplePrime_forestBlockForward s)).mpr
          (Or.inr ⟨phi4WTriplePrime_componentEquiv s (Sum.inl ⟨γ, hγR⟩), ?_⟩)
        exact phi4WTriplePrime_forwardBlock_regionComponentOf_right ⟨γ, hγR⟩
      · -- Sum.inl true → LEFT
        exact phi4WTriplePrime_inv_left_mem_recoveredOuter (phi4WTriplePrime_forestBlockForward s)
          (phi4WTriplePrime_forwardBlock_left_mem_selectedOuter hγ hbr)
          (phi4WTriplePrime_forwardBlock_left_isLeftComponent hγ hbr)
    · -- Sum.inr B → FOREST
      refine (phi4WTriplePrime_mem_recoveredOuter_elements
        (phi4WTriplePrime_forestBlockForward s)).mpr
        (Or.inr ⟨phi4WTriplePrime_componentEquiv s
          (Sum.inr (⟨⟨γ, hγ⟩, B, hbr⟩ : Phi4WTriplePrime_ForestChoiceOccurrence s)), ?_⟩)
      exact phi4WTriplePrime_forwardBlock_regionComponentOf_forest
        (⟨⟨γ, hγ⟩, B, hbr⟩ : Phi4WTriplePrime_ForestChoiceOccurrence s)

/-! ## Step 5 — the recovered choice equals `s.choice` (transport-free, pointwise) -/

/-- **body-622b-3 (Step 5, HEADLINE) — the recovered global choice of `forestBlockForward s` equals
`s.choice`.**  Pointwise and transport-FREE (the value type `Bool ⊕ ForestIdx γ.bcrg` is membership
independent): LEFT → `recoveredChoice_left` = `Sum.inl true`; RIGHT → `Sum.inl false` (Step 2 owner + the
`dif` unfolding); FOREST → `Sum.inr B` plugging body-622b-2's `forwardAligned_recoveredChoice_eq` DIRECTLY. -/
theorem phi4WTriplePrime_recoveredChoice_forestBlockForward
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) :
    ∀ (γ : ResolvedFeynmanSubgraph G)
      (h1 : γ ∈ (phi4WTriplePrime_recoveredOuter (phi4WTriplePrime_forestBlockForward s)).elements)
      (h2 : γ ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G s.outer),
      phi4WTriplePrime_recoveredChoice (phi4WTriplePrime_forestBlockForward s) ⟨γ, h1⟩
          (Finset.mem_attach _ _)
        = s.choice ⟨γ, h2⟩ (Finset.mem_attach _ _) := by
  intro γ h1 h2
  rcases hbr : s.choice ⟨γ, h2⟩ (Finset.mem_attach _ _) with b | B
  · rcases b with _ | _
    · -- RIGHT: value `Sum.inl false`
      have hγR : phi4WTriplePrime_isRightComponent s γ := ⟨h2, hbr⟩
      have hfree : ¬ phi4WTriplePrime_inv_isForestImage (phi4WTriplePrime_forestBlockForward s)
          (phi4WTriplePrime_componentEquiv s (Sum.inl ⟨γ, hγR⟩)) :=
        phi4WTriplePrime_survivor_not_forestImage s ⟨γ, hγR⟩
      have hstep2 : phi4WTriplePrime_inv_regionComponentOf (phi4WTriplePrime_forestBlockForward s)
          (phi4WTriplePrime_componentEquiv s (Sum.inl ⟨γ, hγR⟩)) = γ :=
        phi4WTriplePrime_forwardBlock_regionComponentOf_right ⟨γ, hγR⟩
      show phi4WTriplePrime_recoveredChoice (phi4WTriplePrime_forestBlockForward s) ⟨γ, h1⟩
          (Finset.mem_attach _ _) = Sum.inl false
      unfold phi4WTriplePrime_recoveredChoice
      have hq : ∃ δ : {x // x ∈ (phi4WTriplePrime_forestBlockForward s).2.1.elements},
          phi4WTriplePrime_inv_regionComponentOf (phi4WTriplePrime_forestBlockForward s) δ = γ :=
        ⟨phi4WTriplePrime_componentEquiv s (Sum.inl ⟨γ, hγR⟩), hstep2⟩
      rw [dif_pos hq, dif_neg (show ¬ phi4WTriplePrime_inv_isForestImage
          (phi4WTriplePrime_forestBlockForward s) hq.choose by
        rw [phi4WTriplePrime_inv_regionComponentOf_injective (phi4WTriplePrime_forestBlockForward s)
          (hq.choose_spec.trans hstep2.symm)]; exact hfree)]
    · -- LEFT: value `Sum.inl true`
      exact phi4WTriplePrime_recoveredChoice_left (phi4WTriplePrime_forestBlockForward s)
        (phi4WTriplePrime_forwardBlock_left_mem_selectedOuter h2 hbr)
        (phi4WTriplePrime_forwardBlock_left_isLeftComponent h2 hbr) (Finset.mem_attach _ _)
  · -- FOREST: value `Sum.inr B` (body-622b-2 payload)
    exact phi4WTriplePrime_forwardAligned_recoveredChoice_eq
      (⟨⟨γ, h2⟩, B, hbr⟩ : Phi4WTriplePrime_ForestChoiceOccurrence s) h1

/-! ## Step 6 — the generic independent-target assemble + the headline left inverse -/

/-- **body-622b-3 (Step 6 helper) — the generic split-choice assemble.**  GENERIC in an INDEPENDENT target
`w`, so destructuring `w` and `subst`-ing the outer equality aligns the two recovered/`w` choice domains
JUDGMENTALLY (no occurs-check, no transport), whence the choice `funext` closes from the transport-free
pointwise hypothesis and the remaining `Prop` fields are proof-irrelevant. -/
theorem phi4WTriplePrime_forestBlock_leftAssemble
    (s w : Phi4EdgeCompleteFilteredCoassocSplitChoice G)
    (hA : phi4WTriplePrime_recoveredOuter (phi4WTriplePrime_forestBlockForward s) = w.outer)
    (hc : ∀ (γ : ResolvedFeynmanSubgraph G)
        (h1 : γ ∈ (phi4WTriplePrime_recoveredOuter (phi4WTriplePrime_forestBlockForward s)).elements)
        (h2 : γ ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G w.outer),
        phi4WTriplePrime_recoveredChoice (phi4WTriplePrime_forestBlockForward s) ⟨γ, h1⟩
            (Finset.mem_attach _ _)
          = w.choice ⟨γ, h2⟩ (Finset.mem_attach _ _)) :
    phi4WTriplePrime_recoveredSplitChoice (phi4WTriplePrime_forestBlockForward s) = w := by
  obtain ⟨⟨wouter, wmem, wchoice, wcmem⟩, wfilt⟩ := w
  subst hA
  have hchoice : phi4WTriplePrime_recoveredChoice (phi4WTriplePrime_forestBlockForward s) = wchoice := by
    funext γ hγ
    exact hc γ.1 γ.2 γ.2
  subst hchoice
  rfl

/-- **body-622b-3 (Step 6, HEADLINE) — the FULL forest-block LEFT inverse.**  The source-independent recovered
inverse applied to `forestBlockForward s` returns `s` EXACTLY.  ONLY hypothesis `s`; the outer equality
(Step 4) and the transport-free choice equality (Step 5) are assembled through the generic
independent-target `leftAssemble` (destructure + `subst` the outer equality → judgmental choice domains →
`funext`; `Prop` fields by proof irrelevance). -/
theorem phi4WTriplePrime_recoveredSplitChoice_forestBlockForward
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) :
    phi4WTriplePrime_recoveredSplitChoice (phi4WTriplePrime_forestBlockForward s) = s :=
  phi4WTriplePrime_forestBlock_leftAssemble s s
    (phi4WTriplePrime_recoveredOuter_forestBlockForward s)
    (phi4WTriplePrime_recoveredChoice_forestBlockForward s)

end GaugeGeometry.QFT.Combinatorial
