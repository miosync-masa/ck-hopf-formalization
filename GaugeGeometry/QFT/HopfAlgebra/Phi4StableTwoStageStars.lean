import GaugeGeometry.QFT.HopfAlgebra.Phi4StableTwoStageResidual

/-!
# QFT-R1-body-639b — STABLE final-star OWNERSHIP (second sub-body of the `quot_eq` campaign)

Body-639a delivered the EXACT two-stage residual geometry.  This body establishes **final-star ownership** — it
classifies every outer component's final two-stage star by **which ambient it belongs to** (`Q.vertices`
membership), NOT by the star's numeric value.  This ambient classifier separates ALL LEFT-vs-non-LEFT cross
cases, and, together with the per-sector `starOf` injectivities and the survivor/remnant Finset disjointness,
produces the FOUR inputs body-639c's global correcting-permutation engine needs (two injectivities + two
freshness-disjointnesses).

With `s : StablePhi4MixedSplitChoice G hSt` and `Q := stableSelectedOuterContractGraph s.1`:

## Steps
* **Step 1 — outer component index.**  `StableOuterComponent` (an `abbrev`) + the one-stage star
  `stableOneStageOuterStar` (the canonical star of `s.1.outer`).
* **Step 2 — the final two-stage star.**  `stableFinalTwoStageStar` (LEFT: a first-stage `stableSelectedOuter`
  star; RIGHT: the `Q`-quotient-forest star of the right survivor; FOREST: the `Q`-quotient-forest star of the
  remnant) + LEFT/RIGHT/FOREST simp anchors + each component's membership in the correct forest's `.elements`.
* **Step 3 — the ambient classifier (MATHEMATICAL CENTER).**
  `stableFinalTwoStageStar_mem_quotientAmbient_iff_left`: the final star lies in `Q.vertices` iff the choice is
  `Sum.inl true`.  LEFT star is a first-stage `stableSelectedOuter` star ⇒ a `Q` star-vertex; RIGHT/FOREST star
  is a second-stage canonical `Q`-forest star ⇒ FRESH (outside `Q.vertices`).
* **Step 4 — sector injectivity.**  `_left_injective` / `_right_injective` / `_forest_injective` (owner
  equality recovered from remnant equality — NO dependent `B` equality) / `_right_forest_ne`.
* **Step 5 — global injectivity.**  `stableOneStageOuterStar_injective` and `stableFinalTwoStageStar_injective`
  (a 3×3 choice-tag classification: LEFT cross via Step 3, RIGHT/FOREST cross via quotient-forest separation).
* **Step 6 — surviving-root freshness.**  `stableTwoStageSurvivingVertices := G.vertices \ s.1.outer.vertices`;
  `stableOneStageOuterStar_not_mem_survivors`; `stableFinalTwoStageStar_not_mem_survivors`
  (`stableTwoStageSurvivingVertices ⊆ Q.vertices`).

## HALT / red lines (639b scope: final-star ownership ONLY)
NOT entered here (they belong to 639c/639d): the global permutation `stableTwoStageTau`; ANY composition /
comparison with the local `stableRemnantTau`; ANY retarget composition / graph / class / rightTerm equality; the
exact residual re-proof (READ 639a); summand agreement / `sum_bij` / alpha / coassoc.  ZERO new `structure` /
`class` / permanent `instance` (one file-local `local instance` for the φ⁴ family; `StableOuterComponent` is an
`abbrev`).  ZERO forbidden divergence class in any declaration TYPE; ZERO `sorry` / `admit` / `native_decide`; NO
`HEq` / `cast` / graph-data `▸` (Prop-membership `▸` only).  Body-625's no-go and bodies 629-639a / the old
carrier are UNEDITED.  Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

open ResolvedFeynmanSubgraph

variable {G : ResolvedFeynmanGraph}

set_option maxHeartbeats 3200000

/-- The concrete φ⁴ divergence measure family, registered file-locally (providable instance, NO forbidden
class). -/
noncomputable local instance instPhi4DivergenceMeasureFamily639b : (H : FeynmanGraph) → DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

variable {hSt : StableResolvedBoundaryIds G}

/-! ## Step 1 — the outer component index + the one-stage star -/

/-- **body-639b (Step 1) — the outer component index.**  An outer component of a stable mixed split choice.  An
`abbrev` (definitionally the domain of `s.1.choice` and the `γ`-field of `StableForestChoiceOccurrence`). -/
abbrev StableOuterComponent (s : StablePhi4MixedSplitChoice G hSt) : Type :=
  { γ : ResolvedFeynmanSubgraph G //
      γ ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G s.1.outer }

/-- **body-639b (Step 1) — the one-stage outer star.**  The canonical star of `s.1.outer` at the component. -/
noncomputable def stableOneStageOuterStar (s : StablePhi4MixedSplitChoice G hSt)
    (γ : StableOuterComponent s) : VertexId :=
  phi4WTriplePrimeCanonicalSupply.starOf G s.1.outer γ.1

/-! ## Step 2 — the final two-stage star + anchors + forest membership -/

/-- **body-639b (Step 2) — the final two-stage star of an outer component.**  LEFT (`Sum.inl true`): a
first-stage `stableSelectedOuter` star of `γ`.  RIGHT (`Sum.inl false`): the `Q`-quotient-forest star of the
right survivor.  FOREST (`Sum.inr B`): the `Q`-quotient-forest star of the decompleted remnant. -/
noncomputable def stableFinalTwoStageStar (s : StablePhi4MixedSplitChoice G hSt)
    (γ : StableOuterComponent s) : VertexId :=
  match h : s.1.choice γ (Finset.mem_attach _ γ) with
  | Sum.inl true =>
      phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1) γ.1
  | Sum.inl false =>
      phi4WTriplePrimeCanonicalSupply.starOf (stableSelectedOuterContractGraph s.1)
        (stableQuotientForest s) (stableRightSurvivor s.1 ⟨γ.2, h⟩)
  | Sum.inr B =>
      phi4WTriplePrimeCanonicalSupply.starOf (stableSelectedOuterContractGraph s.1)
        (stableQuotientForest s) (stableRemnantComponent ⟨γ, B, h⟩)

/-- Two forest-choice occurrences with the same owner are equal (the inner forest `B` is DETERMINED by the
owner via the choice value; owner membership and the choice proof enter proof-irrelevantly). -/
theorem stableForestOccurrence_ext_helper (s : StablePhi4MixedSplitChoice G hSt)
    (o₁ o₂ : StableForestChoiceOccurrence s) (h : o₁.γ.1 = o₂.γ.1) : o₁ = o₂ := by
  obtain ⟨⟨γ₁, hγ₁⟩, B₁, hch₁⟩ := o₁
  obtain ⟨⟨γ₂, hγ₂⟩, B₂, hch₂⟩ := o₂
  have h' : γ₁ = γ₂ := h
  subst h'
  have hBB : B₁ = B₂ := Sum.inr.inj (hch₁.symm.trans hch₂)
  subst hBB
  rfl

/-- **body-639b (Step 2, LEFT anchor).** -/
theorem stableFinalTwoStageStar_left (s : StablePhi4MixedSplitChoice G hSt)
    (γ : StableOuterComponent s) (h : s.1.choice γ (Finset.mem_attach _ γ) = Sum.inl true) :
    stableFinalTwoStageStar s γ
      = phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1) γ.1 := by
  unfold stableFinalTwoStageStar
  split
  · rfl
  · rename_i heq; exact absurd (h.symm.trans heq) (by simp)
  · rename_i heq; exact absurd (h.symm.trans heq) (by simp)

/-- **body-639b (Step 2, RIGHT anchor).** -/
theorem stableFinalTwoStageStar_right (s : StablePhi4MixedSplitChoice G hSt)
    (γ : StableOuterComponent s) (h : s.1.choice γ (Finset.mem_attach _ γ) = Sum.inl false) :
    stableFinalTwoStageStar s γ
      = phi4WTriplePrimeCanonicalSupply.starOf (stableSelectedOuterContractGraph s.1)
          (stableQuotientForest s) (stableRightSurvivor s.1 ⟨γ.2, h⟩) := by
  unfold stableFinalTwoStageStar
  split
  · rename_i heq; exact absurd (h.symm.trans heq) (by simp)
  · rfl
  · rename_i heq; exact absurd (h.symm.trans heq) (by simp)

/-- **body-639b (Step 2, FOREST anchor).** -/
theorem stableFinalTwoStageStar_forest (s : StablePhi4MixedSplitChoice G hSt)
    (γ : StableOuterComponent s) (B : StableLocalForestIdx γ.1)
    (h : s.1.choice γ (Finset.mem_attach _ γ) = Sum.inr B) :
    stableFinalTwoStageStar s γ
      = phi4WTriplePrimeCanonicalSupply.starOf (stableSelectedOuterContractGraph s.1)
          (stableQuotientForest s) (stableRemnantComponent ⟨γ, B, h⟩) := by
  unfold stableFinalTwoStageStar
  split
  · rename_i heq; exact absurd (h.symm.trans heq) (by simp)
  · rename_i heq; exact absurd (h.symm.trans heq) (by simp)
  · rename_i B' heq
    exact congrArg
      (phi4WTriplePrimeCanonicalSupply.starOf (stableSelectedOuterContractGraph s.1)
        (stableQuotientForest s))
      (congrArg stableRemnantComponent
        (stableForestOccurrence_ext_helper s ⟨γ, B', heq⟩ ⟨γ, B, h⟩ rfl))

/-- **body-639b (Step 2) — the right survivor lands in the RIGHT-survivor forest of `Q`.** -/
theorem stableFinalRightSurvivor_mem_survivorForest (s : StablePhi4MixedSplitChoice G hSt)
    (γ : StableOuterComponent s) (h : s.1.choice γ (Finset.mem_attach _ γ) = Sum.inl false) :
    stableRightSurvivor s.1 (⟨γ.2, h⟩ : stableIsRightComponent s.1 γ.1)
      ∈ (stableRightSurvivorForest s.1).elements := by
  rw [stableRightSurvivorForest_elements]
  have hmemRC : γ.1 ∈ stableRightComponents s.1 :=
    (stableMem_rightComponents s.1).mpr ⟨γ.2, ⟨γ.2, h⟩⟩
  exact Finset.mem_image.mpr ⟨⟨γ.1, hmemRC⟩, Finset.mem_attach _ _, rfl⟩

/-- **body-639b (Step 2) — the right survivor lands in the LIVE quotient forest of `Q`.** -/
theorem stableFinalRightSurvivor_mem_quotientForest (s : StablePhi4MixedSplitChoice G hSt)
    (γ : StableOuterComponent s) (h : s.1.choice γ (Finset.mem_attach _ γ) = Sum.inl false) :
    stableRightSurvivor s.1 (⟨γ.2, h⟩ : stableIsRightComponent s.1 γ.1)
      ∈ (stableQuotientForest s).elements := by
  rw [stableQuotientForest_elements]
  exact Finset.mem_union_left _ (stableFinalRightSurvivor_mem_survivorForest s γ h)

/-- **body-639b (Step 2) — a decompleted remnant lands in the remnant forest of `Q`.** -/
theorem stableRemnantComponent_mem_remnantForest (s : StablePhi4MixedSplitChoice G hSt)
    (o : StableForestChoiceOccurrence s) :
    stableRemnantComponent o ∈ (stableRemnantForest s).elements := by
  rw [stableRemnantForest_elements]
  have hmemFC : o.γ.1 ∈ stableForestComponents s :=
    (stableMem_forestComponents s).mpr ⟨o.γ.2, o.γ.2, o.B, o.hchoice⟩
  refine Finset.mem_image.mpr ⟨⟨o.γ.1, hmemFC⟩, Finset.mem_attach _ _, ?_⟩
  exact congrArg stableRemnantComponent
    (stableForestOccurrence_ext_helper s _ o rfl)

/-- **body-639b (Step 2) — a decompleted remnant lands in the LIVE quotient forest of `Q`. -/
theorem stableRemnantComponent_mem_quotientForest (s : StablePhi4MixedSplitChoice G hSt)
    (o : StableForestChoiceOccurrence s) :
    stableRemnantComponent o ∈ (stableQuotientForest s).elements := by
  rw [stableQuotientForest_elements]
  exact Finset.mem_union_right _ (stableRemnantComponent_mem_remnantForest s o)

/-- A LEFT-chosen outer component is an element of `stableSelectedOuter`. -/
theorem stableOuterComponent_mem_selectedOuter_of_left (s : StablePhi4MixedSplitChoice G hSt)
    (γ : StableOuterComponent s) (h : s.1.choice γ (Finset.mem_attach _ γ) = Sum.inl true) :
    γ.1 ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G (stableSelectedOuter s.1) := by
  rw [stableSelectedOuter_elements]
  refine Finset.mem_union_left _ ?_
  rw [stableLeftOf_elements, Finset.mem_filter]
  exact ⟨γ.2, γ.2, h⟩

/-! ## Step 3 — the ambient classifier (the mathematical center) -/

/-- **body-639b (Step 3, CLASSIFIER) — final-star ambient ownership.**  The final two-stage star of an outer
component lies in the stable quotient ambient `Q = stableSelectedOuterContractGraph s.1` **iff** its choice is
`Sum.inl true` (LEFT).  A LEFT star is a first-stage `stableSelectedOuter` star of `γ` — a `Q` star-vertex; a
RIGHT / FOREST star is a second-stage canonical `Q`-quotient-forest star — FRESH, outside `Q.vertices`.  This
single lemma separates ALL LEFT-vs-non-LEFT cross cases. -/
theorem stableFinalTwoStageStar_mem_quotientAmbient_iff_left (s : StablePhi4MixedSplitChoice G hSt)
    (γ : StableOuterComponent s) :
    stableFinalTwoStageStar s γ ∈ (stableSelectedOuterContractGraph s.1).vertices
      ↔ s.1.choice γ (Finset.mem_attach _ γ) = Sum.inl true := by
  constructor
  · intro hmem
    cases hc : s.1.choice γ (Finset.mem_attach _ γ) with
    | inl b =>
      cases b with
      | true => rfl
      | false =>
        exfalso
        rw [stableFinalTwoStageStar_right s γ hc] at hmem
        exact stableRemnant_gen_star_not_mem (stableQuotientForest s)
          (stableQuotientForest_isProperForest s)
          (stableFinalRightSurvivor_mem_quotientForest s γ hc) hmem
    | inr B =>
      exfalso
      rw [stableFinalTwoStageStar_forest s γ B hc] at hmem
      exact stableRemnant_gen_star_not_mem (stableQuotientForest s)
        (stableQuotientForest_isProperForest s)
        (stableRemnantComponent_mem_quotientForest s ⟨γ, B, hc⟩) hmem
  · intro h
    rw [stableFinalTwoStageStar_left s γ h]
    have hmem : phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1) γ.1
        ∈ ((stableSelectedOuter s.1).contractWithStars
            (phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1))).vertices := by
      rw [ResolvedAdmissibleSubgraph.contractWithStars_vertices]
      exact Finset.mem_union_right _
        (ResolvedAdmissibleSubgraph.mem_starVertices.mpr
          ⟨γ.1, stableOuterComponent_mem_selectedOuter_of_left s γ h, rfl⟩)
    exact hmem

/-! ## Step 4 — sector injectivity -/

/-- **body-639b (Step 4) — LEFT-sector injectivity.** -/
theorem stableFinalTwoStageStar_left_injective (s : StablePhi4MixedSplitChoice G hSt)
    (γ₁ γ₂ : StableOuterComponent s)
    (h₁ : s.1.choice γ₁ (Finset.mem_attach _ γ₁) = Sum.inl true)
    (h₂ : s.1.choice γ₂ (Finset.mem_attach _ γ₂) = Sum.inl true)
    (he : stableFinalTwoStageStar s γ₁ = stableFinalTwoStageStar s γ₂) : γ₁ = γ₂ := by
  rw [stableFinalTwoStageStar_left s γ₁ h₁, stableFinalTwoStageStar_left s γ₂ h₂] at he
  exact Subtype.ext (stableRemnant_gen_star_injOn (stableSelectedOuter s.1)
    (stableSelectedOuter_isProperForest s.1)
    (stableOuterComponent_mem_selectedOuter_of_left s γ₁ h₁)
    (stableOuterComponent_mem_selectedOuter_of_left s γ₂ h₂) he)

/-- **body-639b (Step 4) — RIGHT-sector injectivity.** -/
theorem stableFinalTwoStageStar_right_injective (s : StablePhi4MixedSplitChoice G hSt)
    (γ₁ γ₂ : StableOuterComponent s)
    (h₁ : s.1.choice γ₁ (Finset.mem_attach _ γ₁) = Sum.inl false)
    (h₂ : s.1.choice γ₂ (Finset.mem_attach _ γ₂) = Sum.inl false)
    (he : stableFinalTwoStageStar s γ₁ = stableFinalTwoStageStar s γ₂) : γ₁ = γ₂ := by
  rw [stableFinalTwoStageStar_right s γ₁ h₁, stableFinalTwoStageStar_right s γ₂ h₂] at he
  have hsurv : stableRightSurvivor s.1 (⟨γ₁.2, h₁⟩ : stableIsRightComponent s.1 γ₁.1)
      = stableRightSurvivor s.1 (⟨γ₂.2, h₂⟩ : stableIsRightComponent s.1 γ₂.1) :=
    stableRemnant_gen_star_injOn (stableQuotientForest s) (stableQuotientForest_isProperForest s)
      (stableFinalRightSurvivor_mem_quotientForest s γ₁ h₁)
      (stableFinalRightSurvivor_mem_quotientForest s γ₂ h₂) he
  exact Subtype.ext (stableRightSurvivor_injOn s.1 ⟨γ₁.2, h₁⟩ ⟨γ₂.2, h₂⟩ hsurv)

/-- **body-639b (Step 4) — FOREST-sector injectivity.**  The OWNER equality is recovered directly from the
remnant-component equality (`stableRemnant_injOn`, contrapositive) — the dependent `B`-equality is NEVER solved. -/
theorem stableFinalTwoStageStar_forest_injective (s : StablePhi4MixedSplitChoice G hSt)
    (γ₁ γ₂ : StableOuterComponent s)
    (B₁ : StableLocalForestIdx γ₁.1) (h₁ : s.1.choice γ₁ (Finset.mem_attach _ γ₁) = Sum.inr B₁)
    (B₂ : StableLocalForestIdx γ₂.1) (h₂ : s.1.choice γ₂ (Finset.mem_attach _ γ₂) = Sum.inr B₂)
    (he : stableFinalTwoStageStar s γ₁ = stableFinalTwoStageStar s γ₂) : γ₁ = γ₂ := by
  rw [stableFinalTwoStageStar_forest s γ₁ B₁ h₁, stableFinalTwoStageStar_forest s γ₂ B₂ h₂] at he
  have hrem : stableRemnantComponent (⟨γ₁, B₁, h₁⟩ : StableForestChoiceOccurrence s)
      = stableRemnantComponent (⟨γ₂, B₂, h₂⟩ : StableForestChoiceOccurrence s) :=
    stableRemnant_gen_star_injOn (stableQuotientForest s) (stableQuotientForest_isProperForest s)
      (stableRemnantComponent_mem_quotientForest s ⟨γ₁, B₁, h₁⟩)
      (stableRemnantComponent_mem_quotientForest s ⟨γ₂, B₂, h₂⟩) he
  by_contra hne
  have hownerNe : (⟨γ₁, B₁, h₁⟩ : StableForestChoiceOccurrence s).γ.1
      ≠ (⟨γ₂, B₂, h₂⟩ : StableForestChoiceOccurrence s).γ.1 :=
    fun hoeq => hne (Subtype.ext hoeq)
  exact stableRemnant_injOn ⟨γ₁, B₁, h₁⟩ ⟨γ₂, B₂, h₂⟩ hownerNe hrem

/-- **body-639b (Step 4) — a RIGHT star and a FOREST star never coincide.**  The right survivor and the remnant
sit in the Finset-disjoint survivor / remnant forests (`stableSurvivorRemnant_elements_disjoint`), so their
canonical `Q`-quotient-forest stars are distinct (`starOf` injectivity would force a shared quotient element). -/
theorem stableFinalTwoStageStar_right_forest_ne (s : StablePhi4MixedSplitChoice G hSt)
    (γ₁ γ₂ : StableOuterComponent s)
    (h₁ : s.1.choice γ₁ (Finset.mem_attach _ γ₁) = Sum.inl false)
    (B₂ : StableLocalForestIdx γ₂.1) (h₂ : s.1.choice γ₂ (Finset.mem_attach _ γ₂) = Sum.inr B₂) :
    stableFinalTwoStageStar s γ₁ ≠ stableFinalTwoStageStar s γ₂ := by
  rw [stableFinalTwoStageStar_right s γ₁ h₁, stableFinalTwoStageStar_forest s γ₂ B₂ h₂]
  intro he
  have heq : stableRightSurvivor s.1 (⟨γ₁.2, h₁⟩ : stableIsRightComponent s.1 γ₁.1)
      = stableRemnantComponent (⟨γ₂, B₂, h₂⟩ : StableForestChoiceOccurrence s) :=
    stableRemnant_gen_star_injOn (stableQuotientForest s) (stableQuotientForest_isProperForest s)
      (stableFinalRightSurvivor_mem_quotientForest s γ₁ h₁)
      (stableRemnantComponent_mem_quotientForest s ⟨γ₂, B₂, h₂⟩) he
  have hS : stableRightSurvivor s.1 (⟨γ₁.2, h₁⟩ : stableIsRightComponent s.1 γ₁.1)
      ∈ (stableRightSurvivorForest s.1).elements :=
    stableFinalRightSurvivor_mem_survivorForest s γ₁ h₁
  rw [heq] at hS
  exact Finset.disjoint_left.mp (stableSurvivorRemnant_elements_disjoint s) hS
    (stableRemnantComponent_mem_remnantForest s ⟨γ₂, B₂, h₂⟩)

/-! ## Step 5 — global injectivity -/

/-- **body-639b (Step 5, HEADLINE INPUT 1) — the one-stage star is injective.** -/
theorem stableOneStageOuterStar_injective (s : StablePhi4MixedSplitChoice G hSt) :
    Function.Injective (stableOneStageOuterStar s) := by
  intro γ₁ γ₂ he
  exact Subtype.ext (stableRemnant_gen_star_injOn s.1.outer
    (((mem_phi4WTriplePrimeIndex G s.1.outer).mp s.1.outer_mem).2.2.2.2.1) γ₁.2 γ₂.2 he)

/-- **body-639b (Step 5, HEADLINE INPUT 2) — the final two-stage star is injective.**  A 3×3 choice-tag
classification: LEFT-vs-non-LEFT is impossible by the Step-3 ambient classifier (LEFT ∈ `Q.vertices`,
non-LEFT ∉ `Q.vertices`); RIGHT-vs-FOREST is impossible by quotient-forest separation
(`_right_forest_ne`); each diagonal case is the corresponding sector injectivity. -/
theorem stableFinalTwoStageStar_injective (s : StablePhi4MixedSplitChoice G hSt) :
    Function.Injective (stableFinalTwoStageStar s) := by
  intro γ₁ γ₂ he
  have hiff : s.1.choice γ₁ (Finset.mem_attach _ γ₁) = Sum.inl true
      ↔ s.1.choice γ₂ (Finset.mem_attach _ γ₂) = Sum.inl true := by
    rw [← stableFinalTwoStageStar_mem_quotientAmbient_iff_left s γ₁,
        ← stableFinalTwoStageStar_mem_quotientAmbient_iff_left s γ₂, he]
  cases hc₁ : s.1.choice γ₁ (Finset.mem_attach _ γ₁) with
  | inl b₁ =>
    cases b₁ with
    | true =>
      exact stableFinalTwoStageStar_left_injective s γ₁ γ₂ hc₁ (hiff.mp hc₁) he
    | false =>
      cases hc₂ : s.1.choice γ₂ (Finset.mem_attach _ γ₂) with
      | inl b₂ =>
        cases b₂ with
        | true => exact absurd (hc₁.symm.trans (hiff.mpr hc₂)) (by simp)
        | false => exact stableFinalTwoStageStar_right_injective s γ₁ γ₂ hc₁ hc₂ he
      | inr B₂ => exact absurd he (stableFinalTwoStageStar_right_forest_ne s γ₁ γ₂ hc₁ B₂ hc₂)
  | inr B₁ =>
    cases hc₂ : s.1.choice γ₂ (Finset.mem_attach _ γ₂) with
    | inl b₂ =>
      cases b₂ with
      | true => exact absurd ((hiff.mpr hc₂).symm.trans hc₁) (by simp)
      | false => exact absurd he.symm (stableFinalTwoStageStar_right_forest_ne s γ₂ γ₁ hc₂ B₁ hc₁)
    | inr B₂ => exact stableFinalTwoStageStar_forest_injective s γ₁ γ₂ B₁ hc₁ B₂ hc₂ he

/-! ## Step 6 — surviving-root freshness -/

/-- **body-639b (Step 6) — the two-stage surviving root vertices** (the input roots surviving the first
contraction): `G`-vertices outside `s.1.outer`. -/
def stableTwoStageSurvivingVertices (s : StablePhi4MixedSplitChoice G hSt) : Finset VertexId :=
  G.vertices \ s.1.outer.vertices

/-- `stableSelectedOuter`'s vertices sit inside `s.1.outer`'s (each component is an outer component or a promoted
lift of one). -/
theorem stableSelectedOuter_vertices_subset_outer (s : StablePhi4MixedSplitChoice G hSt) :
    (stableSelectedOuter s.1).vertices ⊆ s.1.outer.vertices := by
  intro v hv
  rw [ResolvedAdmissibleSubgraph.mem_vertices] at hv ⊢
  obtain ⟨c, hc, hvc⟩ := hv
  rcases stableSelectedOuter_component_origin s.1 hc with ⟨hcmem, -⟩ | ⟨g, hg, B, -, δ, hδ, rfl⟩
  · exact ⟨c, hcmem, hvc⟩
  · exact ⟨g, hg, stableRootRelativeInner_vertices_subset g δ hvc⟩

/-- **body-639b (Step 6) — the surviving roots survive the first contraction: they land in `Q.vertices`.** -/
theorem stableTwoStageSurvivingVertices_subset_Q (s : StablePhi4MixedSplitChoice G hSt) :
    stableTwoStageSurvivingVertices s ⊆ (stableSelectedOuterContractGraph s.1).vertices := by
  intro v hv
  rw [stableTwoStageSurvivingVertices, Finset.mem_sdiff] at hv
  obtain ⟨hvG, hvOut⟩ := hv
  have hvSel : v ∉ (stableSelectedOuter s.1).vertices :=
    fun hc => hvOut (stableSelectedOuter_vertices_subset_outer s hc)
  have hmem : v ∈ ((stableSelectedOuter s.1).contractWithStars
      (phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1))).vertices := by
    rw [ResolvedAdmissibleSubgraph.contractWithStars_vertices]
    exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hvG, hvSel⟩)
  exact hmem

/-- **body-639b (Step 6, HEADLINE INPUT 3) — one-stage stars avoid the surviving roots.**  The one-stage star is
fresh (outside `G`), while the surviving roots are `G`-vertices. -/
theorem stableOneStageOuterStar_not_mem_survivors (s : StablePhi4MixedSplitChoice G hSt)
    (γ : StableOuterComponent s) :
    stableOneStageOuterStar s γ ∉ stableTwoStageSurvivingVertices s := by
  intro hmem
  have hG : stableOneStageOuterStar s γ ∈ G.vertices := (Finset.mem_sdiff.mp hmem).1
  exact stableRemnant_gen_star_not_mem s.1.outer
    (((mem_phi4WTriplePrimeIndex G s.1.outer).mp s.1.outer_mem).2.2.2.2.1) γ.2 hG

/-- **body-639b (Step 6, HEADLINE INPUT 4) — final stars avoid the surviving roots.**  A LEFT final star is fresh
outside `G` (hence outside the surviving roots ⊆ `G.vertices`); a RIGHT / FOREST final star is fresh outside `Q`,
and the surviving roots land in `Q.vertices` (Step 6). -/
theorem stableFinalTwoStageStar_not_mem_survivors (s : StablePhi4MixedSplitChoice G hSt)
    (γ : StableOuterComponent s) :
    stableFinalTwoStageStar s γ ∉ stableTwoStageSurvivingVertices s := by
  intro hmem
  cases hc : s.1.choice γ (Finset.mem_attach _ γ) with
  | inl b =>
    cases b with
    | true =>
      have hG : stableFinalTwoStageStar s γ ∈ G.vertices := (Finset.mem_sdiff.mp hmem).1
      rw [stableFinalTwoStageStar_left s γ hc] at hG
      exact stableRemnant_gen_star_not_mem (stableSelectedOuter s.1)
        (stableSelectedOuter_isProperForest s.1)
        (stableOuterComponent_mem_selectedOuter_of_left s γ hc) hG
    | false =>
      have hQ := stableTwoStageSurvivingVertices_subset_Q s hmem
      rw [stableFinalTwoStageStar_right s γ hc] at hQ
      exact stableRemnant_gen_star_not_mem (stableQuotientForest s)
        (stableQuotientForest_isProperForest s)
        (stableFinalRightSurvivor_mem_quotientForest s γ hc) hQ
  | inr B =>
    have hQ := stableTwoStageSurvivingVertices_subset_Q s hmem
    rw [stableFinalTwoStageStar_forest s γ B hc] at hQ
    exact stableRemnant_gen_star_not_mem (stableQuotientForest s)
      (stableQuotientForest_isProperForest s)
      (stableRemnantComponent_mem_quotientForest s ⟨γ, B, hc⟩) hQ

end GaugeGeometry.QFT.Combinatorial
