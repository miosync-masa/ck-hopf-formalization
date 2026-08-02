import GaugeGeometry.QFT.HopfAlgebra.Phi4StableForestAlignedInnerForest

/-!
# QFT-R1-body-647c — the FULL STABLE forest-block LEFT inverse `inverse ∘ forward = id`

Body-646 delivered the STABLE forest-block RIGHT inverse (`forward ∘ inverse = id`); bodies 647a / 647b-1 /
647b-2 finished the FOREST parent (`stableForwardForest_recoveredParent_eq`), the aligned inner elements, and
the exact FOREST `Sum.inr o.B` choice payload (`stableForwardAligned_recoveredChoice_eq`).  THIS body is the
ASSEMBLY: it reconstructs the source stable mixed split choice `s` from `stableForestBlockForward s` and proves

    stableRecoveredSplitChoice hSt (stableForestBlockForward s) = s

It MIRRORS the OLD body-622b-3 PROOF SHAPE, but on the STABLE carrier and **without** a stable component `Equiv`
(none exists): every quotient component is classified DIRECTLY via body-637's `stableQuotientForest_element_cases`,
and RIGHT witnesses are built from body-634's `stableRightSurvivor` (+ body-646's
`stableRightSurvivor_mem_quotientForest`).  The OLD 622b-3 terms are NEVER consumed — only the proof shape is
mirrored.

## Steps
* **Step 1 (bridge)** — `stableForwardBlock_star_mem_remnant_iff`: a `stableSelectedOuter` component's canonical
  star lands in the remnant of `o` iff any of its vertices lies in `o`'s owner.  Pure membership transport of
  body-635's `stableRemnant_phi_mem_Ltau_iff` across `stableRemnant_retargetVertex_eq_star`; NO τ value / equality.
* **Step 2 (RIGHT)** — `stableForwardBlock_right_not_forestImage` (the survivor is star-free: its vertices ⊆ `G`,
  the selectedOuter canonical star is FRESH ∉ `G`) + `stableForwardBlock_regionComponentOf_right` (the survivor's
  recovered region is its source RIGHT component, all three carrier fields).
* **Step 3 (FOREST)** — `stableForwardBlock_regionComponentOf_forest`: a remnant's recovered region is its
  occurrence owner `o.γ.1` (thin adapter over 647a `stableForwardForest_recoveredParent_eq` + 647a
  `stableRemnant_star_touching`).
* **Step 4 (LEFT)** — `stableForwardBlock_left_mem_selectedOuter` + `stableForwardBlock_left_isLeftComponent`:
  a `Sum.inl true` component stays in `stableSelectedOuter` and is a LEFT component of the forward package (its
  star touches no quotient component — survivors are star-free, remnants only via the Step-1 bridge + owner
  disjointness + choice-tag mismatch).  Classification is by `stableQuotientForest_element_cases`, NO component
  `Equiv`.
* **Step 5 (OUTER)** — `stableRecoveredOuter_forestBlockForward : recoveredOuter … = s.1.outer` (clean
  element-set ext).  Forward: LEFT origin (`stableSelectedOuter_component_origin`; promoted branch contradicts
  via Step 1) or region origin (`stableQuotientForest_element_cases` → Step 2 / Step 3).  Reverse: `s.1.choice`
  three-way.
* **Step 6 (CHOICE)** — `stableRecoveredChoice_forestBlockForward`: pointwise (transport-free) recovered-choice =
  `s.1.choice`, three-branch (RIGHT via Step 2 + `dif`; LEFT via `stableRecoveredChoice_left` + Step 4; FOREST via
  647b-2 `stableForwardAligned_recoveredChoice_eq`).
* **Step 7 (HEADLINE)** — `stableRecoveredSplitChoice_forestBlockForward` via the generic independent-target
  assemble `stableForestBlock_leftAssemble` (destructure the mixed subtype target `w`, `subst` its INDEPENDENT
  outer variable so the two choice domains become judgmentally identical, then `funext`; the `Prop` subtype /
  nontriviality fields are proof-irrelevant).

## Ownership boundary — MUST NOT consume as terms
The OLD 622b-3 `phi4WTriplePrime_forwardBlock_*` / `_recoveredOuter_forestBlockForward` /
`_recoveredChoice_forestBlockForward` / `_forestBlock_leftAssemble` / `_recoveredSplitChoice_forestBlockForward`
are NEVER consumed (proof shape mirrored only).  Reused AS STATED: body-647b-2
`stableForwardAligned_recoveredChoice_eq`; body-647a `stableForwardForest_recoveredParent_eq` /
`stableRemnant_star_touching`; body-646 `stableRightSurvivor_mem_quotientForest`; body-643
`stableRecoveredChoice{,_left}` / `stableRecoveredSplitChoice` / `stableRecoveredResolvedSplitChoice`; body-640
`stableForestBlockForward{,_fst,_snd}`; body-637 `stableQuotientForest{,_element_cases}`; body-635
`StablePhi4MixedSplitChoice` / `StableForestChoiceOccurrence` / `stableRemnantComponent{,_vertices}` /
`stableRemnant_phi_mem_Ltau_iff` / `stableRemnant_retargetVertex_eq_star` / `stableRemnant_promoted_mem`; body-634
`stableRightSurvivor{,_vertices,_internalEdges,_externalLegs}` / `stableIsRightComponent` /
`stableSelectedOuter{,_star_not_mem_vertices}`; body-632 `stableSelectedOuter_elements{,_component_origin}` /
`stableRootRelativeInner_vertices{,_subset}`; the completion-INDEPENDENT inverse scaffolding
(`phi4WTriplePrime_recoveredOuter{,_component_origin,_mem}` / `phi4WTriplePrime_inv_regionComponentOf{,_eq_right,
_eq_parent,_injective}` / `phi4WTriplePrime_inv_isForestImage` / `phi4WTriplePrime_inv_isLeftComponent` /
`phi4WTriplePrime_recoveredRight_{vertices,internalEdges,externalLegs}` /
`phi4WTriplePrime_inv_left_mem_recoveredOuter` / `phi4WTriplePrime_mem_recoveredOuter_elements`).

## HALT / red lines
NO stable component `Equiv` pre-empt (RIGHT witnesses from `stableRightSurvivor` DIRECTLY).  ZERO public `HEq` /
`cast` / graph-data `▸` — the ONLY `▸` is a Prop-level rewrite (`hsub ▸ htrue`, a subtype-equality-driven rewrite
of a choice equation, the sanctioned old-622b-3 shape).  The ONLY `subst` is on the INDEPENDENT `w` outer
variable (Step 7) after destructuring; NO `subst` between FIXED owners.  NO τ / ID / degree / CD / recontraction
re-proof; NO orbit quotient / dedup.  NO `Bijective` / bare `Equiv` / `sum_bij` / alpha / coassoc (those are
648/649).  ZERO forbidden divergence class in any declaration TYPE (a clean `private` element-set ext is
re-derived).  ZERO new `structure` / `class` / permanent `instance` (one file-local `local instance`; the clean
ext is `private`).  NO `sorry` / `admit` / `native_decide`.  Axiom-clean (`propext`, `Classical.choice`,
`Quot.sound`).
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

open ResolvedFeynmanSubgraph

variable {G : ResolvedFeynmanGraph}

set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-- The concrete φ⁴ divergence measure family, registered file-locally (providable instance, NO forbidden
class). -/
noncomputable local instance instPhi4DivergenceMeasureFamily647c :
    (H : FeynmanGraph) → DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

variable {hSt : StableResolvedBoundaryIds G} {s : StablePhi4MixedSplitChoice G hSt}

/-! ## Step 0 — file-local clean element-set ext (bypasses the polluted public ext) -/

/-- **body-647c (Step 0, PRIVATE) — a clean element-set extensionality for φ⁴ admissible subgraphs.**  Bypasses
the `[IsAmbientInvariantDivergence]`-polluted public ext: the two non-`elements` fields are `Prop`s, so equal
element sets force equality by `cases` + definitional proof irrelevance.  NO forbidden divergence class in the
type.  PRIVATE (mirror of body-644 / 646 clean ext). -/
private theorem stableForestBlockLeft_admissible_ext_elements {H : ResolvedFeynmanGraph}
    {A₁ A₂ : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily H}
    (h : @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily H A₁
       = @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily H A₂) : A₁ = A₂ := by
  cases A₁; cases A₂; cases h; rfl

/-! ## Step 1 — shared star / remnant bridge (reuses body-635's KEY membership iff — NO new geometry) -/

/-- **body-647c (Step 1, bridge) — a `stableSelectedOuter` component's star lands in the remnant of `o` iff any
of its vertices lies in `o`'s owner.**  Pure membership transport of body-635's `stableRemnant_phi_mem_Ltau_iff`
across `stableRemnant_retargetVertex_eq_star`; no geometry is re-proved. -/
theorem stableForwardBlock_star_mem_remnant_iff
    (o : StableForestChoiceOccurrence s) {c : ResolvedFeynmanSubgraph G}
    (hc : c ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G
        (stableSelectedOuter s.1))
    {v : VertexId} (hvc : v ∈ c.vertices) :
    phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1) c
        ∈ (stableRemnantComponent o).vertices
      ↔ v ∈ o.γ.1.vertices := by
  rw [stableRemnantComponent_vertices,
      ← stableRemnant_retargetVertex_eq_star (stableSelectedOuter s.1)
        (phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1)) hc hvc]
  exact stableRemnant_phi_mem_Ltau_iff o (c.vertices_subset hvc)

/-! ## Step 2 — RIGHT owner recovery (the survivor is star-free + recovers its right component) -/

/-- **body-647c (Step 2) — the forward package's survivor is a RIGHT (star-free) image.**  Its vertices are the
source RIGHT component's (⊆ `G`), while the `stableSelectedOuter` canonical star is FRESH (∉ `G`).  RIGHT witness
built DIRECTLY from `stableRightSurvivor` — NO component `Equiv`.  Mirror of body-608 survivor-not-forestImage. -/
theorem stableForwardBlock_right_not_forestImage {γ : ResolvedFeynmanSubgraph G}
    (hγR : stableIsRightComponent s.1 γ) :
    ¬ phi4WTriplePrime_inv_isForestImage (stableForestBlockForward s)
      ⟨stableRightSurvivor s.1 hγR, stableRightSurvivor_mem_quotientForest hγR⟩ := by
  rintro ⟨v, hv, hstar⟩
  rw [stableRightSurvivor_vertices] at hv
  obtain ⟨c, hc, hceq⟩ := ResolvedAdmissibleSubgraph.mem_starVertices.mp hstar
  have hvG : v ∈ G.vertices := γ.vertices_subset hv
  rw [← hceq] at hvG
  exact stableSelectedOuter_star_not_mem_vertices s.1 hc hvG

/-- **body-647c (Step 2) — a survivor's recovered region component is its original right component.**  For a
RIGHT component `γ`, `regionComponentOf (forestBlockForward s) ⟨survivor, _⟩ = γ` (star-free, then all three
carrier fields via body-634 survivor anchors). -/
theorem stableForwardBlock_regionComponentOf_right {γ : ResolvedFeynmanSubgraph G}
    (hγR : stableIsRightComponent s.1 γ) :
    phi4WTriplePrime_inv_regionComponentOf (stableForestBlockForward s)
        ⟨stableRightSurvivor s.1 hγR, stableRightSurvivor_mem_quotientForest hγR⟩ = γ := by
  rw [phi4WTriplePrime_inv_regionComponentOf_eq_right (stableForestBlockForward s)
      (stableForwardBlock_right_not_forestImage hγR)]
  refine ResolvedFeynmanSubgraph.ext ?_ ?_ ?_
  · rw [phi4WTriplePrime_recoveredRight_vertices, stableRightSurvivor_vertices]
  · rw [phi4WTriplePrime_recoveredRight_internalEdges, stableRightSurvivor_internalEdges]
  · rw [phi4WTriplePrime_recoveredRight_externalLegs, stableRightSurvivor_externalLegs]

/-! ## Step 3 — FOREST owner recovery (the remnant recovers its occurrence owner) -/

/-- **body-647c (Step 3) — a remnant's recovered region component is its occurrence owner.**  For
`o : StableForestChoiceOccurrence s`, `regionComponentOf (forestBlockForward s) ⟨remnant o, _⟩ = o.γ.1` (a thin
adapter over 647a `stableForwardForest_recoveredParent_eq` via the star-touching from 647a
`stableRemnant_star_touching`).  NO new geometry. -/
theorem stableForwardBlock_regionComponentOf_forest (o : StableForestChoiceOccurrence s) :
    phi4WTriplePrime_inv_regionComponentOf (stableForestBlockForward s)
        ⟨stableRemnantComponent o, stableRemnantComponent_mem_quotientForest s o⟩ = o.γ.1 := by
  rw [phi4WTriplePrime_inv_regionComponentOf_eq_parent (stableForestBlockForward s)
      (stableRemnant_star_touching s o)]
  exact stableForwardForest_recoveredParent_eq s o

/-! ## Step 4 — LEFT: a `Sum.inl true` component is a star-untouched `stableSelectedOuter` component -/

/-- **body-647c (Step 4) — a `Sum.inl true` component stays in `stableSelectedOuter`.** -/
theorem stableForwardBlock_left_mem_selectedOuter {γ : ResolvedFeynmanSubgraph G}
    (hγ : γ ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G s.1.outer)
    (htrue : s.1.choice ⟨γ, hγ⟩ (Finset.mem_attach _ _) = Sum.inl true) :
    γ ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G
      (stableSelectedOuter s.1) := by
  rw [stableSelectedOuter_elements, Finset.mem_union]
  refine Or.inl ?_
  rw [stableLeftOf_elements, Finset.mem_filter]
  exact ⟨hγ, ⟨hγ, htrue⟩⟩

/-- **body-647c (Step 4) — a `Sum.inl true` component is a LEFT component of `stableForestBlockForward s`.**  Its
canonical star touches no quotient component: survivors are star-free (their vertices ⊆ `G`, the star is fresh),
remnants only via the Step-1 bridge (owner-vertex membership contradicting source outer pairwise-disjointness +
the choice-tag mismatch `Sum.inl true ≠ Sum.inr B`).  Classification is by `stableQuotientForest_element_cases`
— NO component `Equiv`. -/
theorem stableForwardBlock_left_isLeftComponent {γ : ResolvedFeynmanSubgraph G}
    (hγ : γ ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G s.1.outer)
    (htrue : s.1.choice ⟨γ, hγ⟩ (Finset.mem_attach _ _) = Sum.inl true) :
    phi4WTriplePrime_inv_isLeftComponent (stableForestBlockForward s) γ := by
  have hsel : γ ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G
      (stableSelectedOuter s.1) :=
    stableForwardBlock_left_mem_selectedOuter hγ htrue
  intro δ' hmem
  rcases stableQuotientForest_element_cases s δ'.2 with ⟨γ'', hγ''R, hδeq⟩ | ⟨o, hδeq⟩
  · -- survivor: star-free (fresh star vs. `G`-native survivor vertices)
    rw [hδeq, stableRightSurvivor_vertices] at hmem
    exact stableSelectedOuter_star_not_mem_vertices s.1 hsel (γ''.vertices_subset hmem)
  · -- remnant: the star maps to the owner, forcing `γ = o.γ.1` (impossible: choices differ)
    rw [hδeq] at hmem
    have houterProper : @ResolvedAdmissibleSubgraph.IsProperForest phi4DivergenceMeasureFamily G
        s.1.outer :=
      ((mem_phi4WTriplePrimeIndex G s.1.outer).mp s.1.outer_mem).2.2.2.2.1
    obtain ⟨v, hv⟩ := Finset.card_pos.mp (houterProper.2.1 γ hγ)
    have hvowner := (stableForwardBlock_star_mem_remnant_iff o hsel hv).mp hmem
    have hne : γ ≠ o.γ.1 := by
      intro h
      have hsub : (⟨γ, hγ⟩ : {x // x ∈ @ResolvedAdmissibleSubgraph.elements
          phi4DivergenceMeasureFamily G s.1.outer}) = o.γ := Subtype.ext h
      have e1 := hsub ▸ htrue
      rw [o.hchoice] at e1
      exact absurd e1 (by simp)
    exact Finset.disjoint_left.mp (s.1.outer.pairwiseDisjoint hγ o.γ.2 hne) hv hvowner

/-! ## Step 5 — TARGET: `recoveredOuter (forestBlockForward s) = s.1.outer` -/

/-- **body-647c (Step 5, HEADLINE) — the recovered outer forest of `stableForestBlockForward s` is `s.1.outer`.**
A clean admissible element-set ext.  Forward inclusion classifies a recovered component as a LEFT
`stableSelectedOuter` component (`stableSelectedOuter_component_origin`; the promoted case is impossible by the
Step-1 bridge) or a quotient region (via `stableQuotientForest_element_cases` → RIGHT `= γ''` (Step 2) / FOREST
`= o.γ.1` (Step 3)).  Reverse inclusion branches `s.1.choice` on `true / false / forest`.  NO component `Equiv`,
NO dedup, NO orbit quotient. -/
theorem stableRecoveredOuter_forestBlockForward (s : StablePhi4MixedSplitChoice G hSt) :
    phi4WTriplePrime_recoveredOuter (stableForestBlockForward s) = s.1.outer := by
  apply stableForestBlockLeft_admissible_ext_elements
  apply Finset.ext
  intro γ
  constructor
  · -- forward: recovered component ⇒ s.1.outer component
    intro hγrec
    rcases phi4WTriplePrime_recoveredOuter_component_origin (stableForestBlockForward s) hγrec
      with ⟨hγsel, hL⟩ | ⟨δq, hδeq⟩
    · -- LEFT stableSelectedOuter component
      rcases stableSelectedOuter_component_origin s.1 hγsel with ⟨hγouter, -⟩ | hP
      · exact hγouter
      · exfalso
        obtain ⟨γ', hγ', B, hchoice, δ, hδ, hγeq⟩ := hP
        obtain ⟨v, hv⟩ := Finset.card_pos.mp
          ((stableForestOcc_B_isProperForest
            (⟨⟨γ', hγ'⟩, B, hchoice⟩ : StableForestChoiceOccurrence s)).2.1 δ hδ)
        have hvc : v ∈ (stableRootRelativeInner γ' δ).vertices := by
          rw [stableRootRelativeInner_vertices]; exact hv
        have hstar := (stableForwardBlock_star_mem_remnant_iff
            (⟨⟨γ', hγ'⟩, B, hchoice⟩ : StableForestChoiceOccurrence s)
            (stableRemnant_promoted_mem
              (⟨⟨γ', hγ'⟩, B, hchoice⟩ : StableForestChoiceOccurrence s) hδ) hvc).mpr
            (stableRootRelativeInner_vertices_subset γ' δ hvc)
        have hcontra := hL ⟨stableRemnantComponent
            (⟨⟨γ', hγ'⟩, B, hchoice⟩ : StableForestChoiceOccurrence s),
            stableRemnantComponent_mem_quotientForest s
              (⟨⟨γ', hγ'⟩, B, hchoice⟩ : StableForestChoiceOccurrence s)⟩
        rw [hγeq] at hcontra
        exact hcontra hstar
    · -- quotient region component: classify via element cases (NO component Equiv)
      rcases stableQuotientForest_element_cases s δq.2 with ⟨γ'', hγ''R, hsurv⟩ | ⟨o, hrem⟩
      · have hδsub : δq = ⟨stableRightSurvivor s.1 hγ''R, stableRightSurvivor_mem_quotientForest hγ''R⟩ :=
          Subtype.ext hsurv
        rw [← hδeq, hδsub, stableForwardBlock_regionComponentOf_right hγ''R]
        exact hγ''R.choose
      · have hδsub : δq = ⟨stableRemnantComponent o, stableRemnantComponent_mem_quotientForest s o⟩ :=
          Subtype.ext hrem
        rw [← hδeq, hδsub, stableForwardBlock_regionComponentOf_forest o]
        exact o.γ.2
  · -- reverse: s.1.outer component ⇒ recovered component
    intro hγ
    rcases hbr : s.1.choice ⟨γ, hγ⟩ (Finset.mem_attach _ _) with b | B
    · rcases b with _ | _
      · -- Sum.inl false → RIGHT
        have hγR : stableIsRightComponent s.1 γ := ⟨hγ, hbr⟩
        exact (phi4WTriplePrime_mem_recoveredOuter_elements (stableForestBlockForward s)).mpr
          (Or.inr ⟨⟨stableRightSurvivor s.1 hγR, stableRightSurvivor_mem_quotientForest hγR⟩,
            stableForwardBlock_regionComponentOf_right hγR⟩)
      · -- Sum.inl true → LEFT
        exact phi4WTriplePrime_inv_left_mem_recoveredOuter (stableForestBlockForward s)
          (stableForwardBlock_left_mem_selectedOuter hγ hbr)
          (stableForwardBlock_left_isLeftComponent hγ hbr)
    · -- Sum.inr B → FOREST
      exact (phi4WTriplePrime_mem_recoveredOuter_elements (stableForestBlockForward s)).mpr
        (Or.inr ⟨⟨stableRemnantComponent (⟨⟨γ, hγ⟩, B, hbr⟩ : StableForestChoiceOccurrence s),
            stableRemnantComponent_mem_quotientForest s
              (⟨⟨γ, hγ⟩, B, hbr⟩ : StableForestChoiceOccurrence s)⟩,
          stableForwardBlock_regionComponentOf_forest
            (⟨⟨γ, hγ⟩, B, hbr⟩ : StableForestChoiceOccurrence s)⟩)

/-! ## Step 6 — the recovered choice equals `s.1.choice` (transport-free, pointwise) -/

/-- **body-647c (Step 6, HEADLINE) — the recovered global choice of `stableForestBlockForward s` equals
`s.1.choice`.**  Pointwise and transport-FREE (the value type `Bool ⊕ StableLocalForestIdx γ` is membership
independent): LEFT → `stableRecoveredChoice_left` = `Sum.inl true`; RIGHT → `Sum.inl false` (Step 2 survivor +
the `dif` unfolding); FOREST → `Sum.inr B` plugging body-647b-2's `stableForwardAligned_recoveredChoice_eq`
DIRECTLY. -/
theorem stableRecoveredChoice_forestBlockForward (s : StablePhi4MixedSplitChoice G hSt) :
    ∀ (γ : ResolvedFeynmanSubgraph G)
      (h1 : γ ∈ (phi4WTriplePrime_recoveredOuter (stableForestBlockForward s)).elements)
      (h2 : γ ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G s.1.outer),
      stableRecoveredChoice hSt (stableForestBlockForward s) ⟨γ, h1⟩ (Finset.mem_attach _ _)
        = s.1.choice ⟨γ, h2⟩ (Finset.mem_attach _ _) := by
  intro γ h1 h2
  rcases hbr : s.1.choice ⟨γ, h2⟩ (Finset.mem_attach _ _) with b | B
  · rcases b with _ | _
    · -- RIGHT: value `Sum.inl false`
      have hγR : stableIsRightComponent s.1 γ := ⟨h2, hbr⟩
      have hfree : ¬ phi4WTriplePrime_inv_isForestImage (stableForestBlockForward s)
          ⟨stableRightSurvivor s.1 hγR, stableRightSurvivor_mem_quotientForest hγR⟩ :=
        stableForwardBlock_right_not_forestImage hγR
      have hstep2 : phi4WTriplePrime_inv_regionComponentOf (stableForestBlockForward s)
          ⟨stableRightSurvivor s.1 hγR, stableRightSurvivor_mem_quotientForest hγR⟩ = γ :=
        stableForwardBlock_regionComponentOf_right hγR
      show stableRecoveredChoice hSt (stableForestBlockForward s) ⟨γ, h1⟩
          (Finset.mem_attach _ _) = Sum.inl false
      unfold stableRecoveredChoice
      have hq : ∃ δ : {x // x ∈ (stableForestBlockForward s).2.1.elements},
          phi4WTriplePrime_inv_regionComponentOf (stableForestBlockForward s) δ = γ :=
        ⟨⟨stableRightSurvivor s.1 hγR, stableRightSurvivor_mem_quotientForest hγR⟩, hstep2⟩
      rw [dif_pos hq, dif_neg (show ¬ phi4WTriplePrime_inv_isForestImage
          (stableForestBlockForward s) hq.choose by
        rw [phi4WTriplePrime_inv_regionComponentOf_injective (stableForestBlockForward s)
          (hq.choose_spec.trans hstep2.symm)]; exact hfree)]
    · -- LEFT: value `Sum.inl true`
      exact stableRecoveredChoice_left hSt (stableForestBlockForward s)
        (stableForwardBlock_left_mem_selectedOuter h2 hbr)
        (stableForwardBlock_left_isLeftComponent h2 hbr) (Finset.mem_attach _ _)
  · -- FOREST: value `Sum.inr B` (body-647b-2 payload)
    exact stableForwardAligned_recoveredChoice_eq
      (⟨⟨γ, h2⟩, B, hbr⟩ : StableForestChoiceOccurrence s) h1

/-! ## Step 7 — the generic independent-target assemble + the headline left inverse -/

/-- **body-647c (Step 7 helper) — the generic split-choice assemble.**  GENERIC in an INDEPENDENT mixed target
`w`, so destructuring `w` (the mixed SUBTYPE wrapper + the resolved structure) and `subst`-ing the outer
equality aligns the two recovered/`w` choice domains JUDGMENTALLY (no occurs-check, no transport), whence the
choice `funext` closes from the transport-free pointwise hypothesis and the remaining `Prop` fields
(nontriviality + the mixed not-all-LEFT witness) are proof-irrelevant. -/
theorem stableForestBlock_leftAssemble (s w : StablePhi4MixedSplitChoice G hSt)
    (hA : phi4WTriplePrime_recoveredOuter (stableForestBlockForward s) = w.1.outer)
    (hc : ∀ (γ : ResolvedFeynmanSubgraph G)
        (h1 : γ ∈ (phi4WTriplePrime_recoveredOuter (stableForestBlockForward s)).elements)
        (h2 : γ ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G w.1.outer),
        stableRecoveredChoice hSt (stableForestBlockForward s) ⟨γ, h1⟩ (Finset.mem_attach _ _)
          = w.1.choice ⟨γ, h2⟩ (Finset.mem_attach _ _)) :
    stableRecoveredSplitChoice hSt (stableForestBlockForward s) = w := by
  obtain ⟨⟨wouter, wmem, wchoice, wcnt⟩, wfilt⟩ := w
  simp only at hA hc
  subst hA
  have hchoice : stableRecoveredChoice hSt (stableForestBlockForward s) = wchoice := by
    funext γ hγ
    exact hc γ.1 γ.2 γ.2
  subst hchoice
  rfl

/-- **body-647c (Step 7, HEADLINE) — the FULL STABLE forest-block LEFT inverse.**  The source-independent stable
recovered inverse applied to `stableForestBlockForward s` returns `s` EXACTLY.  ONLY hypothesis `s`; the outer
equality (Step 5) and the transport-free choice equality (Step 6) are assembled through the generic
independent-target `stableForestBlock_leftAssemble` (destructure the mixed subtype `w` + `subst` its INDEPENDENT
outer variable → judgmental choice domains → `funext`; the `Prop` fields by proof irrelevance). -/
theorem stableRecoveredSplitChoice_forestBlockForward (s : StablePhi4MixedSplitChoice G hSt) :
    stableRecoveredSplitChoice hSt (stableForestBlockForward s) = s :=
  stableForestBlock_leftAssemble s s
    (stableRecoveredOuter_forestBlockForward s)
    (stableRecoveredChoice_forestBlockForward s)

end GaugeGeometry.QFT.Combinatorial
