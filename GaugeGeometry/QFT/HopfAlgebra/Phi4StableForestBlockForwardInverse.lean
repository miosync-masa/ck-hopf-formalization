import GaugeGeometry.QFT.HopfAlgebra.Phi4StableForwardInverseForestReconciliation

/-!
# QFT-R1-body-646 — the STABLE forest-block RIGHT inverse `forward ∘ inverse = id`

Body-644 proved the forward map's OUTER coordinate `stableSelectedOuter (recoveredResolved) = z.1.1`; body-645b
proved the FOREST completion reconciliation
`stableLocalBoundaryCompletedGraph (stableRemnantComponent (recoveredForwardOccurrence)) =
 stableLocalBoundaryCompletedGraph δ.1`.  This body assembles the FULL Sigma RIGHT inverse
`stableForestBlockForward (stableRecoveredSplitChoice hSt z) = z`.  It MIRRORS the OLD body-621 proof shape on the
STABLE carrier; the OLD quotient / remnant / survivor / assemble terms are NEVER consumed (mirror only).

## The Sigma-fiber alignment mechanism (Step 2)

The headline is bundled through `Sigma.ext` ONCE, but the ambient alignment is deferred to a lemma
`stableForestBlock_assemble` that is GENERIC in a split choice `s` and an ARBITRARY codomain `z` (independent
variables) plus the outer equality `hA : stableSelectedOuter s.1 = z.1.1`.  Because `s` and `z` are independent
there, `obtain ⟨⟨A₁, _⟩, _⟩ := z` makes `z.1.1 = A₁` a genuine local variable and `subst hA` eliminates it (NO
circularity — the recovered `s` is only substituted at the headline call site), making the quotient ambient
JUDGMENTALLY aligned.  The `Sigma.ext` fiber HEq is then discharged by `heq_of_eq` on the now-homogeneous `Eq`
(NO hand-written `cast` / `Eq.ndrec` / graph-data `▸`).

## Steps
* **Step 1 (FOREST fields)** — `stableRecoveredForward_remnant_{vertices,internalEdges,externalLegs}`: project
  body-645b's completion HEADLINE to the three component fields.  vertices / internalEdges via `congrArg` +
  body-629 completion projections; externalLegs via ambient-leg-filter saturation of BOTH sides (body-636
  remnant saturation, `z.2.2` W‴ saturation of `δ.1`) over the identified ambient (body-644 outer equality).
* **Step 2 (assemble)** — `stableForestBlock_assemble`: destructure `z`, `subst` the INDEPENDENT `A₁`, clean
  element-ext `stableQuotientForest s = B₁` (a `private` clean admissible ext), `Sigma.ext` fiber via
  `heq_of_eq`.
* **Step 3 (forward)** — `stableQuotientForest_recoveredSplitChoice_fwd`: classify each quotient component
  (survivor ↔ star-free right; remnant ↔ star-touching forest) via `stableQuotientForest_element_cases` +
  recovered-outer `component_origin` with choice-tag contradictions.
* **Step 4 (reverse)** — `stableQuotientForest_recoveredSplitChoice_rev`: classify each `z.2.1` component by star
  incidence (star-free → recovered right survivor; star-touching → recovered forward remnant).
* **Step 5** — `stableQuotientForest_recoveredSplitChoice`: the ambient-free two-directional correspondence.
* **Step 6 (HEADLINE)** — `stableForestBlockForward_recoveredSplitChoice`.

## Ownership boundary — MUST NOT consume as terms
The OLD 621 `phi4WTriplePrime_quotientForest` / `remnantComponent` / `survivor` / `forestBlock_assemble` are
NEVER consumed (proof shape mirrored).  Body-644's occurrence + outer equality, body-645b's completion
reconciliation, body-640's forward package, body-637's quotient forest + element cases, body-636's remnant
forest + saturation, body-634's survivor anchors, body-643's recovered split choice + tags, and the
completion-INDEPENDENT inverse scaffolding (`recoveredOuter` / `regionComponentOf` / `recoveredRight` /
`isForestImage` / the outer-membership BANK) are reused AS STATED.

## HALT / red lines
NO public cross-ambient subgraph `Eq` `stableQuotientForest … = z.2.1` (only the AMBIENT-FREE fieldwise
correspondence); ZERO PUBLIC `HEq` / `cast` / graph-data transport `▸`.  PERMITTED: `subst` on the INDEPENDENT
destructured `z`-component (Step 2), `subst` on locally-destructured occurrence/structure variables in the
`private` clean occurrence ext + the FOREST owner-alignment (mirror of body-607/621), the `Sigma.ext` library
fiber, Prop-witness transport, Prop-membership `▸`.  NO global `τ` / new permutation / strict star equality; ZERO
old-621 term consume; NO left inverse / `Bijective` / bare `Equiv` / `sum_bij` / alpha / coassoc / orbit quotient
/ dedup.  ZERO new `structure` / `class` / permanent `instance` (one file-local `local instance`; every clean ext
re-derivation is `private`); ZERO forbidden divergence class in any declaration TYPE; ZERO
`sorry` / `admit` / `native_decide`.  Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

open ResolvedFeynmanSubgraph

variable {G : ResolvedFeynmanGraph}

set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-- The concrete φ⁴ divergence measure family, registered file-locally (providable instance, NO forbidden
class). -/
noncomputable local instance instPhi4DivergenceMeasureFamily646 :
    (H : FeynmanGraph) → DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

/-! ## Step 0 — file-local clean helper (admissible ext); occurrence ext + remnant membership reused -/

/-- **body-646 (Step 0, PRIVATE) — a clean element-set extensionality for φ⁴ admissible subgraphs.**  Bypasses
the polluted `ResolvedAdmissibleSubgraph.ext_elements` (which carries a forbidden `[IsAmbientInvariantDivergence]`
section binder): the two non-`elements` fields are `Prop`s, so equal element sets force equality by `cases` +
definitional proof irrelevance.  NO forbidden divergence class in the type.  PRIVATE (mirror of body-644's clean
ext, generalized to an arbitrary ambient `H`). -/
private theorem stableForestBlock_admissible_ext_elements {H : ResolvedFeynmanGraph}
    {A₁ A₂ : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily H}
    (h : @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily H A₁
       = @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily H A₂) : A₁ = A₂ := by
  cases A₁; cases A₂; cases h; rfl

/-! ## Step 0b — quotient-forest membership of a survivor (remnant membership reused from body-639b) -/

/-- **body-646 (Step 0b) — a right survivor lands in the quotient forest.**  Its component `γ` is RIGHT-chosen,
so it is a `stableRightComponents` member; the survivor built from that membership equals `stableRightSurvivor
s.1 hγR` by proof irrelevance of the RIGHT-component witness, landing in the survivor-forest image branch of the
quotient union. -/
theorem stableRightSurvivor_mem_quotientForest {hSt : StableResolvedBoundaryIds G}
    {s : StablePhi4MixedSplitChoice G hSt} {γ : ResolvedFeynmanSubgraph G}
    (hγR : stableIsRightComponent s.1 γ) :
    stableRightSurvivor s.1 hγR ∈ (stableQuotientForest s).elements := by
  rw [stableQuotientForest_elements]
  refine Finset.mem_union_left _ ?_
  rw [stableRightSurvivorForest_elements]
  have hmemRC : γ ∈ stableRightComponents s.1 :=
    (stableMem_rightComponents s.1).mpr ⟨hγR.choose, hγR⟩
  exact Finset.mem_image.mpr ⟨⟨γ, hmemRC⟩, Finset.mem_attach _ _, rfl⟩

/-! ## Step 1 — the FOREST recovered-remnant carrier fields (completion projection + saturation) -/

/-- **body-646 (Step 1, vertices) — the recovered remnant's vertices are `δ`'s** (completion projection). -/
theorem stableRecoveredForward_remnant_vertices (hSt : StableResolvedBoundaryIds G)
    (z : Phi4WTriplePrimeInverseCodomain G) {δ : {x // x ∈ z.2.1.elements}}
    (hδ : phi4WTriplePrime_inv_isForestImage z δ) :
    (stableRemnantComponent (stableRecoveredForwardOccurrence hSt z hδ)).vertices = δ.1.vertices := by
  have h := congrArg ResolvedFeynmanGraph.vertices
    (stableForwardInverse_forest_completion_reconcile hSt z hδ)
  rwa [stableLocalBoundaryCompletedGraph_vertices, stableLocalBoundaryCompletedGraph_vertices] at h

/-- **body-646 (Step 1, internalEdges) — the recovered remnant's internal edges are `δ`'s** (completion
projection). -/
theorem stableRecoveredForward_remnant_internalEdges (hSt : StableResolvedBoundaryIds G)
    (z : Phi4WTriplePrimeInverseCodomain G) {δ : {x // x ∈ z.2.1.elements}}
    (hδ : phi4WTriplePrime_inv_isForestImage z δ) :
    (stableRemnantComponent (stableRecoveredForwardOccurrence hSt z hδ)).internalEdges
      = δ.1.internalEdges := by
  have h := congrArg ResolvedFeynmanGraph.internalEdges
    (stableForwardInverse_forest_completion_reconcile hSt z hδ)
  rwa [stableLocalBoundaryCompletedGraph_internalEdges,
    stableLocalBoundaryCompletedGraph_internalEdges] at h

/-- **body-646 (Step 1, externalLegs) — the recovered remnant's external legs are `δ`'s.**  Both the remnant
(on `stableSelectedOuterContractGraph (recoveredSplit).1`) and `δ.1` (on `z.1.1.contractWithStars …`) are
externally-leg saturated, so each equals the ambient-leg filter over its (shared, body-645b) vertex set; the two
ambients coincide by body-644's outer equality (`stableSelectedOuter_recoveredSplitChoice`).  Ambient-free
Multiset equality — NO cross-ambient subgraph `Eq`.  Mirror of old 621's externalLegs correspondence. -/
theorem stableRecoveredForward_remnant_externalLegs (hSt : StableResolvedBoundaryIds G)
    (z : Phi4WTriplePrimeInverseCodomain G) {δ : {x // x ∈ z.2.1.elements}}
    (hδ : phi4WTriplePrime_inv_isForestImage z δ) :
    (stableRemnantComponent (stableRecoveredForwardOccurrence hSt z hδ)).externalLegs
      = δ.1.externalLegs := by
  have hAmb : stableSelectedOuterContractGraph (stableRecoveredSplitChoice hSt z).1
      = z.1.1.contractWithStars (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1) := by
    show (stableSelectedOuter (stableRecoveredSplitChoice hSt z).1).contractWithStars
        (phi4WTriplePrimeCanonicalSupply.starOf G
          (stableSelectedOuter (stableRecoveredSplitChoice hSt z).1))
      = z.1.1.contractWithStars (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1)
    rw [stableRecoveredSplitChoice_base, stableSelectedOuter_recoveredSplitChoice hSt z]
  have hv := stableRecoveredForward_remnant_vertices hSt z hδ
  have hdsat : ResolvedExternalLegSaturated
      (z.1.1.contractWithStars (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1)) δ.1 :=
    (((mem_phi4WTriplePrimeIndex _ z.2.1).mp z.2.2).2.2.2.2.2.1) δ.1 δ.2
  rw [externalLegs_eq_filter_of_saturated
        (stableRemnantComponent (stableRecoveredForwardOccurrence hSt z hδ))
        (stableRemnant_externalLegSaturated (stableRecoveredForwardOccurrence hSt z hδ)),
      externalLegs_eq_filter_of_saturated δ.1 hdsat, hv]
  exact congrArg
    (fun H => Multiset.filter (fun ℓ => ℓ.attachedTo ∈ δ.1.vertices) H.externalLegs) hAmb

/-! ## Step 2 — the generic Sigma assembly (ambient-aligning `subst`) -/

/-- **body-646 (Step 2) — the forest-block pair assembly from the quotient correspondence.**  GENERIC in an
independent `(s, z)` plus the outer equality `hA : stableSelectedOuter s.1 = z.1.1` and the two-directional
carrier correspondence.  Destructuring `z` turns `z.1.1` into a variable and `subst hA` aligns the quotient
ambient JUDGMENTALLY, so the correspondence lifts to a homogeneous element-set equality (`Finset.ext` +
`ResolvedFeynmanSubgraph.ext`) and the `Sigma.ext` fiber HEq is discharged by `heq_of_eq` — NO hand-written
transport.  STABLE mirror of body-621's `phi4WTriplePrime_forestBlock_assemble`. -/
theorem stableForestBlock_assemble {hSt : StableResolvedBoundaryIds G}
    (s : StablePhi4MixedSplitChoice G hSt) (z : Phi4WTriplePrimeInverseCodomain G)
    (hA : stableSelectedOuter s.1 = z.1.1)
    (hfwd : ∀ c ∈ (stableQuotientForest s).elements,
        ∃ d ∈ z.2.1.elements,
          c.vertices = d.vertices ∧ c.internalEdges = d.internalEdges ∧ c.externalLegs = d.externalLegs)
    (hrev : ∀ d ∈ z.2.1.elements,
        ∃ c ∈ (stableQuotientForest s).elements,
          c.vertices = d.vertices ∧ c.internalEdges = d.internalEdges ∧ c.externalLegs = d.externalLegs) :
    stableForestBlockForward s = z := by
  obtain ⟨⟨A₁, hA₁⟩, ⟨B₁, hB₁⟩⟩ := z
  simp only at hA hfwd hrev
  subst hA
  -- ambient aligned: `stableQuotientForest s` and `B₁` now share the ambient `stableSelectedOuterContractGraph s.1`.
  have hquot : stableQuotientForest s = B₁ := by
    apply stableForestBlock_admissible_ext_elements
    apply Finset.ext
    intro c
    constructor
    · intro hc
      obtain ⟨d, hd, hv, hie, hel⟩ := hfwd c hc
      obtain rfl : c = d := ResolvedFeynmanSubgraph.ext hv hie hel
      exact hd
    · intro hc
      obtain ⟨c', hc', hv, hie, hel⟩ := hrev c hc
      obtain rfl : c' = c := ResolvedFeynmanSubgraph.ext hv hie hel
      exact hc'
  refine Sigma.ext (Subtype.ext rfl) (heq_of_eq (Subtype.ext ?_))
  exact hquot

/-! ## Step 3 — the forward correspondence for the recovered split choice -/

/-- **body-646 (Step 3, forward) — every quotient component of `stableRecoveredSplitChoice hSt z` matches a
`z.2.1` component field-for-field.**  A survivor comes from a star-free `δ` (its right component
`regionComponentOf z δ` recovers `δ.1` verbatim); a remnant comes from a star-touching `δ` (owner determinacy
pins the occurrence to `stableRecoveredForwardOccurrence hSt z hst`, then Step-1 gives the three fields). -/
theorem stableQuotientForest_recoveredSplitChoice_fwd (hSt : StableResolvedBoundaryIds G)
    (z : Phi4WTriplePrimeInverseCodomain G) :
    ∀ c ∈ (stableQuotientForest (stableRecoveredSplitChoice hSt z)).elements,
      ∃ d ∈ z.2.1.elements,
        c.vertices = d.vertices ∧ c.internalEdges = d.internalEdges ∧ c.externalLegs = d.externalLegs := by
  intro c hc
  rcases stableQuotientForest_element_cases (stableRecoveredSplitChoice hSt z) hc
    with ⟨γ, hγR, rfl⟩ | ⟨o, rfl⟩
  · -- survivor of a right component γ
    have hspec : stableRecoveredChoice hSt z ⟨γ, hγR.choose⟩ (Finset.mem_attach _ _) = Sum.inl false :=
      hγR.choose_spec
    have hγmem : γ ∈ (phi4WTriplePrime_recoveredOuter z).elements := hγR.choose
    rcases phi4WTriplePrime_recoveredOuter_component_origin z hγmem with ⟨hγA, hL⟩ | ⟨δ, rfl⟩
    · -- LEFT γ ⇒ choice = Sum.inl true, contradicting the right tag
      exfalso
      have hno : ¬ ∃ d : {x // x ∈ z.2.1.elements},
          phi4WTriplePrime_inv_regionComponentOf z d = γ := by
        rintro ⟨d, hd⟩
        have hdisj := phi4WTriplePrime_inv_left_regionComponent_disjoint z hγA hL d
        rw [hd] at hdisj
        obtain ⟨v, hv⟩ := Finset.card_pos.mp ((phi4WTriplePrime_inv_A_isProperForest z).2.1 γ hγA)
        exact Finset.disjoint_left.mp hdisj hv hv
      have hval : stableRecoveredChoice hSt z ⟨γ, hγR.choose⟩ (Finset.mem_attach _ _) = Sum.inl true := by
        unfold stableRecoveredChoice; rw [dif_neg hno]
      exact absurd (hspec.symm.trans hval) (by simp)
    · -- γ = regionComponentOf z δ
      by_cases hst : phi4WTriplePrime_inv_isForestImage z δ
      · -- star-touching ⇒ choice isRight, contradicting the right tag
        exfalso
        have hval : (stableRecoveredChoice hSt z
            ⟨phi4WTriplePrime_inv_regionComponentOf z δ, hγR.choose⟩ (Finset.mem_attach _ _)).isRight
            = true := by
          unfold stableRecoveredChoice
          have hq : ∃ d, phi4WTriplePrime_inv_regionComponentOf z d
              = phi4WTriplePrime_inv_regionComponentOf z δ := ⟨δ, rfl⟩
          rw [dif_pos hq]
          have hchoose : hq.choose = δ :=
            phi4WTriplePrime_inv_regionComponentOf_injective z hq.choose_spec
          rw [dif_pos (show phi4WTriplePrime_inv_isForestImage z hq.choose by rw [hchoose]; exact hst)]
          rfl
        rw [hspec] at hval
        simp at hval
      · -- star-free ⇒ survivor recovers δ.1 verbatim
        refine ⟨δ.1, δ.2, ?_, ?_, ?_⟩
        · rw [stableRightSurvivor_vertices, phi4WTriplePrime_inv_regionComponentOf_eq_right z hst,
            phi4WTriplePrime_recoveredRight_vertices]
        · rw [stableRightSurvivor_internalEdges,
            phi4WTriplePrime_inv_regionComponentOf_eq_right z hst,
            phi4WTriplePrime_recoveredRight_internalEdges]
        · rw [stableRightSurvivor_externalLegs,
            phi4WTriplePrime_inv_regionComponentOf_eq_right z hst,
            phi4WTriplePrime_recoveredRight_externalLegs]
  · -- remnant of an occurrence o
    have hspec : stableRecoveredChoice hSt z o.γ (Finset.mem_attach _ o.γ) = Sum.inr o.B := o.hchoice
    have hγmem : o.γ.1 ∈ (phi4WTriplePrime_recoveredOuter z).elements := o.γ.2
    rcases phi4WTriplePrime_recoveredOuter_component_origin z hγmem with ⟨hγA, hL⟩ | ⟨δ, hδeq⟩
    · -- LEFT owner ⇒ choice = Sum.inl true, contradicting the forest tag
      exfalso
      have hno : ¬ ∃ d : {x // x ∈ z.2.1.elements},
          phi4WTriplePrime_inv_regionComponentOf z d = o.γ.1 := by
        rintro ⟨d, hd⟩
        have hdisj := phi4WTriplePrime_inv_left_regionComponent_disjoint z hγA hL d
        rw [hd] at hdisj
        obtain ⟨v, hv⟩ := Finset.card_pos.mp ((phi4WTriplePrime_inv_A_isProperForest z).2.1 o.γ.1 hγA)
        exact Finset.disjoint_left.mp hdisj hv hv
      have hval : stableRecoveredChoice hSt z o.γ (Finset.mem_attach _ o.γ) = Sum.inl true := by
        unfold stableRecoveredChoice; rw [dif_neg hno]
      exact absurd (hspec.symm.trans hval) (by simp)
    · by_cases hst : phi4WTriplePrime_inv_isForestImage z δ
      · -- star-touching ⇒ o is the canonical forward occurrence at δ
        have howner : o.γ.1 = (stableRecoveredForwardOccurrence hSt z hst).γ.1 := by
          rw [← hδeq, phi4WTriplePrime_inv_regionComponentOf_eq_parent z hst]
          rfl
        have hoeq : o = stableRecoveredForwardOccurrence hSt z hst :=
          stableForestOccurrence_ext_helper (stableRecoveredSplitChoice hSt z) o
            (stableRecoveredForwardOccurrence hSt z hst) howner
        subst hoeq
        exact ⟨δ.1, δ.2, stableRecoveredForward_remnant_vertices hSt z hst,
          stableRecoveredForward_remnant_internalEdges hSt z hst,
          stableRecoveredForward_remnant_externalLegs hSt z hst⟩
      · -- star-free owner ⇒ choice = Sum.inl false, contradicting the forest tag
        exfalso
        have hval : stableRecoveredChoice hSt z o.γ (Finset.mem_attach _ o.γ) = Sum.inl false := by
          unfold stableRecoveredChoice
          have hq : ∃ d, phi4WTriplePrime_inv_regionComponentOf z d = o.γ.1 := ⟨δ, hδeq⟩
          rw [dif_pos hq]
          have hchoose : hq.choose = δ :=
            phi4WTriplePrime_inv_regionComponentOf_injective z (hq.choose_spec.trans hδeq.symm)
          rw [dif_neg (show ¬ phi4WTriplePrime_inv_isForestImage z hq.choose by rw [hchoose]; exact hst)]
        rw [hspec] at hval
        simp at hval

/-! ## Step 4 — the reverse correspondence for the recovered split choice -/

/-- **body-646 (Step 4, reverse) — every `z.2.1` component matches a quotient component of
`stableRecoveredSplitChoice hSt z` field-for-field.**  A star-free `δ` maps to its right survivor; a
star-touching `δ` maps to the remnant of `stableRecoveredForwardOccurrence hSt z hst`. -/
theorem stableQuotientForest_recoveredSplitChoice_rev (hSt : StableResolvedBoundaryIds G)
    (z : Phi4WTriplePrimeInverseCodomain G) :
    ∀ d ∈ z.2.1.elements,
      ∃ c ∈ (stableQuotientForest (stableRecoveredSplitChoice hSt z)).elements,
        c.vertices = d.vertices ∧ c.internalEdges = d.internalEdges ∧ c.externalLegs = d.externalLegs := by
  intro d hd
  set δ : {x // x ∈ z.2.1.elements} := ⟨d, hd⟩ with hδ
  by_cases hst : phi4WTriplePrime_inv_isForestImage z δ
  · -- FOREST: the remnant of the canonical forward occurrence
    refine ⟨stableRemnantComponent (stableRecoveredForwardOccurrence hSt z hst),
      stableRemnantComponent_mem_quotientForest (stableRecoveredSplitChoice hSt z) _,
      stableRecoveredForward_remnant_vertices hSt z hst,
      stableRecoveredForward_remnant_internalEdges hSt z hst,
      stableRecoveredForward_remnant_externalLegs hSt z hst⟩
  · -- RIGHT: the survivor of the right component regionComponentOf z δ
    have hγR : stableIsRightComponent (stableRecoveredSplitChoice hSt z).1
        (phi4WTriplePrime_inv_regionComponentOf z δ) :=
      ⟨phi4WTriplePrime_inv_regionComponent_mem_recoveredOuter z δ,
        stableRecoveredChoice_right hSt z hst (Finset.mem_attach _ _)⟩
    refine ⟨stableRightSurvivor (stableRecoveredSplitChoice hSt z).1 hγR,
      stableRightSurvivor_mem_quotientForest hγR, ?_, ?_, ?_⟩
    · rw [stableRightSurvivor_vertices, phi4WTriplePrime_inv_regionComponentOf_eq_right z hst,
        phi4WTriplePrime_recoveredRight_vertices]
    · rw [stableRightSurvivor_internalEdges,
        phi4WTriplePrime_inv_regionComponentOf_eq_right z hst,
        phi4WTriplePrime_recoveredRight_internalEdges]
    · rw [stableRightSurvivor_externalLegs,
        phi4WTriplePrime_inv_regionComponentOf_eq_right z hst,
        phi4WTriplePrime_recoveredRight_externalLegs]

/-! ## Step 5 — the quotient correspondence -/

/-- **body-646 (Step 5, HEADLINE correspondence) — the quotient forest of `stableRecoveredSplitChoice hSt z`
reconstructs `z.2.1` componentwise.**  The two-directional carrier correspondence (survivor ↔ star-free, remnant
↔ star-touching); this is the well-typed (AMBIENT-FREE) form of `quotientForest = z.2.1`, packaged for the
`Sigma.ext` fiber (a public cross-ambient raw subgraph equality / `HEq` is FORBIDDEN). -/
theorem stableQuotientForest_recoveredSplitChoice (hSt : StableResolvedBoundaryIds G)
    (z : Phi4WTriplePrimeInverseCodomain G) :
    (∀ c ∈ (stableQuotientForest (stableRecoveredSplitChoice hSt z)).elements,
        ∃ d ∈ z.2.1.elements,
          c.vertices = d.vertices ∧ c.internalEdges = d.internalEdges ∧ c.externalLegs = d.externalLegs)
      ∧ (∀ d ∈ z.2.1.elements,
        ∃ c ∈ (stableQuotientForest (stableRecoveredSplitChoice hSt z)).elements,
          c.vertices = d.vertices ∧ c.internalEdges = d.internalEdges ∧ c.externalLegs = d.externalLegs) :=
  ⟨stableQuotientForest_recoveredSplitChoice_fwd hSt z,
    stableQuotientForest_recoveredSplitChoice_rev hSt z⟩

/-! ## Step 6 — the headline right inverse -/

/-- **body-646 (Step 6, HEADLINE) — `forward ∘ inverse = id`.**  The stable forest-block forward map applied to
the source-independent recovered split choice returns `z`, bundling the outer equality (body-644) and the
quotient correspondence (Step 5) through `Sigma.ext` once (ambient aligned by the `subst` inside
`stableForestBlock_assemble`).  A genuine FULL Sigma RIGHT inverse; NO public cross-ambient / `HEq`; NO
hand-written transport. -/
theorem stableForestBlockForward_recoveredSplitChoice (hSt : StableResolvedBoundaryIds G)
    (z : Phi4WTriplePrimeInverseCodomain G) :
    stableForestBlockForward (stableRecoveredSplitChoice hSt z) = z :=
  stableForestBlock_assemble (stableRecoveredSplitChoice hSt z) z
    (stableSelectedOuter_recoveredSplitChoice hSt z)
    (stableQuotientForest_recoveredSplitChoice_fwd hSt z)
    (stableQuotientForest_recoveredSplitChoice_rev hSt z)

end GaugeGeometry.QFT.Combinatorial
