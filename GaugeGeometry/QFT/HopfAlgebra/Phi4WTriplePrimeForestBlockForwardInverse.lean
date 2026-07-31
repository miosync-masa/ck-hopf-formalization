import GaugeGeometry.QFT.HopfAlgebra.Phi4WTriplePrimeForestOccurrenceReconciliation

/-!
# QFT-R1-body-621 — the forest-block RIGHT inverse `forward ∘ inverse = id`

body-620 stopped at the ILL-TYPED cross-ambient raw subgraph equality `remnantComponent o = δ.1`
(LHS over `selectedOuterContractGraph s`, RHS over `z.1.1.contractWithStars …`) and delivered instead the
AMBIENT-FREE bcrg reconciliation `(remnantComponent (recoveredForwardOccurrence z hδ)).bcrg = δ.1.bcrg`.

This body proves the RIGHT inverse of the EXISTING forward map
`phi4WTriplePrime_forestBlockForward (phi4WTriplePrime_recoveredSplitChoice z) = z` (no separate corrected
forward map is built — body-604's `remnantTau` already carries the forward-side correction).

## The Sigma-fiber alignment mechanism (Step 2)

The headline is bundled through `Sigma.ext` ONCE, but the ambient alignment is deferred to a lemma
`phi4WTriplePrime_forestBlock_assemble` that is GENERIC in a split choice `s` and an ARBITRARY codomain `z`
(independent variables) plus the outer equality `hA : selectedOuter s = z.1.1`.  Because `s` and `z` are
independent there, `obtain ⟨⟨A₁, _⟩, _⟩ := z` makes `z.1.1 = A₁` a genuine local variable and `subst hA`
eliminates it (NO circularity — the recovered `s` is only substituted at the headline call site), making the
quotient ambient JUDGMENTALLY aligned.  The `Sigma.ext` fiber HEq is then discharged by `heq_of_eq` on the
now-homogeneous `Eq` (NO hand-written `cast` / `Eq.ndrec` / graph-data `▸`).

## Steps
* **Step 3 (RIGHT)** — a star-free `δ` recovers as a right component `regionComponentOf z δ`; its survivor's
  three carrier fields are `δ.1`'s by the body-608 recovered-right anchors (all `rfl`) + body-603 survivor
  anchors.
* **Step 4 (FOREST)** — for a star-touching `δ`, the canonical `o := recoveredForwardOccurrence z hδ`; the
  remnant's vertices / internal edges are `δ.1`'s by field projection of body-620's bcrg headline, and its
  external legs are `δ.1`'s by W‴ external-leg saturation of BOTH sides (over the identified ambient).  The
  local `remnantComponent o = δ.1` never appears as a public cross-ambient theorem.
* **Step 5** — the two-directional quotient correspondence
  `phi4WTriplePrime_quotientForest_recoveredSplitChoice`: every quotient component of `s` matches a `z.2.1`
  component field-for-field and vice versa (survivor ↔ star-free, remnant ↔ star-touching), classified by the
  star classifier.  Every `Finset.image` inside the consumed collections already carries its injectivity.
* **Step 6 (HEADLINE)** — `phi4WTriplePrime_forestBlockForward_recoveredSplitChoice`.

## HALT compliance
Axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only); ZERO forbidden divergence classes in any
declaration type.  NO public cross-ambient raw-subgraph equality / public `HEq`; NO hand-written `cast` /
`Eq.ndrec` / graph-data `▸`; NO new permutation / global `τ`; NO orbit quotient / dedup; NO
`forestBlockForwardCorrected`.  HALT (not entered): inverse-after-forward (622); whole `Equiv` (623);
summand / `sum_bij` / alpha / coassoc.  No `sorry` / `admit` / `native_decide`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

open ResolvedFeynmanSubgraph

variable {G : ResolvedFeynmanGraph}

set_option maxHeartbeats 3200000

/-- The concrete φ⁴ divergence measure family, registered file-locally (providable instance, NO forbidden
class). -/
noncomputable local instance phi4Inst621 : (H : FeynmanGraph) → DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

/-! ## Step 4 — the FOREST recovered-remnant carrier fields (bcrg projection + saturation) -/

/-- **body-621 (Step 4, vertices) — the recovered remnant's vertices are `δ`'s** (bcrg projection). -/
theorem phi4WTriplePrime_recoveredForward_remnant_vertices
    (z : Phi4WTriplePrimeInverseCodomain G) {δ : {x // x ∈ z.2.1.elements}}
    (hst : phi4WTriplePrime_inv_isForestImage z δ) :
    (phi4WTriplePrime_remnantComponent (phi4WTriplePrime_recoveredForwardOccurrence z hst)).vertices
      = δ.1.vertices := by
  have h := congrArg ResolvedFeynmanGraph.vertices
    (phi4WTriplePrime_forwardInverse_forest_bcrg_reconcile z hst)
  rwa [ResolvedFeynmanSubgraph.boundaryCompletedResolvedGraph_vertices,
    ResolvedFeynmanSubgraph.boundaryCompletedResolvedGraph_vertices] at h

/-- **body-621 (Step 4, internalEdges) — the recovered remnant's internal edges are `δ`'s** (bcrg
projection). -/
theorem phi4WTriplePrime_recoveredForward_remnant_internalEdges
    (z : Phi4WTriplePrimeInverseCodomain G) {δ : {x // x ∈ z.2.1.elements}}
    (hst : phi4WTriplePrime_inv_isForestImage z δ) :
    (phi4WTriplePrime_remnantComponent (phi4WTriplePrime_recoveredForwardOccurrence z hst)).internalEdges
      = δ.1.internalEdges := by
  have h := congrArg ResolvedFeynmanGraph.internalEdges
    (phi4WTriplePrime_forwardInverse_forest_bcrg_reconcile z hst)
  rwa [ResolvedFeynmanSubgraph.boundaryCompletedResolvedGraph_internalEdges,
    ResolvedFeynmanSubgraph.boundaryCompletedResolvedGraph_internalEdges] at h

/-- **body-621 (Step 4, externalLegs) — the recovered remnant's external legs are `δ`'s.**  Both the remnant
(on `selectedOuterContractGraph (recoveredSplitChoice z)`) and `δ.1` (on `z.1.1.contractWithStars …`) are
externally-leg saturated, so each equals the ambient-leg filter over its (shared) vertex set; the two ambients
have equal external legs by the outer equality (`selectedOuter_recoveredSplitChoice`). -/
theorem phi4WTriplePrime_recoveredForward_remnant_externalLegs
    (z : Phi4WTriplePrimeInverseCodomain G) {δ : {x // x ∈ z.2.1.elements}}
    (hst : phi4WTriplePrime_inv_isForestImage z δ) :
    (phi4WTriplePrime_remnantComponent (phi4WTriplePrime_recoveredForwardOccurrence z hst)).externalLegs
      = δ.1.externalLegs := by
  have hAmb : phi4WTriplePrime_selectedOuterContractGraph (phi4WTriplePrime_recoveredSplitChoice z)
      = z.1.1.contractWithStars (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1) :=
    congrArg (fun A => A.contractWithStars (phi4WTriplePrimeCanonicalSupply.starOf G A))
      (phi4WTriplePrime_selectedOuter_recoveredSplitChoice z)
  have hv := phi4WTriplePrime_recoveredForward_remnant_vertices z hst
  have hdsat : ResolvedExternalLegSaturated
      (z.1.1.contractWithStars (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1)) δ.1 :=
    (((mem_phi4WTriplePrimeIndex _ z.2.1).mp z.2.2).2.2.2.2.2.1) δ.1 δ.2
  rw [externalLegs_eq_filter_of_saturated
        (phi4WTriplePrime_remnantComponent (phi4WTriplePrime_recoveredForwardOccurrence z hst))
        (phi4WTriplePrime_remnant_saturated _),
      externalLegs_eq_filter_of_saturated δ.1 hdsat]
  simp only [hv]
  rw [hAmb]

/-! ## Step 6 helper — the generic Sigma assembly (ambient-aligning `subst`) -/

/-- **body-621 (Step 6 helper) — the forest-block pair assembly from the quotient correspondence.**  GENERIC in
an independent `(s, z)` plus the outer equality `hA : selectedOuter s = z.1.1` and the two-directional carrier
correspondence between the quotient components of `s` and the components of `z.2.1`.  Destructuring `z` turns
`z.1.1` into a variable and `subst hA` aligns the quotient ambient JUDGMENTALLY, so the correspondence lifts to
a homogeneous element-set equality (`Finset.ext` + `ResolvedFeynmanSubgraph.ext`) and the `Sigma.ext` fiber HEq
is discharged by `heq_of_eq` — NO hand-written transport. -/
theorem phi4WTriplePrime_forestBlock_assemble
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) (z : Phi4WTriplePrimeInverseCodomain G)
    (hA : phi4WTriplePrime_selectedOuter s = z.1.1)
    (hfwd : ∀ c ∈ (phi4WTriplePrime_quotientForest s).elements,
        ∃ d ∈ z.2.1.elements,
          c.vertices = d.vertices ∧ c.internalEdges = d.internalEdges ∧ c.externalLegs = d.externalLegs)
    (hrev : ∀ d ∈ z.2.1.elements,
        ∃ c ∈ (phi4WTriplePrime_quotientForest s).elements,
          c.vertices = d.vertices ∧ c.internalEdges = d.internalEdges ∧ c.externalLegs = d.externalLegs) :
    phi4WTriplePrime_forestBlockForward s = z := by
  obtain ⟨⟨A₁, hA₁⟩, ⟨B₁, hB₁⟩⟩ := z
  simp only at hA hfwd hrev
  subst hA
  -- ambient aligned: `quotientForest s` and `B₁` now share the ambient `selectedOuterContractGraph s`.
  have hquot : phi4WTriplePrime_quotientForest s = B₁ := by
    apply phi4WTriplePrime_admissible_ext_elements
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

/-! ## Step 5 — the quotient correspondence for the recovered split choice -/

/-- **body-621 (Step 5, forward) — every quotient component of `recoveredSplitChoice z` matches a `z.2.1`
component field-for-field.**  A survivor comes from a star-free `δ` (its right component `regionComponentOf z δ`
recovers `δ.1` verbatim); a remnant comes from a star-touching `δ` (owner determinacy pins the occurrence to
`recoveredForwardOccurrence z hst`, then Step-4 gives the three fields). -/
theorem phi4WTriplePrime_quotientForest_recoveredSplitChoice_fwd
    (z : Phi4WTriplePrimeInverseCodomain G) :
    ∀ c ∈ (phi4WTriplePrime_quotientForest (phi4WTriplePrime_recoveredSplitChoice z)).elements,
      ∃ d ∈ z.2.1.elements,
        c.vertices = d.vertices ∧ c.internalEdges = d.internalEdges ∧ c.externalLegs = d.externalLegs := by
  intro c hc
  rcases phi4WTriplePrime_quotientForest_element_cases (phi4WTriplePrime_recoveredSplitChoice z) hc
    with ⟨γ, hγR, rfl⟩ | ⟨o, rfl⟩
  · -- survivor of a right component γ
    have hspec : phi4WTriplePrime_recoveredChoice z ⟨γ, hγR.choose⟩ (Finset.mem_attach _ _)
        = Sum.inl false := hγR.choose_spec
    have hγmem : γ ∈ (phi4WTriplePrime_recoveredOuter z).elements := hγR.choose
    rcases phi4WTriplePrime_recoveredOuter_component_origin z hγmem with ⟨hγA, hL⟩ | ⟨δ, rfl⟩
    · -- LEFT γ ⇒ choice = Sum.inl true (no region witness), contradicting the right tag
      exfalso
      have hno : ¬ ∃ d : {x // x ∈ z.2.1.elements}, phi4WTriplePrime_inv_regionComponentOf z d = γ := by
        rintro ⟨d, hd⟩
        have hdisj := phi4WTriplePrime_inv_left_regionComponent_disjoint z hγA hL d
        rw [hd] at hdisj
        obtain ⟨v, hv⟩ := Finset.card_pos.mp ((phi4WTriplePrime_inv_A_isProperForest z).2.1 γ hγA)
        exact Finset.disjoint_left.mp hdisj hv hv
      have hval : phi4WTriplePrime_recoveredChoice z ⟨γ, hγR.choose⟩ (Finset.mem_attach _ _)
          = Sum.inl true := by
        unfold phi4WTriplePrime_recoveredChoice; rw [dif_neg hno]
      exact absurd (hspec.symm.trans hval) (by simp)
    · -- γ = regionComponentOf z δ
      by_cases hst : phi4WTriplePrime_inv_isForestImage z δ
      · -- star-touching ⇒ choice isRight, contradicting the right tag
        exfalso
        have hval : (phi4WTriplePrime_recoveredChoice z
            ⟨phi4WTriplePrime_inv_regionComponentOf z δ, hγR.choose⟩ (Finset.mem_attach _ _)).isRight
            = true := by
          unfold phi4WTriplePrime_recoveredChoice
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
        · rw [phi4WTriplePrime_survivor_vertices, phi4WTriplePrime_inv_regionComponentOf_eq_right z hst,
            phi4WTriplePrime_recoveredRight_vertices]
        · rw [phi4WTriplePrime_survivor_internalEdges,
            phi4WTriplePrime_inv_regionComponentOf_eq_right z hst,
            phi4WTriplePrime_recoveredRight_internalEdges]
        · rw [phi4WTriplePrime_survivor_externalLegs,
            phi4WTriplePrime_inv_regionComponentOf_eq_right z hst,
            phi4WTriplePrime_recoveredRight_externalLegs]
  · -- remnant of an occurrence o
    have hspec : phi4WTriplePrime_recoveredChoice z o.γ (Finset.mem_attach _ o.γ)
        = Sum.inr o.B := o.hchoice
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
      have hval : phi4WTriplePrime_recoveredChoice z o.γ (Finset.mem_attach _ o.γ)
          = Sum.inl true := by
        unfold phi4WTriplePrime_recoveredChoice; rw [dif_neg hno]
      exact absurd (hspec.symm.trans hval) (by simp)
    · by_cases hst : phi4WTriplePrime_inv_isForestImage z δ
      · -- star-touching ⇒ o is the canonical forward occurrence at δ
        have howner : o.γ.1 = (phi4WTriplePrime_recoveredForwardOccurrence z hst).γ.1 := by
          rw [← hδeq, phi4WTriplePrime_inv_regionComponentOf_eq_parent z hst]
          rfl
        have hoeq : o = phi4WTriplePrime_recoveredForwardOccurrence z hst :=
          phi4WTriplePrime_occurrence_ext howner
        subst hoeq
        exact ⟨δ.1, δ.2, phi4WTriplePrime_recoveredForward_remnant_vertices z hst,
          phi4WTriplePrime_recoveredForward_remnant_internalEdges z hst,
          phi4WTriplePrime_recoveredForward_remnant_externalLegs z hst⟩
      · -- star-free owner ⇒ choice = Sum.inl false, contradicting the forest tag
        exfalso
        have hval : phi4WTriplePrime_recoveredChoice z o.γ (Finset.mem_attach _ o.γ)
            = Sum.inl false := by
          unfold phi4WTriplePrime_recoveredChoice
          have hq : ∃ d, phi4WTriplePrime_inv_regionComponentOf z d = o.γ.1 := ⟨δ, hδeq⟩
          rw [dif_pos hq]
          have hchoose : hq.choose = δ :=
            phi4WTriplePrime_inv_regionComponentOf_injective z (hq.choose_spec.trans hδeq.symm)
          rw [dif_neg (show ¬ phi4WTriplePrime_inv_isForestImage z hq.choose by rw [hchoose]; exact hst)]
        rw [hspec] at hval
        simp at hval

/-- **body-621 (Step 5, reverse) — every `z.2.1` component matches a quotient component of
`recoveredSplitChoice z` field-for-field.**  A star-free `δ` maps to its right survivor; a star-touching `δ`
maps to the remnant of `recoveredForwardOccurrence z hst`. -/
theorem phi4WTriplePrime_quotientForest_recoveredSplitChoice_rev
    (z : Phi4WTriplePrimeInverseCodomain G) :
    ∀ d ∈ z.2.1.elements,
      ∃ c ∈ (phi4WTriplePrime_quotientForest (phi4WTriplePrime_recoveredSplitChoice z)).elements,
        c.vertices = d.vertices ∧ c.internalEdges = d.internalEdges ∧ c.externalLegs = d.externalLegs := by
  intro d hd
  set δ : {x // x ∈ z.2.1.elements} := ⟨d, hd⟩ with hδ
  by_cases hst : phi4WTriplePrime_inv_isForestImage z δ
  · -- FOREST: the remnant of the canonical forward occurrence
    refine ⟨phi4WTriplePrime_remnantComponent (phi4WTriplePrime_recoveredForwardOccurrence z hst),
      phi4WTriplePrime_remnantComponent_mem_quotientForest _,
      phi4WTriplePrime_recoveredForward_remnant_vertices z hst,
      phi4WTriplePrime_recoveredForward_remnant_internalEdges z hst,
      phi4WTriplePrime_recoveredForward_remnant_externalLegs z hst⟩
  · -- RIGHT: the survivor of the right component regionComponentOf z δ
    have hγR : phi4WTriplePrime_isRightComponent (phi4WTriplePrime_recoveredSplitChoice z)
        (phi4WTriplePrime_inv_regionComponentOf z δ) :=
      ⟨phi4WTriplePrime_inv_regionComponent_mem_recoveredOuter z δ,
        phi4WTriplePrime_recoveredChoice_right z hst (Finset.mem_attach _ _)⟩
    refine ⟨phi4WTriplePrime_survivor (phi4WTriplePrime_recoveredSplitChoice z) hγR,
      phi4WTriplePrime_survivor_mem_quotientForest _ hγR, ?_, ?_, ?_⟩
    · rw [phi4WTriplePrime_survivor_vertices, phi4WTriplePrime_inv_regionComponentOf_eq_right z hst,
        phi4WTriplePrime_recoveredRight_vertices]
    · rw [phi4WTriplePrime_survivor_internalEdges,
        phi4WTriplePrime_inv_regionComponentOf_eq_right z hst,
        phi4WTriplePrime_recoveredRight_internalEdges]
    · rw [phi4WTriplePrime_survivor_externalLegs,
        phi4WTriplePrime_inv_regionComponentOf_eq_right z hst,
        phi4WTriplePrime_recoveredRight_externalLegs]

/-- **body-621 (Step 5, HEADLINE correspondence) — the quotient forest of `recoveredSplitChoice z`
reconstructs `z.2.1` componentwise.**  The two-directional carrier correspondence (survivor ↔ star-free,
remnant ↔ star-touching); this is the well-typed (ambient-free) form of `quotientForest s = z.2.1`, packaged
for the `Sigma.ext` fiber (a public cross-ambient raw subgraph equality / `HEq` is FORBIDDEN). -/
theorem phi4WTriplePrime_quotientForest_recoveredSplitChoice
    (z : Phi4WTriplePrimeInverseCodomain G) :
    (∀ c ∈ (phi4WTriplePrime_quotientForest (phi4WTriplePrime_recoveredSplitChoice z)).elements,
        ∃ d ∈ z.2.1.elements,
          c.vertices = d.vertices ∧ c.internalEdges = d.internalEdges ∧ c.externalLegs = d.externalLegs)
      ∧ (∀ d ∈ z.2.1.elements,
        ∃ c ∈ (phi4WTriplePrime_quotientForest (phi4WTriplePrime_recoveredSplitChoice z)).elements,
          c.vertices = d.vertices ∧ c.internalEdges = d.internalEdges ∧ c.externalLegs = d.externalLegs) :=
  ⟨phi4WTriplePrime_quotientForest_recoveredSplitChoice_fwd z,
    phi4WTriplePrime_quotientForest_recoveredSplitChoice_rev z⟩

/-! ## Step 6 — the headline right inverse -/

/-- **body-621 (Step 6, HEADLINE) — `forward ∘ inverse = id`.**  The EXISTING forest-block forward map applied
to the source-independent recovered split choice returns `z`, bundling the outer equality (body-620) and the
quotient correspondence (Step 5) through `Sigma.ext` once (ambient aligned by the `subst` inside
`phi4WTriplePrime_forestBlock_assemble`).  NO corrected forward map; NO public cross-ambient / `HEq`; NO
hand-written transport. -/
theorem phi4WTriplePrime_forestBlockForward_recoveredSplitChoice
    (z : Phi4WTriplePrimeInverseCodomain G) :
    phi4WTriplePrime_forestBlockForward (phi4WTriplePrime_recoveredSplitChoice z) = z :=
  phi4WTriplePrime_forestBlock_assemble (phi4WTriplePrime_recoveredSplitChoice z) z
    (phi4WTriplePrime_selectedOuter_recoveredSplitChoice z)
    (phi4WTriplePrime_quotientForest_recoveredSplitChoice_fwd z)
    (phi4WTriplePrime_quotientForest_recoveredSplitChoice_rev z)

end GaugeGeometry.QFT.Combinatorial
