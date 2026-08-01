import GaugeGeometry.QFT.HopfAlgebra.Phi4StableRecoveredSplitChoice

/-!
# QFT-R1-body-644 — stable forward-after-inverse OUTER recovery (FOREST payload + outer equality only)

Body-643 assembled the whole INVERSE FUNCTION owner `stableRecoveredSplitChoice hSt z :
StablePhi4MixedSplitChoice G hSt`, deferring the EXACT explicit-witness FOREST (`Sum.inr`) value across the
`Exists.choose`-selected `δ` (the body-614 forward-image scope guard).  This body closes the RIGHT-inverse's
FIRST coordinate: it (1) discharges that deferred FOREST value as a HOMOGENEOUS equation (owner FIXED to the
recovered parent from the start), and (2) proves that the stable forward map's outer forest reconstructs
`z.1.1` EXACTLY (a raw `ResolvedAdmissibleSubgraph` equality).  It is the STABLE mirror of the old body-620
`phi4WTriplePrime_selectedOuter_recoveredSplitChoice` proof shape — the OLD choice / tag / split-choice /
inner forest are NEVER consumed as terms, only their proof shape mirrored on body-632/635/642/643's STABLE
carrier.

## Steps
* **Step 1** — `stableRecoveredForestTag_heq` (PRIVATE, transport collapse).  When the `Exists.choose`-selected
  `δ'` and a fixed `δ` yield the SAME recovered parent (`hq.choose = δ` by
  `regionComponentOf_injective`), body-643's `stableRecoveredForestTag` transport (the `heq ▸`) collapses to
  IDENTITY: `HEq (tag) (stableInvRecoveredInnerForestValue hSt (fd z hδ))`.  The `▸` becomes an
  `eqRec`-`HEq` (`heq_of_eqRec`), and the two `ForestDecontractionInput`s agree by definitional proof
  irrelevance after `subst hcs` (`stableInvRecoveredInnerForestValue_hcongr`).  The ONLY `HEq` in the file
  lives inside these PRIVATE helpers.
* **Step 2** — `stableRecoveredChoice_forest_value` (HOMOGENEOUS).  The deferred FOREST value, with owner FIXED
  to `recoveredParent (fd z hδ)` from the START (so the statement is homogeneous in
  `StableLocalForestIdx (recoveredParent (fd z hδ))`).  `dif_pos hq`, `dif_pos hst'`, then Step-1's collapse.
* **Step 3** — `stableRecoveredForwardOccurrence`: a `⟨…⟩` into the EXISTING body-635
  `StableForestChoiceOccurrence (stableRecoveredSplitChoice hSt z)` (NO new structure), with `hchoice` = Step 2.
* **Step 4** — `stablePromotedElemsAt_recoveredForestOwner`: the promoted set at a recovered forest owner is the
  touched outer forest's element set (Step 2 picks the `.image` branch, then body-642's
  `rootRelative_image` VERBATIM).
* **Step 5** — `stableSelectedOuter_recoveredSplitChoice` (HEADLINE): the raw outer equality
  `stableSelectedOuter (stableRecoveredResolvedSplitChoice hSt z) = z.1.1`.  Clean file-local proof-irrelevance
  ext → `stableSelectedOuter_elements` → `ext c` → `Finset.mem_union`; forward (LEFT via `component_origin`;
  PROMOTED via Step 4) + reverse (LEFT / non-LEFT star-touching via Step 4).

## Ownership boundary — MUST NOT consume as terms
The OLD `phi4WTriplePrime_recoveredChoice` / `recoveredForestTag` / `recoveredSplitChoice` /
`phi4WTriplePrime_inv_recoveredInnerForest`, and the OLD forest-block `Equiv` (623).  Only body-643's STABLE
choice / tag / split-choice, body-642's STABLE inner forest payload, body-632's stable selectedOuter algebra,
body-635's `StableForestChoiceOccurrence`, and the completion-INDEPENDENT scaffolding (`recoveredOuter` /
`regionComponentOf` / `recoveredParent` / `isForestImage` / `touchedOuterForest` / the outer-membership BANK)
are reused.

## HALT / red lines
The SECOND (quotient-forest) coordinate is NOT compared with `z.2.1`; NO remnant recontraction / bcrg
reconciliation; `stableForestBlockForward (stableRecoveredSplitChoice hSt z) = z` is NOT asserted;
inverse-after-forward is NOT entered; `StablePhi4ForestBlockForwardBijective` is NOT proved.  NO round-trip /
Equiv / `Finset.sum_bij` / alpha / coassoc / `Bijective`.  ZERO consume of the OLD choice / tag / split-choice
/ inner forest / 623 Equiv.  ZERO new `structure` / `class` / permanent `instance` (one file-local
`local instance`; the occurrence is a `⟨…⟩` into the EXISTING `StableForestChoiceOccurrence`).  ZERO PUBLIC
`HEq` / `cast` / transport API — the ONLY `HEq` lives in PRIVATE `heq_of_eqRec` /
`stableInvRecoveredInnerForestValue_hcongr` / `stableRecoveredForestTag_heq`; all other `▸` are same-ambient-`G`
owner alignment or Prop-membership rewrites.  Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

open ResolvedFeynmanSubgraph

variable {G : ResolvedFeynmanGraph}

set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-- The concrete φ⁴ divergence measure family, registered file-locally (providable instance, NO forbidden
class). -/
noncomputable local instance instPhi4DivergenceMeasureFamily644 :
    (H : FeynmanGraph) → DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

/-! ## Step 1 — the transport collapse (PRIVATE, the only `HEq` in the file) -/

/-- **body-644 (Step 1, PRIVATE) — an `eqRec`-transport along a `G`-native owner equality is `HEq` to its
argument.**  Generic `Eq.rec`/`▸` collapse for the fibre `StableLocalForestIdx`, over the SAME ambient `G`.
NO `cast`; PRIVATE (transport-bearing). -/
private theorem heq_of_eqRec {a b : ResolvedFeynmanSubgraph G}
    (h : a = b) (x : StableLocalForestIdx a) : HEq (h ▸ x) x := by
  cases h; rfl

/-- **body-644 (Step 1, PRIVATE) — the stable inner-forest payload is `HEq`-invariant under a `δ`-owner
equality.**  For two decontraction inputs over `δ = δ'`, their body-642 payloads agree up to `HEq` — after
`subst`, the two `phi4WTriplePrime_ForestDecontractionInput`s (a `Prop`) coincide by definitional proof
irrelevance, so the payloads are definitionally equal.  PRIVATE (transport-bearing). -/
private theorem stableInvRecoveredInnerForestValue_hcongr (hSt : StableResolvedBoundaryIds G)
    (z : Phi4WTriplePrimeInverseCodomain G) {δ δ' : {x // x ∈ z.2.1.elements}} (hdd : δ = δ')
    (I : phi4WTriplePrime_ForestDecontractionInput z δ)
    (I' : phi4WTriplePrime_ForestDecontractionInput z δ') :
    HEq (stableInvRecoveredInnerForestValue hSt I) (stableInvRecoveredInnerForestValue hSt I') := by
  subst hdd
  rfl

/-- **body-644 (Step 1, PRIVATE) — the transport collapse.**  When the `Exists.choose`-selected witness of `hq`
recovers the SAME `δ` (`hcs : hq.choose = δ`), body-643's transported FOREST tag is `HEq` to body-642's stable
payload over `δ`: the internal `heq ▸` becomes `heq_of_eqRec` (collapse to the untransported payload over
`hq.choose`), and the payloads over `hq.choose` / `δ` agree by `stableInvRecoveredInnerForestValue_hcongr`.
PRIVATE (transport-bearing); NO cross-ambient `HEq` — both fibres live over the SAME ambient `G`. -/
private theorem stableRecoveredForestTag_heq (hSt : StableResolvedBoundaryIds G)
    (z : Phi4WTriplePrimeInverseCodomain G)
    (γ : {x // x ∈ (phi4WTriplePrime_recoveredOuter z).elements})
    (hq : ∃ δ : {x // x ∈ z.2.1.elements}, phi4WTriplePrime_inv_regionComponentOf z δ = γ.1)
    (hst : phi4WTriplePrime_inv_isForestImage z hq.choose)
    {δ : {x // x ∈ z.2.1.elements}} (hδ : phi4WTriplePrime_inv_isForestImage z δ)
    (hcs : hq.choose = δ) :
    HEq (stableRecoveredForestTag hSt z γ hq hst)
        (stableInvRecoveredInnerForestValue hSt
          (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδ)) :=
  HEq.trans
    (heq_of_eqRec _ (stableInvRecoveredInnerForestValue hSt
      (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hst)))
    (stableInvRecoveredInnerForestValue_hcongr hSt z hcs _ _)

/-! ## Step 2 — the deferred exact FOREST value (HOMOGENEOUS) -/

/-- **body-644 (Step 2, HEADLINE) — the deferred exact FOREST `Sum.inr` value, HOMOGENEOUS.**  The owner is
FIXED to the recovered parent `recoveredParent (fd z hδ)` from the START, so the statement lives entirely in
`StableLocalForestIdx (recoveredParent (fd z hδ))` — NO cross-type equation.  The `Exists.choose`-selected
witness recovers `δ` (`hcs` by injectivity), so Step-1's transport collapse identifies the two payloads.
Discharges body-643's `stableRecoveredChoice_forest_isRight` scope guard (the exact witness value). -/
theorem stableRecoveredChoice_forest_value (hSt : StableResolvedBoundaryIds G)
    (z : Phi4WTriplePrimeInverseCodomain G) {δ : {x // x ∈ z.2.1.elements}}
    (hδ : phi4WTriplePrime_inv_isForestImage z δ)
    (hγ : phi4WTriplePrime_inv_recoveredParent
        (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδ)
      ∈ (phi4WTriplePrime_recoveredOuter z).elements) :
    stableRecoveredChoice hSt z
        ⟨phi4WTriplePrime_inv_recoveredParent
          (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδ), hγ⟩
        (Finset.mem_attach _ _)
      = Sum.inr (stableInvRecoveredInnerForestValue hSt
          (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδ)) := by
  have hq : ∃ d : {x // x ∈ z.2.1.elements},
      phi4WTriplePrime_inv_regionComponentOf z d
        = phi4WTriplePrime_inv_recoveredParent
            (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδ) :=
    ⟨δ, phi4WTriplePrime_inv_regionComponentOf_eq_parent z hδ⟩
  have hcs : hq.choose = δ :=
    phi4WTriplePrime_inv_regionComponentOf_injective z
      (hq.choose_spec.trans (phi4WTriplePrime_inv_regionComponentOf_eq_parent z hδ).symm)
  have hst' : phi4WTriplePrime_inv_isForestImage z hq.choose := by rw [hcs]; exact hδ
  rw [show stableRecoveredChoice hSt z
        ⟨phi4WTriplePrime_inv_recoveredParent
          (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδ), hγ⟩
        (Finset.mem_attach _ _)
      = Sum.inr (stableRecoveredForestTag hSt z
          ⟨phi4WTriplePrime_inv_recoveredParent
            (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδ), hγ⟩ hq hst') from by
      unfold stableRecoveredChoice; rw [dif_pos hq]; exact dif_pos hst']
  exact congrArg Sum.inr
    (eq_of_heq (stableRecoveredForestTag_heq hSt z _ hq hst' hδ hcs))

/-! ## Step 3 — the canonical stable forward occurrence -/

/-- **body-644 (Step 3) — the canonical FOREST occurrence of the stable recovered split choice.**  For a
star-touching `δ`, the recovered-outer component `recoveredParent (fd z hδ)` is a `Sum.inr` owner carrying
body-642's stable inner forest — a `⟨…⟩` value into the EXISTING body-635 `StableForestChoiceOccurrence`
(NO new structure).  `hchoice` is Step 2 (through the `_base` / `_choice` rfl accessors). -/
noncomputable def stableRecoveredForwardOccurrence (hSt : StableResolvedBoundaryIds G)
    (z : Phi4WTriplePrimeInverseCodomain G) {δ : {x // x ∈ z.2.1.elements}}
    (hδ : phi4WTriplePrime_inv_isForestImage z δ) :
    StableForestChoiceOccurrence (stableRecoveredSplitChoice hSt z) where
  γ := ⟨phi4WTriplePrime_inv_recoveredParent
      (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδ),
    (phi4WTriplePrime_inv_regionComponentOf_eq_parent z hδ)
      ▸ phi4WTriplePrime_inv_regionComponent_mem_recoveredOuter z δ⟩
  B := stableInvRecoveredInnerForestValue hSt
    (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδ)
  hchoice := stableRecoveredChoice_forest_value hSt z hδ _

/-! ## Step 4 — promotion recovery at one owner -/

/-- **body-644 (Step 4) — the promoted set at a recovered forest owner is the touched outer forest.**  At the
recovered parent of a star-touching `δ`, the stable choice is `Sum.inr` of body-642's stable inner forest
(Step 2), so `stablePromotedElemsAt` picks the `.image` branch, which is body-642's `rootRelative_image`
VERBATIM — the touched outer forest's element set.  NO promotion geometry re-proved. -/
theorem stablePromotedElemsAt_recoveredForestOwner (hSt : StableResolvedBoundaryIds G)
    (z : Phi4WTriplePrimeInverseCodomain G) {δ : {x // x ∈ z.2.1.elements}}
    (hδ : phi4WTriplePrime_inv_isForestImage z δ)
    (hγ : phi4WTriplePrime_inv_recoveredParent
        (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδ)
      ∈ (phi4WTriplePrime_recoveredOuter z).elements) :
    stablePromotedElemsAt (stableRecoveredResolvedSplitChoice hSt z)
        ⟨phi4WTriplePrime_inv_recoveredParent
          (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδ), hγ⟩
      = (phi4WTriplePrime_touchedOuterForest z δ).elements := by
  have hchoice : (stableRecoveredResolvedSplitChoice hSt z).choice
        ⟨phi4WTriplePrime_inv_recoveredParent
          (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδ), hγ⟩
        (Finset.mem_attach _ _)
      = Sum.inr (stableInvRecoveredInnerForestValue hSt
          (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδ)) := by
    rw [stableRecoveredResolvedSplitChoice_choice]
    exact stableRecoveredChoice_forest_value hSt z hδ hγ
  unfold stablePromotedElemsAt
  rw [hchoice]
  simp only [Sum.elim_inr]
  exact stableInvRecoveredInnerForest_rootRelative_image hSt
    (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδ)

/-! ## Step 5 — HEADLINE: the raw outer equality -/

/-- **body-644 (Step 5, PRIVATE) — a clean element-set extensionality for φ⁴ admissible subgraphs.**  Bypasses
the polluted `ResolvedAdmissibleSubgraph.ext_elements` (which carries a forbidden `[IsAmbientInvariantDivergence]`
section binder): the two non-`elements` fields are `Prop`s, so equal element sets force equality by `cases` +
definitional proof irrelevance.  NO forbidden divergence class in the type.  PRIVATE (file-local re-derivation,
mirror of body-620's clean ext). -/
private theorem stable_admissible_ext_elements
    {A₁ A₂ : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G}
    (h : @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G A₁
       = @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G A₂) : A₁ = A₂ := by
  cases A₁; cases A₂; cases h; rfl

/-- **body-644 (Step 5, HEADLINE) — the stable outer raw equality.**  `stableSelectedOuter` of the stable
recovered resolved split choice reconstructs the original outer forest `z.1.1` EXACTLY (a raw
`ResolvedAdmissibleSubgraph` equality via the clean ext): LEFT components come back verbatim; the FOREST
promotions re-inflate to the touched outer components (Step 4 + body-642's `rootRelative_image`).  Identifies
the ambient PROPOSITIONALLY only (same `G`).  STABLE mirror of body-620's
`phi4WTriplePrime_selectedOuter_recoveredSplitChoice`. -/
theorem stableSelectedOuter_recoveredSplitChoice (hSt : StableResolvedBoundaryIds G)
    (z : Phi4WTriplePrimeInverseCodomain G) :
    stableSelectedOuter (stableRecoveredResolvedSplitChoice hSt z) = z.1.1 := by
  apply stable_admissible_ext_elements
  rw [stableSelectedOuter_elements]
  ext c
  rw [Finset.mem_union]
  constructor
  · rintro (hL | hP)
    · -- c ∈ leftOf.elements → c ∈ A
      rw [stableLeftOf_elements, Finset.mem_filter] at hL
      obtain ⟨hcRO, hlp⟩ := hL
      rcases phi4WTriplePrime_recoveredOuter_component_origin z hcRO with ⟨hcA, _⟩ | ⟨δc, hδceq⟩
      · exact hcA
      · exfalso
        obtain ⟨hh, htrue⟩ := hlp
        have hq : ∃ d : {x // x ∈ z.2.1.elements},
            phi4WTriplePrime_inv_regionComponentOf z d = c := ⟨δc, hδceq⟩
        by_cases hst : phi4WTriplePrime_inv_isForestImage z hq.choose
        · rw [show (stableRecoveredResolvedSplitChoice hSt z).choice ⟨c, hh⟩ (Finset.mem_attach _ _)
                = Sum.inr (stableRecoveredForestTag hSt z ⟨c, hh⟩ hq hst) from by
                  rw [stableRecoveredResolvedSplitChoice_choice]
                  unfold stableRecoveredChoice
                  rw [dif_pos hq]; exact dif_pos hst] at htrue
          simp at htrue
        · rw [show (stableRecoveredResolvedSplitChoice hSt z).choice ⟨c, hh⟩ (Finset.mem_attach _ _)
                = Sum.inl false from by
                  rw [stableRecoveredResolvedSplitChoice_choice]
                  unfold stableRecoveredChoice
                  rw [dif_pos hq]; exact dif_neg hst] at htrue
          simp at htrue
    · -- c ∈ promotedOf.elements → c ∈ A
      rw [stablePromotedOf_elements, Finset.mem_biUnion] at hP
      obtain ⟨a, -, hca⟩ := hP
      rcases hcc : (stableRecoveredResolvedSplitChoice hSt z).choice a (Finset.mem_attach _ a) with b | B
      · -- primitive leg → promoted set empty
        exfalso
        rw [show stablePromotedElemsAt (stableRecoveredResolvedSplitChoice hSt z) a = ∅
              from by unfold stablePromotedElemsAt; rw [hcc]; simp only [Sum.elim_inl]] at hca
        simp at hca
      · -- forest leg → forest owner → touched outer forest ⊆ A
        have hq : ∃ d : {x // x ∈ z.2.1.elements},
            phi4WTriplePrime_inv_regionComponentOf z d = a.1 := by
          by_contra hnq
          rw [show (stableRecoveredResolvedSplitChoice hSt z).choice a (Finset.mem_attach _ a)
                = Sum.inl true from by
                  rw [stableRecoveredResolvedSplitChoice_choice]
                  unfold stableRecoveredChoice; rw [dif_neg hnq]] at hcc
          simp at hcc
        have hst : phi4WTriplePrime_inv_isForestImage z hq.choose := by
          by_contra hns
          rw [show (stableRecoveredResolvedSplitChoice hSt z).choice a (Finset.mem_attach _ a)
                = Sum.inl false from by
                  rw [stableRecoveredResolvedSplitChoice_choice]
                  unfold stableRecoveredChoice; rw [dif_pos hq, dif_neg hns]] at hcc
          simp at hcc
        have hav : a.1 = phi4WTriplePrime_inv_recoveredParent
                          (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hst) :=
          hq.choose_spec.symm.trans (phi4WTriplePrime_inv_regionComponentOf_eq_parent z hst)
        have ha_eq : a = ⟨phi4WTriplePrime_inv_recoveredParent
              (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hst), hav ▸ a.2⟩ :=
          Subtype.ext hav
        have hset : stablePromotedElemsAt (stableRecoveredResolvedSplitChoice hSt z) a
            = (phi4WTriplePrime_touchedOuterForest z hq.choose).elements :=
          (congrArg (stablePromotedElemsAt (stableRecoveredResolvedSplitChoice hSt z)) ha_eq).trans
            (stablePromotedElemsAt_recoveredForestOwner hSt z hst (hav ▸ a.2))
        rw [hset] at hca
        exact phi4WTriplePrime_inv_touchedForest_subset_A hca
  · intro hc
    by_cases hL : phi4WTriplePrime_inv_isLeftComponent z c
    · -- LEFT → leftOf
      left
      rw [stableLeftOf_elements, Finset.mem_filter]
      exact ⟨phi4WTriplePrime_inv_left_mem_recoveredOuter z hc hL,
        phi4WTriplePrime_inv_left_mem_recoveredOuter z hc hL,
        stableRecoveredChoice_left hSt z hc hL (Finset.mem_attach _ _)⟩
    · -- non-left → touched → promotedOf
      right
      obtain ⟨δ, hδv⟩ := (phi4WTriplePrime_inv_not_isLeftComponent_iff z c).mp hL
      have hδf : phi4WTriplePrime_inv_isForestImage z δ :=
        ⟨phi4WTriplePrimeCanonicalSupply.starOf G z.1.1 c, hδv,
          ResolvedAdmissibleSubgraph.mem_starVertices.mpr ⟨c, hc, rfl⟩⟩
      have hcT : c ∈ (phi4WTriplePrime_touchedOuterForest z δ).elements :=
        phi4WTriplePrime_inv_touched_of_starA_mem hc hδv
      rw [stablePromotedOf_elements, Finset.mem_biUnion]
      have hmem : phi4WTriplePrime_inv_recoveredParent
                    (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδf)
                  ∈ (phi4WTriplePrime_recoveredOuter z).elements :=
        (phi4WTriplePrime_inv_regionComponentOf_eq_parent z hδf)
          ▸ phi4WTriplePrime_inv_regionComponent_mem_recoveredOuter z δ
      refine ⟨⟨phi4WTriplePrime_inv_recoveredParent
                (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδf), hmem⟩,
        Finset.mem_attach _ _, ?_⟩
      rw [stablePromotedElemsAt_recoveredForestOwner hSt z hδf hmem]
      exact hcT

end GaugeGeometry.QFT.Combinatorial
