import GaugeGeometry.QFT.HopfAlgebra.Phi4StableRecoveredInnerForest
import GaugeGeometry.QFT.HopfAlgebra.Phi4WTriplePrimeRecoveredInverse

/-!
# QFT-R1-body-643 — the source-independent STABLE recovered split choice

Body-642 rebuilt the FOREST payload of the inverse map in stable normal form
(`stableInvRecoveredInnerForestValue : StableLocalForestIdx (recoveredParent I)`).  This body assembles, for the
FIRST time in STABLE type, the whole INVERSE FUNCTION owner: from any `z : Phi4WTriplePrimeInverseCodomain G`
it builds a `StablePhi4MixedSplitChoice G hSt` with ZERO residual field.  It is a WIRING / OWNERSHIP assembly
(NO geometry re-proof) — the OLD body-614/617/619 `recoveredChoice` / `recoveredForestTag` /
`recoveredSplitChoice` PROOF SHAPE is MIRRORED on the STABLE carrier, with body-642's stable FOREST payload
plugged in.  The old inverse is NEVER consumed as a term — only its proof shape is mirrored.

## Steps
* **Step 1** — `stableRecoveredForestTag`: the FOREST tag `StableLocalForestIdx γ.1`.  Owner-fix via
  `hq.choose_spec` (`regionComponentOf z hq.choose = γ.1`); the stable payload
  `stableInvRecoveredInnerForestValue hSt I : StableLocalForestIdx (recoveredParent I)` is transported to
  `StableLocalForestIdx γ.1` along the GENUINE `ResolvedFeynmanSubgraph G` equality
  `heq : recoveredParent I = γ.1` (the ONE permitted owner-alignment `▸`; NO cross-ambient HEq, NO `cast`).
* **Step 2** — `stableRecoveredChoice`: the three-way `dite` (FOREST → `Sum.inr` of the tag; RIGHT →
  `Sum.inl false`; LEFT → `Sum.inl true`) directly into the STABLE codomain
  `StablePhi4ComponentChoice (recoveredOuter z)`.
* **Step 3** — the tag anchors: `_left` (`Sum.inl true`), `_right` (`Sum.inl false`), `_forest_isRight`
  (`.isRight = true`), `_forest_owner_unique` (`= regionComponentOf_injective`).  The EXACT FOREST `Sum.inr`
  value across `Exists.choose` witnesses is DEFERRED (forward-image scope guard, body-614 style).
* **Step 4** — `stableRecoveredChoice_mem`: carrier membership (`stablePhi4_mem_globalChoiceCarrier`).
* **Step 5** — mixedness: `_not_all_right` / `_not_all_left` (mirror the body-617/619 non-purity shape).
* **Step 6** — the TARGET: `stableRecoveredResolvedSplitChoice : StablePhi4ResolvedSplitChoice G hSt` and
  `stableRecoveredSplitChoice : … → StablePhi4MixedSplitChoice G hSt` (residual-field-free), + accessors.

## Ownership boundary — MUST NOT consume as terms
The OLD `phi4WTriplePrime_recoveredChoice` / `recoveredForestTag` / `recoveredSplitChoice` /
`recoveredSplitChoiceValue`, the OLD `phi4WTriplePrime_inv_recoveredInnerForest`, and the OLD forest-block
`Equiv` (623).  Only the completion-INDEPENDENT scaffolding (`recoveredOuter` / `regionComponentOf` /
`isForestImage` / `recoveredParent` / the outer-membership BANK) is reused.

## HALT / red lines
`stableForestBlockForward (stableRecoveredSplitChoice hSt z) = z` is NOT asserted; inverse-after-forward is NOT
entered; `StablePhi4ForestBlockForwardBijective` is NOT proved.  NO round-trip / Equiv / `Finset.sum_bij` /
alpha / coassoc / `Bijective`.  ZERO consume of the OLD choice / tag / split-choice / inner forest / 623 Equiv.
ZERO new `structure` / `class` / permanent `instance` (one file-local `local instance`; the split-choice is a
`⟨…⟩` builder into the EXISTING `StablePhi4ResolvedSplitChoice` / `StablePhi4MixedSplitChoice`).  ZERO PUBLIC
transport API / `HEq` / `cast`; the ONLY `▸` are Step-1's owner-alignment on the genuine `heq` and Prop-
membership rewrites.  Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

open ResolvedFeynmanSubgraph

variable {G : ResolvedFeynmanGraph}

set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-- The concrete φ⁴ divergence measure family, registered file-locally (providable instance, NO forbidden
class). -/
noncomputable local instance instPhi4DivergenceMeasureFamily643 : (H : FeynmanGraph) → DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

/-! ## Step 1 — the stable FOREST tag -/

/-- **body-643 (Step 1) — the transported STABLE FOREST tag.**  For a recovered-outer component `γ` that is a
recovered quotient-region image (`hq`) of a star-touching `δ = hq.choose` (`hst`), the FOREST tag is body-642's
stable recovered inner forest, carried across the recovered-parent / recovered-outer identification.

The payload `stableInvRecoveredInnerForestValue hSt I : StableLocalForestIdx (recoveredParent I)` (with
`I := forestDecontractionInput_of_starTouching z hst`) is transported to `StableLocalForestIdx γ.1` along the
GENUINE `ResolvedFeynmanSubgraph G` equality `heq : recoveredParent I = γ.1`
(`= (regionComponentOf_eq_parent z hst).symm.trans hq.choose_spec`).  Both sides live over the SAME ambient
`G`, so this `▸` is an honest owner-alignment — NOT a cross-ambient HEq, NOT a `cast`.  STABLE mirror of body-
614:424's `heq ▸`, with the stable payload. -/
noncomputable def stableRecoveredForestTag (hSt : StableResolvedBoundaryIds G)
    (z : Phi4WTriplePrimeInverseCodomain G)
    (γ : {x // x ∈ (phi4WTriplePrime_recoveredOuter z).elements})
    (hq : ∃ δ : {x // x ∈ z.2.1.elements}, phi4WTriplePrime_inv_regionComponentOf z δ = γ.1)
    (hst : phi4WTriplePrime_inv_isForestImage z hq.choose) :
    StableLocalForestIdx γ.1 :=
  have heq : phi4WTriplePrime_inv_recoveredParent
      (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hst) = γ.1 :=
    (phi4WTriplePrime_inv_regionComponentOf_eq_parent z hst).symm.trans hq.choose_spec
  heq ▸ stableInvRecoveredInnerForestValue hSt
    (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hst)

/-! ## Step 2 — the stable recovered global choice -/

/-- **body-643 (Step 2, HEADLINE) — the stable recovered global choice value.**  Each recovered-outer
component is assigned its region tag in the STABLE codomain: LEFT → `Sum.inl true`; RIGHT → `Sum.inl false`;
FOREST → `Sum.inr` of the stable recovered inner W‴ forest (Step 1).  Defined DIRECTLY into
`StablePhi4ComponentChoice (recoveredOuter z)`; the OLD `recoveredChoice` is NOT converted.  Reads only `z`.
STABLE mirror of body-614:445. -/
noncomputable def stableRecoveredChoice (hSt : StableResolvedBoundaryIds G)
    (z : Phi4WTriplePrimeInverseCodomain G) :
    StablePhi4ComponentChoice (phi4WTriplePrime_recoveredOuter z) :=
  fun γ _ =>
    if hq : ∃ δ : {x // x ∈ z.2.1.elements}, phi4WTriplePrime_inv_regionComponentOf z δ = γ.1 then
      if hst : phi4WTriplePrime_inv_isForestImage z hq.choose then
        Sum.inr (stableRecoveredForestTag hSt z γ hq hst)
      else
        Sum.inl false
    else
      Sum.inl true

/-! ## Step 3 — the tag anchors -/

/-- **body-643 (Step 3, LEFT tag) — the stable recovered choice at a LEFT component is `Sum.inl true`.**
STABLE mirror of body-614:478. -/
theorem stableRecoveredChoice_left (hSt : StableResolvedBoundaryIds G)
    (z : Phi4WTriplePrimeInverseCodomain G)
    {γ : ResolvedFeynmanSubgraph G} (hγA : γ ∈ z.1.1.elements)
    (hL : phi4WTriplePrime_inv_isLeftComponent z γ)
    (h : (⟨γ, phi4WTriplePrime_inv_left_mem_recoveredOuter z hγA hL⟩ :
        {x // x ∈ (phi4WTriplePrime_recoveredOuter z).elements})
      ∈ (phi4WTriplePrime_recoveredOuter z).elements.attach) :
    stableRecoveredChoice hSt z
        ⟨γ, phi4WTriplePrime_inv_left_mem_recoveredOuter z hγA hL⟩ h = Sum.inl true := by
  have hno : ¬ ∃ δ : {x // x ∈ z.2.1.elements},
      phi4WTriplePrime_inv_regionComponentOf z δ = γ := by
    rintro ⟨δ, hδ⟩
    have hdisj := phi4WTriplePrime_inv_left_regionComponent_disjoint z hγA hL δ
    rw [hδ] at hdisj
    obtain ⟨v, hv⟩ := Finset.card_pos.mp ((phi4WTriplePrime_inv_A_isProperForest z).2.1 γ hγA)
    exact Finset.disjoint_left.mp hdisj hv hv
  unfold stableRecoveredChoice
  rw [dif_neg hno]

/-- **body-643 (Step 3, RIGHT tag) — the stable recovered choice at a RIGHT component is `Sum.inl false`.**
STABLE mirror of body-614:497. -/
theorem stableRecoveredChoice_right (hSt : StableResolvedBoundaryIds G)
    (z : Phi4WTriplePrimeInverseCodomain G)
    {δ₀ : {x // x ∈ z.2.1.elements}} (hfree : ¬ phi4WTriplePrime_inv_isForestImage z δ₀)
    (h : (⟨phi4WTriplePrime_inv_regionComponentOf z δ₀,
        phi4WTriplePrime_inv_regionComponent_mem_recoveredOuter z δ₀⟩ :
        {x // x ∈ (phi4WTriplePrime_recoveredOuter z).elements})
      ∈ (phi4WTriplePrime_recoveredOuter z).elements.attach) :
    stableRecoveredChoice hSt z
        ⟨phi4WTriplePrime_inv_regionComponentOf z δ₀,
          phi4WTriplePrime_inv_regionComponent_mem_recoveredOuter z δ₀⟩ h = Sum.inl false := by
  unfold stableRecoveredChoice
  have hq : ∃ δ : {x // x ∈ z.2.1.elements},
      phi4WTriplePrime_inv_regionComponentOf z δ = phi4WTriplePrime_inv_regionComponentOf z δ₀ :=
    ⟨δ₀, rfl⟩
  rw [dif_pos hq]
  have hchoose : hq.choose = δ₀ :=
    phi4WTriplePrime_inv_regionComponentOf_injective z hq.choose_spec
  rw [dif_neg (show ¬ phi4WTriplePrime_inv_isForestImage z hq.choose by rw [hchoose]; exact hfree)]

/-- **body-643 (Step 3, FOREST tag) — the stable recovered choice at a FOREST component is a `Sum.inr`.**
Recorded via `isRight`, with owner determinacy below fixing the occurrence.  The EXACT explicit-witness value
equation `= Sum.inr (stableRecoveredForestTag …)` for a fixed `δ₀` is a dependent round-trip alignment over the
`Exists.choose`-selected `δ` — a NAMED forward-image obligation, discharged there (same body-614 scope guard),
deliberately NOT built here.  STABLE mirror of body-614:520. -/
theorem stableRecoveredChoice_forest_isRight (hSt : StableResolvedBoundaryIds G)
    (z : Phi4WTriplePrimeInverseCodomain G)
    {δ₀ : {x // x ∈ z.2.1.elements}} (hst₀ : phi4WTriplePrime_inv_isForestImage z δ₀)
    (h : (⟨phi4WTriplePrime_inv_regionComponentOf z δ₀,
        phi4WTriplePrime_inv_regionComponent_mem_recoveredOuter z δ₀⟩ :
        {x // x ∈ (phi4WTriplePrime_recoveredOuter z).elements})
      ∈ (phi4WTriplePrime_recoveredOuter z).elements.attach) :
    (stableRecoveredChoice hSt z
        ⟨phi4WTriplePrime_inv_regionComponentOf z δ₀,
          phi4WTriplePrime_inv_regionComponent_mem_recoveredOuter z δ₀⟩ h).isRight = true := by
  unfold stableRecoveredChoice
  have hq : ∃ δ : {x // x ∈ z.2.1.elements},
      phi4WTriplePrime_inv_regionComponentOf z δ = phi4WTriplePrime_inv_regionComponentOf z δ₀ :=
    ⟨δ₀, rfl⟩
  rw [dif_pos hq]
  have hchoose : hq.choose = δ₀ :=
    phi4WTriplePrime_inv_regionComponentOf_injective z hq.choose_spec
  rw [dif_pos (show phi4WTriplePrime_inv_isForestImage z hq.choose by rw [hchoose]; exact hst₀)]
  rfl

/-- **body-643 (Step 3, owner determinacy) — the FOREST occurrence is determined by its recovered-outer
component** (injectivity of `regionComponentOf`).  STABLE mirror of body-614:541. -/
theorem stableRecoveredChoice_forest_owner_unique (z : Phi4WTriplePrimeInverseCodomain G)
    {δ₀ δ : {x // x ∈ z.2.1.elements}}
    (h : phi4WTriplePrime_inv_regionComponentOf z δ = phi4WTriplePrime_inv_regionComponentOf z δ₀) :
    δ = δ₀ :=
  phi4WTriplePrime_inv_regionComponentOf_injective z h

/-! ## Step 4 — the finite carrier membership -/

/-- **body-643 (Step 4) — the stable recovered choice is a valid global component choice.**  The 641 local
carriers cover the whole `Bool ⊕ StableLocalForestIdx` fibre, so ANY component-choice function lands in the
global carrier.  STABLE mirror of body-614:460. -/
theorem stableRecoveredChoice_mem (hSt : StableResolvedBoundaryIds G)
    (z : Phi4WTriplePrimeInverseCodomain G) :
    stableRecoveredChoice hSt z
      ∈ stablePhi4GlobalChoiceCarrier hSt (phi4WTriplePrime_recoveredOuter z) :=
  stablePhi4_mem_globalChoiceCarrier hSt (phi4WTriplePrime_recoveredOuter z)
    (stableRecoveredChoice hSt z)

/-! ## Step 5 — mixedness (not-all-RIGHT and not-all-LEFT) -/

/-- **body-643 (Step 5) — the stable recovered choice is NOT the all-RIGHT choice.**  Either some `A`-component
is LEFT (tagged `Sum.inl true`), or — if none is — the nonempty `z.1.1` has a component whose canonical star
lands in some `δ₀`, making `δ₀` star-touching (FOREST, `.isRight`); either way a component is tagged
`≠ Sum.inl false`.  STABLE mirror of body-617's `_ne_pureRight`. -/
theorem stableRecoveredChoice_not_all_right (hSt : StableResolvedBoundaryIds G)
    (z : Phi4WTriplePrimeInverseCodomain G) :
    ∃ (a : {x // x ∈ (phi4WTriplePrime_recoveredOuter z).elements})
      (hatt : a ∈ (phi4WTriplePrime_recoveredOuter z).elements.attach),
      stableRecoveredChoice hSt z a hatt ≠ Sum.inl false := by
  by_cases hLex : ∃ γ : ResolvedFeynmanSubgraph G,
      γ ∈ z.1.1.elements ∧ phi4WTriplePrime_inv_isLeftComponent z γ
  · obtain ⟨γ, hγA, hLc⟩ := hLex
    refine ⟨⟨γ, phi4WTriplePrime_inv_left_mem_recoveredOuter z hγA hLc⟩, Finset.mem_attach _ _, ?_⟩
    intro hEq
    have hL := stableRecoveredChoice_left hSt z hγA hLc (Finset.mem_attach _ _)
    rw [hEq] at hL
    exact absurd (Sum.inl.inj hL) (by decide)
  · push_neg at hLex
    obtain ⟨c, hc⟩ := (phi4WTriplePrime_inv_A_isProperForest z).1
    have hnotL : ¬ phi4WTriplePrime_inv_isLeftComponent z c := hLex c hc
    rw [phi4WTriplePrime_inv_not_isLeftComponent_iff] at hnotL
    obtain ⟨δ₀, hstar⟩ := hnotL
    have hst : phi4WTriplePrime_inv_isForestImage z δ₀ :=
      ⟨phi4WTriplePrimeCanonicalSupply.starOf G z.1.1 c, hstar,
        ResolvedAdmissibleSubgraph.mem_starVertices.mpr ⟨c, hc, rfl⟩⟩
    refine ⟨⟨phi4WTriplePrime_inv_regionComponentOf z δ₀,
        phi4WTriplePrime_inv_regionComponent_mem_recoveredOuter z δ₀⟩, Finset.mem_attach _ _, ?_⟩
    intro hEq
    have hR := stableRecoveredChoice_forest_isRight hSt z hst (Finset.mem_attach _ _)
    rw [hEq] at hR
    simp only [Sum.isRight_inl] at hR
    exact absurd hR (by decide)

/-- **body-643 (Step 5) — the stable recovered choice is NOT the all-LEFT choice.**  `z.2.1` is a proper forest,
hence has a component `δ₀`; its recovered quotient-region component is tagged `Sum.inl false` (RIGHT) or
`Sum.inr …` (FOREST) — never `Sum.inl true`.  STABLE mirror of body-617's `_ne_pureLeft`. -/
theorem stableRecoveredChoice_not_all_left (hSt : StableResolvedBoundaryIds G)
    (z : Phi4WTriplePrimeInverseCodomain G) :
    ∃ (a : {x // x ∈ (phi4WTriplePrime_recoveredOuter z).elements})
      (hatt : a ∈ (phi4WTriplePrime_recoveredOuter z).elements.attach),
      stableRecoveredChoice hSt z a hatt ≠ Sum.inl true := by
  obtain ⟨d, hd⟩ := (phi4WTriplePrime_inv_B_isProperForest z).1
  set δ₀ : {x // x ∈ z.2.1.elements} := ⟨d, hd⟩ with hδ₀
  refine ⟨⟨phi4WTriplePrime_inv_regionComponentOf z δ₀,
      phi4WTriplePrime_inv_regionComponent_mem_recoveredOuter z δ₀⟩, Finset.mem_attach _ _, ?_⟩
  by_cases hst : phi4WTriplePrime_inv_isForestImage z δ₀
  · intro hEq
    have hR := stableRecoveredChoice_forest_isRight hSt z hst (Finset.mem_attach _ _)
    rw [hEq] at hR
    simp only [Sum.isRight_inl] at hR
    exact absurd hR (by decide)
  · intro hEq
    have hF := stableRecoveredChoice_right hSt z hst (Finset.mem_attach _ _)
    rw [hEq] at hF
    exact absurd (Sum.inl.inj hF) (by decide)

/-! ## Step 6 — the TARGET: the stable recovered split choice -/

/-- **body-643 (Step 6, TARGET base) — the stable recovered resolved split choice.**  All four fields from
Steps 1–5: `outer := recoveredOuter z` with its body-619 W‴ membership, `choice := stableRecoveredChoice z`,
and `choice_nontrivial := not_all_right`.  ZERO residual field.  A `⟨…⟩` builder into the EXISTING
`StablePhi4ResolvedSplitChoice` — NO new structure. -/
noncomputable def stableRecoveredResolvedSplitChoice (hSt : StableResolvedBoundaryIds G)
    (z : Phi4WTriplePrimeInverseCodomain G) : StablePhi4ResolvedSplitChoice G hSt where
  outer := phi4WTriplePrime_recoveredOuter z
  outer_mem := phi4WTriplePrime_recoveredOuter_mem z
  choice := stableRecoveredChoice hSt z
  choice_nontrivial := stableRecoveredChoice_not_all_right hSt z

/-- **body-643 (Step 6, TARGET) — the source-independent STABLE recovered split choice.**  The mixed
split-choice owner, a function of an arbitrary codomain `z` alone: the resolved base plus the not-all-LEFT
witness (`_not_all_left`).  ZERO residual field.  A `⟨…⟩` builder into the EXISTING `StablePhi4MixedSplitChoice`
— NO new structure.  STABLE mirror of body-619's `recoveredSplitChoice`. -/
noncomputable def stableRecoveredSplitChoice (hSt : StableResolvedBoundaryIds G)
    (z : Phi4WTriplePrimeInverseCodomain G) : StablePhi4MixedSplitChoice G hSt :=
  ⟨stableRecoveredResolvedSplitChoice hSt z, stableRecoveredChoice_not_all_left hSt z⟩

/-- **body-643 (Step 6, accessor) — the recovered split choice's outer forest. -/
@[simp] theorem stableRecoveredResolvedSplitChoice_outer (hSt : StableResolvedBoundaryIds G)
    (z : Phi4WTriplePrimeInverseCodomain G) :
    (stableRecoveredResolvedSplitChoice hSt z).outer = phi4WTriplePrime_recoveredOuter z := rfl

/-- **body-643 (Step 6, accessor) — the recovered split choice's global choice. -/
@[simp] theorem stableRecoveredResolvedSplitChoice_choice (hSt : StableResolvedBoundaryIds G)
    (z : Phi4WTriplePrimeInverseCodomain G) :
    (stableRecoveredResolvedSplitChoice hSt z).choice = stableRecoveredChoice hSt z := rfl

/-- **body-643 (Step 6, accessor) — the mixed recovered split choice's base is the resolved recovered split
choice. -/
@[simp] theorem stableRecoveredSplitChoice_base (hSt : StableResolvedBoundaryIds G)
    (z : Phi4WTriplePrimeInverseCodomain G) :
    (stableRecoveredSplitChoice hSt z).1 = stableRecoveredResolvedSplitChoice hSt z := rfl

end GaugeGeometry.QFT.Combinatorial
