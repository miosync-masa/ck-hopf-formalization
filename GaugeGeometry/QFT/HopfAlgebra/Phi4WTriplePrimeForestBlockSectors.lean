import GaugeGeometry.QFT.HopfAlgebra.Phi4WTriplePrimeQuotientForest

/-!
# QFT-R1-body-607 — W‴ forest-block sectors + component correspondence

Bodies 602/606 made both `selectedOuter s` and `quotientForest s` live W‴ members.  This body fixes the
forest-block FORWARD map (reading those two) and the **component-level sector correspondence** — a bijection
between the source `Right ⊕ Forest-occurrence` index and the quotient forest's components — plus a
star-incidence classifier that lets body-608 invert it.

SCOPE STOPS at the component `Equiv` + classifier: NO global inverse, NO whole-forest-block bijection, NO
summand agreement, NO `sum_bij` / `rightTerm` / `quot_eq` / alpha / coassoc.

## What closes cleanly

* **forward map** — `phi4WTriplePrime_forestBlockForward s = ⟨⟨selectedOuter, mem⟩, ⟨quotientForest, mem⟩⟩`
  (the second index ambient is definitionally `Q = selectedOuter.contractWithStars starOf`).
* **the component `Equiv`** — `Right ⊕ Forest-occurrence ≃ {δ // δ ∈ quotientForest.elements}` via
  `Equiv.ofBijective`.  Injectivity: inl/inl by 603 `survivor_injOn`; inr/inr by 605 `remnant_injOn`
  (contrapositive → equal owners) + the new occurrence-determinacy ext (equal `.γ` ⇒ equal `.B` from
  `hchoice`); inl/inr (cross) by the star classifier (survivor vertices are star-free, remnant vertices are
  star-touching).  Surjectivity: 606 `quotientForest_element_cases`.
* **star classifier** — `isForestImage δ := (δ has a vertex on selectedOuter.starVertices)`; survivor images
  are star-FREE (freshness of `starOf` outside `G`), remnant images are star-TOUCHING (a promoted global
  star, `remnantTau_map`), so `isForestImage ↔ RemnantSector`, `¬ isForestImage ↔ RightSector`.

## HALT compliance

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only); ZERO forbidden divergence classes in ANY
declaration's type (the survivor-embed stack / `resolvedComponentGen` / polluted supply lemmas are NOT
consumed).  No `sorry` / `admit` / `native_decide`.  NO strict cross-presentation star equality (only the
canonical star's freshness/injectivity and the body-604 designated-star witness `remnantTau_map`).  No
global inverse, no whole-forest-block `Equiv`, no `sum_bij`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

open ResolvedFeynmanSubgraph

variable {G : ResolvedFeynmanGraph}

set_option maxHeartbeats 3200000

/-- The concrete φ⁴ divergence measure family, registered file-locally (providable instance, NO forbidden
class). -/
noncomputable local instance phi4Inst607 : (H : FeynmanGraph) → DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

/-! ## Step 0 — the right-component index type + occurrence determinacy -/

/-- **body-607 (Step 0) — the right-component index type** (source `Sum.inl` sector). -/
def phi4WTriplePrime_RightComponent (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) : Type :=
  {γ : ResolvedFeynmanSubgraph G // phi4WTriplePrime_isRightComponent s γ}

/-- **body-607 (Step 0) — occurrence determinacy.**  A `ForestChoiceOccurrence` is determined by its owner:
equal `.γ` (values) force equal `.B` from the pinned `hchoice`, and the `hchoice` field is proof-irrelevant. -/
theorem phi4WTriplePrime_occurrence_ext {s : Phi4EdgeCompleteFilteredCoassocSplitChoice G}
    {o₁ o₂ : Phi4WTriplePrime_ForestChoiceOccurrence s} (hγ : o₁.γ.1 = o₂.γ.1) : o₁ = o₂ := by
  obtain ⟨γ₁, B₁, hc₁⟩ := o₁
  obtain ⟨γ₂, B₂, hc₂⟩ := o₂
  have hγ' : γ₁ = γ₂ := Subtype.ext hγ
  subst hγ'
  have hB : B₁ = B₂ := Sum.inr.inj (hc₁.symm.trans hc₂)
  subst hB
  rfl

/-! ## Step 1 — the raw star-incidence facts (survivor star-free, remnant star-touching) -/

/-- **body-607 (Step 1) — survivor vertices are star-FREE.**  A right survivor's vertices are `γ`'s, hence
inside `G`, while every `selectedOuter`-star is fresh (outside `G`), so no survivor vertex is a star. -/
theorem phi4WTriplePrime_survivor_star_free (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G)
    {γ : ResolvedFeynmanSubgraph G} (hγR : phi4WTriplePrime_isRightComponent s γ) :
    ∀ v ∈ (phi4WTriplePrime_survivor s hγR).vertices,
      v ∉ (phi4WTriplePrime_selectedOuter s).starVertices
        (phi4WTriplePrimeCanonicalSupply.starOf G (phi4WTriplePrime_selectedOuter s)) := by
  intro v hv hstar
  rw [phi4WTriplePrime_survivor_vertices] at hv
  obtain ⟨δ', hδ', hstarv⟩ := ResolvedAdmissibleSubgraph.mem_starVertices.mp hstar
  have hvG : v ∈ G.vertices := γ.vertices_subset hv
  rw [← hstarv] at hvG
  exact phi4WTriplePrime_gen_star_not_mem (phi4WTriplePrime_selectedOuter s)
    (phi4WTriplePrime_selectedOuter_isProperForest s) hδ' hvG

/-- **body-607 (Step 1) — remnant vertices are star-TOUCHING.**  A promoted inner component's local star maps
(under `remnantTau`, `remnantTau_map`) to the global `selectedOuter` star of `rootRelativeInner γ δ₀`; that
vertex lives in the remnant's vertex set (`remnant_isNonempty` route) and in `selectedOuter.starVertices`
(the promoted component is a `selectedOuter` element).  Designated-star witness — NO strict star equality. -/
theorem phi4WTriplePrime_remnant_star_touching {s : Phi4EdgeCompleteFilteredCoassocSplitChoice G}
    (o : Phi4WTriplePrime_ForestChoiceOccurrence s) :
    ∃ v ∈ (phi4WTriplePrime_remnantComponent o).vertices,
      v ∈ (phi4WTriplePrime_selectedOuter s).starVertices
        (phi4WTriplePrimeCanonicalSupply.starOf G (phi4WTriplePrime_selectedOuter s)) := by
  obtain ⟨δ₀, hδ₀⟩ := (phi4WTriplePrime_occ_B_isProperForest o).1
  refine ⟨phi4WTriplePrime_remnantTau o
      (phi4WTriplePrimeCanonicalSupply.starOf o.γ.1.boundaryCompletedResolvedGraph o.B.1 δ₀), ?_, ?_⟩
  · rw [phi4WTriplePrime_remnantComponent_vertices]
    apply Finset.mem_image.mpr
    refine ⟨phi4WTriplePrimeCanonicalSupply.starOf o.γ.1.boundaryCompletedResolvedGraph o.B.1 δ₀, ?_, rfl⟩
    rw [phi4WTriplePrime_localContractGraph, ResolvedAdmissibleSubgraph.contractWithStars_vertices]
    exact Finset.mem_union_right _
      (ResolvedAdmissibleSubgraph.mem_starVertices.mpr ⟨δ₀, hδ₀, rfl⟩)
  · rw [phi4WTriplePrime_remnantTau_map o ⟨δ₀, hδ₀⟩]
    exact ResolvedAdmissibleSubgraph.mem_starVertices.mpr
      ⟨rootRelativeInner o.γ.1 δ₀, phi4WTriplePrime_remnant_promoted_mem o hδ₀, rfl⟩

/-! ## Step 2 — quotient-forest component membership of the two sectors -/

/-- **body-607 (Step 2) — a right survivor is a quotient-forest component.** -/
theorem phi4WTriplePrime_survivor_mem_quotientForest
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) {γ : ResolvedFeynmanSubgraph G}
    (hγR : phi4WTriplePrime_isRightComponent s γ) :
    phi4WTriplePrime_survivor s hγR ∈ (phi4WTriplePrime_quotientForest s).elements := by
  rw [phi4WTriplePrime_quotientForest_elements]
  refine Finset.mem_union_left _ ?_
  rw [phi4WTriplePrime_rightSurvivorForest_elements]
  have hmemRC : γ ∈ phi4WTriplePrime_rightComponents s :=
    (phi4WTriplePrime_mem_rightComponents s).mpr ⟨hγR.choose, hγR⟩
  exact Finset.mem_image.mpr ⟨⟨γ, hmemRC⟩, Finset.mem_attach _ _, rfl⟩

/-- **body-607 (Step 2) — a decompleted remnant is a quotient-forest component.**  Its owner is a forest
component; occurrence determinacy pins the forest-forest occurrence back to `o`. -/
theorem phi4WTriplePrime_remnantComponent_mem_quotientForest
    {s : Phi4EdgeCompleteFilteredCoassocSplitChoice G}
    (o : Phi4WTriplePrime_ForestChoiceOccurrence s) :
    phi4WTriplePrime_remnantComponent o ∈ (phi4WTriplePrime_quotientForest s).elements := by
  rw [phi4WTriplePrime_quotientForest_elements]
  refine Finset.mem_union_right _ ?_
  rw [phi4WTriplePrime_remnantForest_elements]
  have hmemFC : o.γ.1 ∈ phi4WTriplePrime_forestComponents s :=
    (phi4WTriplePrime_mem_forestComponents s).mpr ⟨o.γ.2, o.γ.2, o.B, o.hchoice⟩
  refine Finset.mem_image.mpr ⟨⟨o.γ.1, hmemFC⟩, Finset.mem_attach _ _, ?_⟩
  exact congrArg phi4WTriplePrime_remnantComponent
    (phi4WTriplePrime_occurrence_ext
      (phi4WTriplePrime_forestComponentOccurrence_owner ⟨o.γ.1, hmemFC⟩))

/-! ## Step 3a — the forward map (Step 1 of the spec) -/

/-- **body-607 (Step 3a) — the forest-block FORWARD map.**  A W‴ filtered split choice maps to the pair of
its `selectedOuter` (in the W‴ index on `G`) and its `quotientForest` (in the W‴ index on the quotient
ambient `Q = selectedOuter.contractWithStars starOf`).  NO inverse is constructed. -/
noncomputable def phi4WTriplePrime_forestBlockForward
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) :
    Σ A : {A // A ∈ phi4WTriplePrimeIndex G},
      {B // B ∈ phi4WTriplePrimeIndex
        ((A.1).contractWithStars (phi4WTriplePrimeCanonicalSupply.starOf G A.1))} :=
  ⟨⟨phi4WTriplePrime_selectedOuter s, phi4WTriplePrime_selectedOuter_mem s⟩,
    ⟨phi4WTriplePrime_quotientForest s, phi4WTriplePrime_quotientForest_mem s⟩⟩

@[simp] theorem phi4WTriplePrime_forestBlockForward_outer
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) :
    (phi4WTriplePrime_forestBlockForward s).1.1 = phi4WTriplePrime_selectedOuter s := rfl

@[simp] theorem phi4WTriplePrime_forestBlockForward_quotient
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) :
    (phi4WTriplePrime_forestBlockForward s).2.1 = phi4WTriplePrime_quotientForest s := rfl

/-! ## Step 3b — the component forward map + bijection (Step 3 of the spec) -/

/-- **body-607 (Step 3b) — the raw component forward map.**  `Sum.inl` → the right survivor, `Sum.inr` → the
decompleted remnant, both landing in the quotient-forest components. -/
noncomputable def phi4WTriplePrime_forestBlockToFun
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) :
    phi4WTriplePrime_RightComponent s ⊕ Phi4WTriplePrime_ForestChoiceOccurrence s
      → {δ // δ ∈ (phi4WTriplePrime_quotientForest s).elements} :=
  fun x => match x with
    | Sum.inl γR => ⟨phi4WTriplePrime_survivor s γR.2,
        phi4WTriplePrime_survivor_mem_quotientForest s γR.2⟩
    | Sum.inr o => ⟨phi4WTriplePrime_remnantComponent o,
        phi4WTriplePrime_remnantComponent_mem_quotientForest o⟩

@[simp] theorem phi4WTriplePrime_forestBlockToFun_inl
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) (γR : phi4WTriplePrime_RightComponent s) :
    (phi4WTriplePrime_forestBlockToFun s (Sum.inl γR)).1 = phi4WTriplePrime_survivor s γR.2 := rfl

@[simp] theorem phi4WTriplePrime_forestBlockToFun_inr
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G)
    (o : Phi4WTriplePrime_ForestChoiceOccurrence s) :
    (phi4WTriplePrime_forestBlockToFun s (Sum.inr o)).1 = phi4WTriplePrime_remnantComponent o := rfl

/-- **body-607 (Step 3b) — the component forward map is injective.**  inl/inl via 603 `survivor_injOn`;
inr/inr via 605 `remnant_injOn` (contrapositive → equal owners) + occurrence determinacy; inl/inr (cross)
via the star classifier (survivor star-free vs. remnant star-touching). -/
theorem phi4WTriplePrime_forestBlockToFun_injective
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) :
    Function.Injective (phi4WTriplePrime_forestBlockToFun s) := by
  rintro (⟨γ₁, h₁⟩ | o₁) (⟨γ₂, h₂⟩ | o₂) heq
  · -- inl / inl
    have hval : phi4WTriplePrime_survivor s h₁ = phi4WTriplePrime_survivor s h₂ :=
      congrArg Subtype.val heq
    have hγ : γ₁ = γ₂ := phi4WTriplePrime_survivor_injOn s h₁ h₂ hval
    subst hγ
    exact congrArg Sum.inl (Subtype.ext rfl)
  · -- inl / inr (cross)
    exfalso
    have hval : phi4WTriplePrime_survivor s h₁ = phi4WTriplePrime_remnantComponent o₂ :=
      congrArg Subtype.val heq
    obtain ⟨v, hv, hstar⟩ := phi4WTriplePrime_remnant_star_touching o₂
    rw [← hval] at hv
    exact phi4WTriplePrime_survivor_star_free s h₁ v hv hstar
  · -- inr / inl (cross)
    exfalso
    have hval : phi4WTriplePrime_remnantComponent o₁ = phi4WTriplePrime_survivor s h₂ :=
      congrArg Subtype.val heq
    obtain ⟨v, hv, hstar⟩ := phi4WTriplePrime_remnant_star_touching o₁
    rw [hval] at hv
    exact phi4WTriplePrime_survivor_star_free s h₂ v hv hstar
  · -- inr / inr
    have hval : phi4WTriplePrime_remnantComponent o₁ = phi4WTriplePrime_remnantComponent o₂ :=
      congrArg Subtype.val heq
    have hγ : o₁.γ.1 = o₂.γ.1 := by
      by_contra hne
      exact phi4WTriplePrime_remnant_injOn o₁ o₂ hne hval
    exact congrArg Sum.inr (phi4WTriplePrime_occurrence_ext hγ)

/-- **body-607 (Step 3b) — the component forward map is surjective** (606 `quotientForest_element_cases`). -/
theorem phi4WTriplePrime_forestBlockToFun_surjective
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) :
    Function.Surjective (phi4WTriplePrime_forestBlockToFun s) := by
  intro δ
  rcases phi4WTriplePrime_quotientForest_element_cases s δ.2 with ⟨γ, hγR, hδeq⟩ | ⟨o, hδeq⟩
  · exact ⟨Sum.inl ⟨γ, hγR⟩, Subtype.ext hδeq.symm⟩
  · exact ⟨Sum.inr o, Subtype.ext hδeq.symm⟩

/-- **body-607 (Step 3b, HEADLINE) — the COMPONENT correspondence.**  A bijection between the source
`Right ⊕ Forest-occurrence` index and the quotient forest's components.  NO global inverse split-choice,
NO whole-forest-block `Equiv`. -/
noncomputable def phi4WTriplePrime_componentEquiv
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) :
    (phi4WTriplePrime_RightComponent s ⊕ Phi4WTriplePrime_ForestChoiceOccurrence s)
      ≃ {δ // δ ∈ (phi4WTriplePrime_quotientForest s).elements} :=
  Equiv.ofBijective (phi4WTriplePrime_forestBlockToFun s)
    ⟨phi4WTriplePrime_forestBlockToFun_injective s, phi4WTriplePrime_forestBlockToFun_surjective s⟩

/-- **body-607 (Step 3b) — branch-apply, `Sum.inl`.** -/
@[simp] theorem phi4WTriplePrime_componentEquiv_inl
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) (γR : phi4WTriplePrime_RightComponent s) :
    (phi4WTriplePrime_componentEquiv s (Sum.inl γR)).1 = phi4WTriplePrime_survivor s γR.2 := rfl

/-- **body-607 (Step 3b) — branch-apply, `Sum.inr`.** -/
@[simp] theorem phi4WTriplePrime_componentEquiv_inr
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G)
    (o : Phi4WTriplePrime_ForestChoiceOccurrence s) :
    (phi4WTriplePrime_componentEquiv s (Sum.inr o)).1 = phi4WTriplePrime_remnantComponent o := rfl

/-- **body-607 (Step 3b) — round-trip anchor (forward then inverse).** -/
theorem phi4WTriplePrime_componentEquiv_apply_symm
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G)
    (δ : {δ // δ ∈ (phi4WTriplePrime_quotientForest s).elements}) :
    phi4WTriplePrime_componentEquiv s ((phi4WTriplePrime_componentEquiv s).symm δ) = δ :=
  (phi4WTriplePrime_componentEquiv s).apply_symm_apply δ

/-- **body-607 (Step 3b) — round-trip anchor (inverse then forward).** -/
theorem phi4WTriplePrime_componentEquiv_symm_apply
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G)
    (x : phi4WTriplePrime_RightComponent s ⊕ Phi4WTriplePrime_ForestChoiceOccurrence s) :
    (phi4WTriplePrime_componentEquiv s).symm (phi4WTriplePrime_componentEquiv s x) = x :=
  (phi4WTriplePrime_componentEquiv s).symm_apply_apply x

/-! ## Step 4a — the two sectors + exclusive partition (Step 2 of the spec) -/

/-- **body-607 (Step 4a) — the RIGHT sector** of a quotient-forest component (a right-survivor image). -/
def phi4WTriplePrime_RightSector (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G)
    (δ : {δ // δ ∈ (phi4WTriplePrime_quotientForest s).elements}) : Prop :=
  δ.1 ∈ (phi4WTriplePrime_rightSurvivorForest s).elements

/-- **body-607 (Step 4a) — the REMNANT sector** of a quotient-forest component (a decompleted-remnant image). -/
def phi4WTriplePrime_RemnantSector (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G)
    (δ : {δ // δ ∈ (phi4WTriplePrime_quotientForest s).elements}) : Prop :=
  δ.1 ∈ (phi4WTriplePrime_remnantForest s).elements

/-- **body-607 (Step 4a) — completeness: every quotient component is in one of the two sectors.** -/
theorem phi4WTriplePrime_sector_complete (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G)
    (δ : {δ // δ ∈ (phi4WTriplePrime_quotientForest s).elements}) :
    phi4WTriplePrime_RightSector s δ ∨ phi4WTriplePrime_RemnantSector s δ := by
  have hmem : δ.1 ∈ (phi4WTriplePrime_rightSurvivorForest s).elements
      ∪ (phi4WTriplePrime_remnantForest s).elements := by
    rw [← phi4WTriplePrime_quotientForest_elements]; exact δ.2
  exact Finset.mem_union.mp hmem

/-- **body-607 (Step 4a) — mutual exclusion: no quotient component is in both sectors.**  A right survivor is
star-FREE while a decompleted remnant is star-TOUCHING, so no vertex set can be both. -/
theorem phi4WTriplePrime_sector_not_both (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G)
    (δ : {δ // δ ∈ (phi4WTriplePrime_quotientForest s).elements}) :
    ¬ (phi4WTriplePrime_RightSector s δ ∧ phi4WTriplePrime_RemnantSector s δ) := by
  rintro ⟨hR, hF⟩
  obtain ⟨γ, hγR, hδR⟩ := phi4WTriplePrime_survivor_origin s hR
  obtain ⟨o, hδF⟩ := phi4WTriplePrime_remnantForest_element_origin hF
  obtain ⟨v, hv, hstar⟩ := phi4WTriplePrime_remnant_star_touching o
  rw [← hδF] at hv
  rw [hδR] at hv
  exact phi4WTriplePrime_survivor_star_free s hγR v hv hstar

/-- **body-607 (Step 4a) — the EXCLUSIVE partition** of quotient components into the two sectors. -/
theorem phi4WTriplePrime_sector_exclusive (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G)
    (δ : {δ // δ ∈ (phi4WTriplePrime_quotientForest s).elements}) :
    (phi4WTriplePrime_RightSector s δ ∧ ¬ phi4WTriplePrime_RemnantSector s δ)
      ∨ (¬ phi4WTriplePrime_RightSector s δ ∧ phi4WTriplePrime_RemnantSector s δ) := by
  rcases phi4WTriplePrime_sector_complete s δ with hR | hF
  · exact Or.inl ⟨hR, fun hF => phi4WTriplePrime_sector_not_both s δ ⟨hR, hF⟩⟩
  · exact Or.inr ⟨fun hR => phi4WTriplePrime_sector_not_both s δ ⟨hR, hF⟩, hF⟩

/-! ## Step 4b — the star classifier (Step 4 of the spec) -/

/-- **body-607 (Step 4b) — the star-incidence classifier.**  A quotient-forest component is a "forest image"
iff one of its vertices lies on `selectedOuter`'s contract-star carrier. -/
def phi4WTriplePrime_isForestImage (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G)
    (δ : {δ // δ ∈ (phi4WTriplePrime_quotientForest s).elements}) : Prop :=
  ∃ v ∈ δ.1.vertices, v ∈ (phi4WTriplePrime_selectedOuter s).starVertices
    (phi4WTriplePrimeCanonicalSupply.starOf G (phi4WTriplePrime_selectedOuter s))

/-- **body-607 (Step 4b) — survivor images are star-FREE.** -/
theorem phi4WTriplePrime_survivor_not_forestImage
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) (γR : phi4WTriplePrime_RightComponent s) :
    ¬ phi4WTriplePrime_isForestImage s (phi4WTriplePrime_componentEquiv s (Sum.inl γR)) := by
  rintro ⟨v, hv, hstar⟩
  rw [phi4WTriplePrime_componentEquiv_inl] at hv
  exact phi4WTriplePrime_survivor_star_free s γR.2 v hv hstar

/-- **body-607 (Step 4b) — remnant images are star-TOUCHING.** -/
theorem phi4WTriplePrime_remnant_forestImage
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G)
    (o : Phi4WTriplePrime_ForestChoiceOccurrence s) :
    phi4WTriplePrime_isForestImage s (phi4WTriplePrime_componentEquiv s (Sum.inr o)) := by
  obtain ⟨v, hv, hstar⟩ := phi4WTriplePrime_remnant_star_touching o
  refine ⟨v, ?_, hstar⟩
  rw [phi4WTriplePrime_componentEquiv_inr]
  exact hv

/-- **body-607 (Step 4b) — the classifier IS the remnant sector.** -/
theorem phi4WTriplePrime_isForestImage_iff_remnantSector
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G)
    (δ : {δ // δ ∈ (phi4WTriplePrime_quotientForest s).elements}) :
    phi4WTriplePrime_isForestImage s δ ↔ phi4WTriplePrime_RemnantSector s δ := by
  constructor
  · rintro ⟨v, hv, hstar⟩
    have hmem : δ.1 ∈ (phi4WTriplePrime_rightSurvivorForest s).elements
        ∪ (phi4WTriplePrime_remnantForest s).elements := by
      rw [← phi4WTriplePrime_quotientForest_elements]; exact δ.2
    rcases Finset.mem_union.mp hmem with hR | hF
    · exfalso
      obtain ⟨γ, hγR, hδeq⟩ := phi4WTriplePrime_survivor_origin s hR
      rw [hδeq] at hv
      exact phi4WTriplePrime_survivor_star_free s hγR v hv hstar
    · exact hF
  · intro hF
    obtain ⟨o, hδeq⟩ := phi4WTriplePrime_remnantForest_element_origin hF
    obtain ⟨v, hv, hstar⟩ := phi4WTriplePrime_remnant_star_touching o
    refine ⟨v, ?_, hstar⟩
    rw [hδeq]
    exact hv

/-- **body-607 (Step 4b) — the classifier's negation IS the right sector.** -/
theorem phi4WTriplePrime_not_isForestImage_iff_rightSector
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G)
    (δ : {δ // δ ∈ (phi4WTriplePrime_quotientForest s).elements}) :
    ¬ phi4WTriplePrime_isForestImage s δ ↔ phi4WTriplePrime_RightSector s δ := by
  rw [phi4WTriplePrime_isForestImage_iff_remnantSector]
  constructor
  · intro h
    rcases phi4WTriplePrime_sector_complete s δ with hR | hF
    · exact hR
    · exact absurd hF h
  · intro hR hF
    exact phi4WTriplePrime_sector_not_both s δ ⟨hR, hF⟩

/-- **body-607 (Step 4b) — inverse-origin via the classifier: a star-touching target came from `Sum.inr`.** -/
theorem phi4WTriplePrime_componentEquiv_symm_forest
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G)
    (δ : {δ // δ ∈ (phi4WTriplePrime_quotientForest s).elements})
    (h : phi4WTriplePrime_isForestImage s δ) :
    ∃ o, (phi4WTriplePrime_componentEquiv s).symm δ = Sum.inr o := by
  set x := (phi4WTriplePrime_componentEquiv s).symm δ with hx
  have happ : phi4WTriplePrime_componentEquiv s x = δ := by
    rw [hx]; exact (phi4WTriplePrime_componentEquiv s).apply_symm_apply δ
  rcases x with γR | o
  · exfalso
    have hne := phi4WTriplePrime_survivor_not_forestImage s γR
    rw [happ] at hne
    exact hne h
  · exact ⟨o, rfl⟩

/-- **body-607 (Step 4b) — inverse-origin via the classifier: a star-free target came from `Sum.inl`.** -/
theorem phi4WTriplePrime_componentEquiv_symm_right
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G)
    (δ : {δ // δ ∈ (phi4WTriplePrime_quotientForest s).elements})
    (h : ¬ phi4WTriplePrime_isForestImage s δ) :
    ∃ γR, (phi4WTriplePrime_componentEquiv s).symm δ = Sum.inl γR := by
  set x := (phi4WTriplePrime_componentEquiv s).symm δ with hx
  have happ : phi4WTriplePrime_componentEquiv s x = δ := by
    rw [hx]; exact (phi4WTriplePrime_componentEquiv s).apply_symm_apply δ
  rcases x with γR | o
  · exact ⟨γR, rfl⟩
  · exfalso
    have hyes := phi4WTriplePrime_remnant_forestImage s o
    rw [happ] at hyes
    exact h hyes

/-! ## Step 4c — forest-level equivalence (Step 4 of the spec) -/

/-- **body-607 (Step 4c) — the source has a forest choice iff the target has a star-touching component.**
Left: a forest component gives an occurrence whose remnant is star-touching.  Right: a star-touching target
is a remnant image (`isForestImage_iff_remnantSector`), whose owner is a forest component. -/
theorem phi4WTriplePrime_source_hasForest_iff_target_starTouching
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) :
    (phi4WTriplePrime_forestComponents s).Nonempty ↔
      ∃ δ : {δ // δ ∈ (phi4WTriplePrime_quotientForest s).elements},
        phi4WTriplePrime_isForestImage s δ := by
  constructor
  · rintro ⟨γ, hγ⟩
    refine ⟨⟨phi4WTriplePrime_remnantComponent (phi4WTriplePrime_forestComponentOccurrence ⟨γ, hγ⟩),
      phi4WTriplePrime_remnantComponent_mem_quotientForest _⟩, ?_⟩
    obtain ⟨v, hv, hstar⟩ :=
      phi4WTriplePrime_remnant_star_touching (phi4WTriplePrime_forestComponentOccurrence ⟨γ, hγ⟩)
    exact ⟨v, hv, hstar⟩
  · rintro ⟨δ, hFI⟩
    rw [phi4WTriplePrime_isForestImage_iff_remnantSector] at hFI
    have hmem : δ.1 ∈ (phi4WTriplePrime_remnantForest s).elements := hFI
    rw [phi4WTriplePrime_remnantForest_elements] at hmem
    obtain ⟨γF, -, -⟩ := Finset.mem_image.mp hmem
    exact ⟨γF.1, γF.2⟩

end GaugeGeometry.QFT.Combinatorial
