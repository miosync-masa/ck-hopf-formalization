import GaugeGeometry.QFT.HopfAlgebra.Phi4WTriplePrimeRemnantForest

/-!
# QFT-R1-body-606 — quotient forest assembly + W‴ membership

Body-603 built the right-survivor forest and body-605 the remnant forest, both on the quotient ambient
`Q := phi4WTriplePrime_selectedOuterContractGraph s`.  This body UNIONS them into `quotientForest` and
lands it back in the fifth-axis index `phi4WTriplePrimeIndex Q` — so the quotient of a W‴ split choice is
itself a live W‴ forest.

## What closes cleanly vs. the one genuine residual

* **cross-disjointness** — a right survivor `γ_R` (right component, `Sum.inl false`) and a remnant
  `remnantComponent o` (forest owner `γ_F`, `Sum.inr B`) have different owners, so `s.outer`'s pairwise
  disjointness separates the `γ_F`-vertices, and the promoted global stars of the remnant are fresh
  (outside `G`) while `γ_R ⊆ G`.
* **honest nonemptiness** — proved ONLY for the WHOLE `quotientForest` from `choice_filtered ≠ PL`.  We do
  NOT claim `rightSurvivorForest`/`remnantForest` nonempty separately (a mixed choice may empty either
  side; the union is always nonempty because some component is right or forest).
* **remnant positive internal edges** — `remnant.internalEdges = B.1.complementEdges.map r`, whose card is
  `B.1.complementEdges.card > 0` from the inner live-W‴ owner's properness (NO CD / E-supply route).
* **`0 < complementEdges.card`** — DERIVED internally (bodies 500/501 input-residual route, re-keyed clean):
  `quotientForest.internalEdges ≤ R.map r` where `R := s.outer.internalEdges − selectedOuter.internalEdges`,
  and `card R < card A.complementEdges = card Q.internalEdges` because `s.outer` (a W‴ member, hence a proper
  forest) has a positive complement in `G`.  So `_isProperForest` and `_mem` take ONLY `{G} (s)`.

## HALT compliance

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only); ZERO forbidden divergence classes in ANY
declaration's type (the survivor-embed stack / `resolvedComponentGen` / polluted supply lemmas are NOT
consumed — the ambient-support / edge-&-leg-id-uniqueness facts on `Q` are RE-DERIVED clean from the
`retargetEdge`/`retargetLeg` id-preservation primitives).  No `sorry` / `admit` / `native_decide`.  No
star separator / sector / forest-block / alpha / coassoc; no strict star equality.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

open ResolvedFeynmanSubgraph

variable {G : ResolvedFeynmanGraph}

set_option maxHeartbeats 3200000

/-- The concrete φ⁴ divergence measure family, registered file-locally (providable instance, NO forbidden
class). -/
noncomputable local instance phi4Inst606 : (H : FeynmanGraph) → DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

/-! ## Step 1 — survivor origin + cross-disjointness -/

/-- **body-606 (Step 1) — right-survivor origin recovery.**  Every right-survivor-forest element is
`survivor γ hγR` for a concrete right component `γ` (mirror of body-605 `remnantForest_element_origin`). -/
theorem phi4WTriplePrime_survivor_origin (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G)
    {δ : ResolvedFeynmanSubgraph (phi4WTriplePrime_selectedOuterContractGraph s)}
    (hδ : δ ∈ (phi4WTriplePrime_rightSurvivorForest s).elements) :
    ∃ (γ : ResolvedFeynmanSubgraph G) (hγR : phi4WTriplePrime_isRightComponent s γ),
      δ = phi4WTriplePrime_survivor s hγR := by
  rw [phi4WTriplePrime_rightSurvivorForest_elements] at hδ
  obtain ⟨γR, -, rfl⟩ := Finset.mem_image.mp hδ
  exact ⟨γR.1, ((phi4WTriplePrime_mem_rightComponents s).mp γR.2).2, rfl⟩

/-- **body-606 (Step 1) — cross-disjointness of survivors vs. remnants.**  A right survivor `γ_R` and a
remnant `remnantComponent o` (owner `γ_F = o.γ.1`) have different owners, so `s.outer.pairwiseDisjoint`
separates the `γ_F`-vertices from `γ_R`; the remnant's promoted global stars are fresh (outside `G`) while
`γ_R.vertices ⊆ G.vertices`. -/
theorem phi4WTriplePrime_quotient_crossDisjoint (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) :
    ∀ γ ∈ (phi4WTriplePrime_rightSurvivorForest s).elements,
      ∀ δ ∈ (phi4WTriplePrime_remnantForest s).elements, γ ≠ δ → γ.Disjoint δ := by
  intro γ hγ δ hδ _hne
  obtain ⟨γR, hγR, rfl⟩ := phi4WTriplePrime_survivor_origin s hγ
  obtain ⟨o, rfl⟩ := phi4WTriplePrime_remnantForest_element_origin hδ
  have hpfSel := phi4WTriplePrime_selectedOuter_isProperForest s
  have hneOwner : γR ≠ o.γ.1 := by
    intro heq
    subst heq
    exact absurd (hγR.choose_spec.symm.trans o.hchoice) (by simp)
  have hdd : o.γ.1.Disjoint γR :=
    s.outer.pairwiseDisjoint o.γ.2 hγR.choose (fun h => hneOwner h.symm)
  show _root_.Disjoint (phi4WTriplePrime_survivor s hγR).vertices
    (phi4WTriplePrime_remnantComponent o).vertices
  rw [phi4WTriplePrime_survivor_vertices, Finset.disjoint_left]
  intro v hvγR hvrem
  rcases phi4WTriplePrime_remnant_vertex_mem_cases o hvrem with hvγF | ⟨δ0, hδ0, hveq⟩
  · exact Finset.disjoint_left.mp hdd hvγF hvγR
  · exact phi4WTriplePrime_gen_star_not_mem (phi4WTriplePrime_selectedOuter s) hpfSel
      (phi4WTriplePrime_remnant_promoted_mem o hδ0) (hveq ▸ γR.vertices_subset hvγR)

/-! ## Step 2 — quotientForest + honest nonemptiness -/

/-- **body-606 (Step 2) — the quotient forest** in the quotient ambient `Q`.  The union of the
right-survivor forest and the remnant forest. -/
noncomputable def phi4WTriplePrime_quotientForest
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) :
    @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily
      (phi4WTriplePrime_selectedOuterContractGraph s) :=
  (phi4WTriplePrime_rightSurvivorForest s).union (phi4WTriplePrime_remnantForest s)
    (phi4WTriplePrime_quotient_crossDisjoint s)

@[simp] theorem phi4WTriplePrime_quotientForest_elements
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) :
    (phi4WTriplePrime_quotientForest s).elements
      = (phi4WTriplePrime_rightSurvivorForest s).elements
        ∪ (phi4WTriplePrime_remnantForest s).elements := by
  unfold phi4WTriplePrime_quotientForest
  ext c
  simp only [ResolvedAdmissibleSubgraph.union_elements, Finset.mem_union]

/-- **body-606 (Step 2) — element origin.**  Every quotient-forest element is either a survivor of a
concrete right component OR a remnant of a concrete forest-choice occurrence. -/
theorem phi4WTriplePrime_quotientForest_element_cases
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G)
    {δ : ResolvedFeynmanSubgraph (phi4WTriplePrime_selectedOuterContractGraph s)}
    (hδ : δ ∈ (phi4WTriplePrime_quotientForest s).elements) :
    (∃ (γ : ResolvedFeynmanSubgraph G) (hγR : phi4WTriplePrime_isRightComponent s γ),
        δ = phi4WTriplePrime_survivor s hγR)
      ∨ (∃ o : Phi4WTriplePrime_ForestChoiceOccurrence s,
        δ = phi4WTriplePrime_remnantComponent o) := by
  rw [phi4WTriplePrime_quotientForest_elements, Finset.mem_union] at hδ
  rcases hδ with h | h
  · exact Or.inl (phi4WTriplePrime_survivor_origin s h)
  · exact Or.inr (phi4WTriplePrime_remnantForest_element_origin h)

/-- **body-606 (Step 2) — honest nonemptiness of the quotient forest.**  From `choice_filtered ≠ PL`
(the all-left primitive): some component's choice is not `Sum.inl true`; a `Sum.inl false` (right) yields
a survivor in the union, a `Sum.inr B` (forest) yields a remnant in the union.  Proved ONLY for the whole
union — never for `rightSurvivorForest` / `remnantForest` separately. -/
theorem phi4WTriplePrime_quotientForest_isNonempty
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) :
    (phi4WTriplePrime_quotientForest s).IsNonempty := by
  have hfilt := (mem_phi4EdgeCompleteForestChoiceCarrier s.outer).mp s.choice_filtered
  have hNePL : s.choice ≠ phi4EdgeCompleteChoicePL s.outer := hfilt.2.2
  have h1 : ∃ a, s.choice a ≠ phi4EdgeCompleteChoicePL s.outer a := by
    by_contra hcon
    exact hNePL (funext (fun a => by by_contra hne; exact hcon ⟨a, hne⟩))
  obtain ⟨a, ha⟩ := h1
  have h2 : ∃ hatt, s.choice a hatt ≠ phi4EdgeCompleteChoicePL s.outer a hatt := by
    by_contra hcon
    exact ha (funext (fun hatt => by by_contra hne; exact hcon ⟨hatt, hne⟩))
  obtain ⟨hatt, ha2⟩ := h2
  show (phi4WTriplePrime_quotientForest s).elements.Nonempty
  rw [phi4WTriplePrime_quotientForest_elements]
  rcases hcase : s.choice a hatt with b | B
  · rcases b with _ | _
    · -- Sum.inl false → a.1 is a RIGHT component → survivor in the left of the union
      have haR : phi4WTriplePrime_isRightComponent s a.1 := ⟨a.2, hcase⟩
      have hmemRC : a.1 ∈ phi4WTriplePrime_rightComponents s :=
        (phi4WTriplePrime_mem_rightComponents s).mpr ⟨a.2, haR⟩
      refine ⟨phi4WTriplePrime_survivor s
        ((phi4WTriplePrime_mem_rightComponents s).mp hmemRC).2, ?_⟩
      refine Finset.mem_union_left _ ?_
      rw [phi4WTriplePrime_rightSurvivorForest_elements]
      exact Finset.mem_image.mpr ⟨⟨a.1, hmemRC⟩, Finset.mem_attach _ _, rfl⟩
    · -- Sum.inl true → contradicts `ha2` (PL a hatt = Sum.inl true)
      exact absurd hcase ha2
  · -- Sum.inr B → a.1 is a FOREST component → remnant in the right of the union
    have haF : phi4WTriplePrime_isForestComponent s a.1 := ⟨a.2, B, hcase⟩
    have hmemFC : a.1 ∈ phi4WTriplePrime_forestComponents s :=
      (phi4WTriplePrime_mem_forestComponents s).mpr ⟨a.2, haF⟩
    refine ⟨phi4WTriplePrime_remnantComponent
      (phi4WTriplePrime_forestComponentOccurrence ⟨a.1, hmemFC⟩), ?_⟩
    refine Finset.mem_union_right _ ?_
    rw [phi4WTriplePrime_remnantForest_elements]
    exact Finset.mem_image.mpr ⟨⟨a.1, hmemFC⟩, Finset.mem_attach _ _, rfl⟩

/-! ## Step 2b — the input-residual bound (bodies 500/501 route, re-keyed clean) — CLOSES the complement
positivity, so no external hypothesis is needed.  Let `A := selectedOuter s`, `r := A.retargetEdge starOf`,
`R := s.outer.internalEdges - A.internalEdges` (the input residual).  We prove
`quotientForest.internalEdges ≤ R.map r`, and `card R < card A.complementEdges = card Q.internalEdges`, so
the quotient complement is strictly positive. -/

/-- **body-606 (Step 2b) — the owner count lemma** (multiplicity-safe; body-432 re-keyed clean).  In a
pairwise-disjoint forest, an edge's multiplicity in the whole forest equals its multiplicity in the single
component that carries it. -/
theorem phi4WTriplePrime_ownerCount {H : ResolvedFeynmanGraph}
    {Raw : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily H}
    {γ : ResolvedFeynmanSubgraph H} (hγ : γ ∈ Raw.elements)
    {e : ResolvedFeynmanEdge} (he : e ∈ γ.internalEdges) :
    Multiset.count e Raw.internalEdges = Multiset.count e γ.internalEdges := by
  show Multiset.count e (Raw.elements.sum (fun c => c.internalEdges)) = _
  rw [Multiset.count_sum']
  refine Finset.sum_eq_single γ (fun c hc hcγ => ?_) (fun hnγ => absurd hγ hnγ)
  by_contra h
  have hec : e ∈ c.internalEdges := Multiset.count_pos.mp (Nat.pos_of_ne_zero h)
  exact Finset.disjoint_left.mp (Raw.pairwiseDisjoint hγ hc hcγ.symm)
    (γ.edges_supported e he).1 (c.edges_supported e hec).1

/-- **body-606 (Step 2b) — selectedOuter's internal edges are inside `s.outer`'s** (each component lands in
an `s.outer` component; mirror of body-602's `hcompLe`). -/
theorem phi4WTriplePrime_selectedOuter_internalEdges_le_outer
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) :
    (phi4WTriplePrime_selectedOuter s).internalEdges ≤ s.outer.internalEdges := by
  refine phi4WTriplePrime_internalEdges_le_of_components_le (phi4WTriplePrime_selectedOuter s)
    (fun c hc => ?_)
  rcases phi4WTriplePrime_selectedOuter_component_origin s hc with ⟨hcmem, -⟩ | hP
  · exact Finset.single_le_sum (f := fun x : ResolvedFeynmanSubgraph G => x.internalEdges)
      (fun i _ => Multiset.zero_le _) hcmem
  · obtain ⟨γ, hγ, B, -, δ, hδ, rfl⟩ := hP
    have h1 : (rootRelativeInner γ δ).internalEdges ≤ γ.internalEdges := by
      show δ.internalEdges ≤ γ.internalEdges
      exact δ.internalEdges_le
    exact le_trans h1 (Finset.single_le_sum (f := fun x : ResolvedFeynmanSubgraph G => x.internalEdges)
      (fun i _ => Multiset.zero_le _) hγ)

/-- **body-606 (Step 2b) — `s.outer`'s internal edges are inside the ambient** (aggregate of the subgraph
bound; re-derived clean, NOT via the class-binder-carrying `internalEdges_le`). -/
theorem phi4WTriplePrime_outer_internalEdges_le
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) :
    s.outer.internalEdges ≤ G.internalEdges :=
  phi4WTriplePrime_internalEdges_le_of_components_le s.outer (fun c _ => c.internalEdges_le)

/-- **body-606 (Step 2b) — the selected-outer owner bound** (body-460's `selectedOuter_count_le_occurrence`
re-keyed clean): a `γ`-internal edge occurs no more often in `selectedOuter` than in the occurrence forest
`B`. -/
theorem phi4WTriplePrime_selectedOuter_count_le_occurrence
    {s : Phi4EdgeCompleteFilteredCoassocSplitChoice G}
    (o : Phi4WTriplePrime_ForestChoiceOccurrence s) {e : ResolvedFeynmanEdge}
    (heγ : e ∈ o.γ.1.internalEdges) :
    Multiset.count e (phi4WTriplePrime_selectedOuter s).internalEdges
      ≤ Multiset.count e o.B.1.internalEdges := by
  by_cases hcS : Multiset.count e (phi4WTriplePrime_selectedOuter s).internalEdges = 0
  · rw [hcS]; exact Nat.zero_le _
  · have heS : e ∈ (phi4WTriplePrime_selectedOuter s).internalEdges :=
      Multiset.count_pos.mp (Nat.pos_of_ne_zero hcS)
    obtain ⟨σ, hσ, heσ⟩ := phi4WTriplePrime_mem_selectedOuter_internalEdges o heS
    have howner : Multiset.count e (phi4WTriplePrime_selectedOuter s).internalEdges
        = Multiset.count e σ.internalEdges := phi4WTriplePrime_ownerCount hσ heσ
    rcases phi4WTriplePrime_selectedOuter_component_origin s hσ with ⟨hσmem, hleftσ⟩ | hP
    · exfalso
      by_cases hσγ : σ = o.γ.1
      · obtain ⟨hh, hσtrue⟩ := hleftσ
        subst hσγ
        exact absurd (hσtrue.symm.trans o.hchoice) (by simp)
      · exact Finset.disjoint_left.mp (s.outer.pairwiseDisjoint hσmem o.γ.2 hσγ)
          (σ.edges_supported e heσ).1 (o.γ.1.edges_supported e heγ).1
    · obtain ⟨γ', hγ', B', hchoice', δ, hδ, rfl⟩ := hP
      have hσγ' : γ' = o.γ.1 := by
        by_contra hne
        exact Finset.disjoint_left.mp (s.outer.pairwiseDisjoint hγ' o.γ.2 hne)
          (phi4WTriplePrime_rootRelativeInner_vertices_subset γ' δ
            ((rootRelativeInner γ' δ).edges_supported e heσ).1)
          (o.γ.1.edges_supported e heγ).1
      subst hσγ'
      have hBeq : B' = o.B := Sum.inr.inj (hchoice'.symm.trans o.hchoice)
      subst hBeq
      rw [howner, rootRelativeInner_internalEdges]
      exact Multiset.count_le_of_le e
        (Finset.single_le_sum (fun i _ => Multiset.zero_le _) hδ)

/-- **body-606 (Step 2b) — a right component + selectedOuter fit disjointly inside `s.outer`.** -/
theorem phi4WTriplePrime_rightComponent_add_selectedOuter_le_outer
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) {γ : ResolvedFeynmanSubgraph G}
    (hγR : phi4WTriplePrime_isRightComponent s γ) :
    γ.internalEdges + (phi4WTriplePrime_selectedOuter s).internalEdges ≤ s.outer.internalEdges := by
  rw [Multiset.le_iff_count]
  intro e
  rw [Multiset.count_add]
  by_cases hcr : e ∈ γ.internalEdges
  · have hown : Multiset.count e s.outer.internalEdges = Multiset.count e γ.internalEdges :=
      phi4WTriplePrime_ownerCount hγR.choose hcr
    have hdisj : Disjoint γ.vertices (phi4WTriplePrime_selectedOuter s).vertices :=
      phi4WTriplePrime_rightComponent_disjoint_selectedOuter s hγR
    have hS0 : Multiset.count e (phi4WTriplePrime_selectedOuter s).internalEdges = 0 := by
      rw [Multiset.count_eq_zero]
      intro heS
      exact Finset.disjoint_left.mp hdisj (γ.edges_supported e hcr).1
        (phi4WTriplePrime_source_mem_vertices (phi4WTriplePrime_selectedOuter s) heS)
    rw [hown, hS0]
    omega
  · rw [Multiset.count_eq_zero.mpr hcr, Nat.zero_add]
    exact Multiset.count_le_of_le e (phi4WTriplePrime_selectedOuter_internalEdges_le_outer s)

/-- **body-606 (Step 2b) — an occurrence's inner complement + selectedOuter fit inside `s.outer`.** -/
theorem phi4WTriplePrime_occurrence_add_selectedOuter_le_outer
    {s : Phi4EdgeCompleteFilteredCoassocSplitChoice G}
    (o : Phi4WTriplePrime_ForestChoiceOccurrence s) :
    o.B.1.complementEdges + (phi4WTriplePrime_selectedOuter s).internalEdges
      ≤ s.outer.internalEdges := by
  rw [Multiset.le_iff_count]
  intro e
  rw [Multiset.count_add]
  by_cases hcB : e ∈ o.B.1.complementEdges
  · have heγ : e ∈ o.γ.1.internalEdges := by
      have h : e ∈ o.γ.1.boundaryCompletedResolvedGraph.internalEdges :=
        Multiset.mem_of_le (Multiset.sub_le_self _ _) hcB
      rwa [boundaryCompletedResolvedGraph_internalEdges] at h
    have hSB := phi4WTriplePrime_selectedOuter_count_le_occurrence o heγ
    have hcomp : Multiset.count e o.B.1.complementEdges
        = Multiset.count e o.γ.1.internalEdges - Multiset.count e o.B.1.internalEdges := by
      show Multiset.count e (o.γ.1.boundaryCompletedResolvedGraph.internalEdges
        - o.B.1.internalEdges) = _
      rw [Multiset.count_sub, boundaryCompletedResolvedGraph_internalEdges]
    have hBγ : Multiset.count e o.B.1.internalEdges ≤ Multiset.count e o.γ.1.internalEdges := by
      have h := Multiset.count_le_of_le e
        (phi4WTriplePrime_internalEdges_le_of_components_le o.B.1 (fun c _ => c.internalEdges_le))
      rwa [boundaryCompletedResolvedGraph_internalEdges] at h
    have hown : Multiset.count e s.outer.internalEdges = Multiset.count e o.γ.1.internalEdges :=
      phi4WTriplePrime_ownerCount o.γ.2 heγ
    rw [hcomp, hown]
    omega
  · rw [Multiset.count_eq_zero.mpr hcB, Nat.zero_add]
    exact Multiset.count_le_of_le e (phi4WTriplePrime_selectedOuter_internalEdges_le_outer s)

/-- **body-606 (Step 2b) — the survivor's residual bound** `survivor.internalEdges ≤ R.map r`. -/
theorem phi4WTriplePrime_survivor_internalEdges_le_residual
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) {γ : ResolvedFeynmanSubgraph G}
    (hγR : phi4WTriplePrime_isRightComponent s γ) :
    (phi4WTriplePrime_survivor s hγR).internalEdges
      ≤ (s.outer.internalEdges - (phi4WTriplePrime_selectedOuter s).internalEdges).map
          ((phi4WTriplePrime_selectedOuter s).retargetEdge
            (phi4WTriplePrimeCanonicalSupply.starOf G (phi4WTriplePrime_selectedOuter s))) := by
  have hle_R : γ.internalEdges
      ≤ s.outer.internalEdges - (phi4WTriplePrime_selectedOuter s).internalEdges :=
    (le_tsub_iff_right (phi4WTriplePrime_selectedOuter_internalEdges_le_outer s)).2
      (phi4WTriplePrime_rightComponent_add_selectedOuter_le_outer s hγR)
  have hdisj : Disjoint γ.vertices (phi4WTriplePrime_selectedOuter s).vertices :=
    phi4WTriplePrime_rightComponent_disjoint_selectedOuter s hγR
  have hmapid : γ.internalEdges.map ((phi4WTriplePrime_selectedOuter s).retargetEdge
      (phi4WTriplePrimeCanonicalSupply.starOf G (phi4WTriplePrime_selectedOuter s)))
      = γ.internalEdges := by
    conv_rhs => rw [← Multiset.map_id γ.internalEdges]
    apply Multiset.map_congr rfl
    intro e he
    obtain ⟨hs, ht⟩ := γ.edges_supported e he
    unfold ResolvedAdmissibleSubgraph.retargetEdge ResolvedFeynmanEdge.retarget
    rw [(phi4WTriplePrime_selectedOuter s).retargetVertex_of_not_mem _
        (Finset.disjoint_left.mp hdisj hs),
      (phi4WTriplePrime_selectedOuter s).retargetVertex_of_not_mem _
        (Finset.disjoint_left.mp hdisj ht)]
    rfl
  rw [phi4WTriplePrime_survivor_internalEdges, ← hmapid]
  exact Multiset.map_le_map hle_R

/-- **body-606 (Step 2b) — the remnant's residual bound** `remnant.internalEdges ≤ R.map r`. -/
theorem phi4WTriplePrime_remnant_internalEdges_le_residual
    {s : Phi4EdgeCompleteFilteredCoassocSplitChoice G}
    (o : Phi4WTriplePrime_ForestChoiceOccurrence s) :
    (phi4WTriplePrime_remnantComponent o).internalEdges
      ≤ (s.outer.internalEdges - (phi4WTriplePrime_selectedOuter s).internalEdges).map
          ((phi4WTriplePrime_selectedOuter s).retargetEdge
            (phi4WTriplePrimeCanonicalSupply.starOf G (phi4WTriplePrime_selectedOuter s))) := by
  rw [phi4WTriplePrime_remnantComponent_internalEdges, phi4WTriplePrime_remnant_internalEdges_eq]
  refine Multiset.map_le_map ?_
  exact (le_tsub_iff_right (phi4WTriplePrime_selectedOuter_internalEdges_le_outer s)).2
    (phi4WTriplePrime_occurrence_add_selectedOuter_le_outer o)

/-- **body-606 (Step 2b) — the whole quotient forest is inside the input residual** `R.map r`. -/
theorem phi4WTriplePrime_quotientForest_internalEdges_le_residual
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) :
    (phi4WTriplePrime_quotientForest s).internalEdges
      ≤ (s.outer.internalEdges - (phi4WTriplePrime_selectedOuter s).internalEdges).map
          ((phi4WTriplePrime_selectedOuter s).retargetEdge
            (phi4WTriplePrimeCanonicalSupply.starOf G (phi4WTriplePrime_selectedOuter s))) := by
  refine phi4WTriplePrime_internalEdges_le_of_components_le (phi4WTriplePrime_quotientForest s)
    (fun c hc => ?_)
  rcases phi4WTriplePrime_quotientForest_element_cases s hc with ⟨γ, hγR, rfl⟩ | ⟨o, rfl⟩
  · exact phi4WTriplePrime_survivor_internalEdges_le_residual s hγR
  · exact phi4WTriplePrime_remnant_internalEdges_le_residual o

/-- **body-606 (Step 2b, HEADLINE) — the quotient complement is strictly positive.**  The input residual
`R = s.outer.internalEdges − selectedOuter.internalEdges` has strictly fewer edges than
`A.complementEdges = G.internalEdges − selectedOuter.internalEdges` (because `s.outer` has a positive
complement in `G`), and `quotientForest.internalEdges ≤ R.map r ≤ Q.internalEdges`, so
`0 < Q.complementEdges.card`.  NO external hypothesis. -/
theorem phi4WTriplePrime_quotient_complement_pos
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) :
    0 < (phi4WTriplePrime_quotientForest s).complementEdges.card := by
  have houterProper : s.outer.IsProperForest :=
    ((mem_phi4WTriplePrimeIndex G s.outer).mp s.outer_mem).2.2.2.2.1
  have hSelLe : (phi4WTriplePrime_selectedOuter s).internalEdges ≤ s.outer.internalEdges :=
    phi4WTriplePrime_selectedOuter_internalEdges_le_outer s
  have hOutLeG : s.outer.internalEdges ≤ G.internalEdges := phi4WTriplePrime_outer_internalEdges_le s
  have hSelLeG : (phi4WTriplePrime_selectedOuter s).internalEdges ≤ G.internalEdges :=
    le_trans hSelLe hOutLeG
  -- qF.internalEdges ≤ Q.internalEdges
  have hqFQ : (phi4WTriplePrime_quotientForest s).internalEdges
      ≤ (phi4WTriplePrime_selectedOuterContractGraph s).internalEdges :=
    phi4WTriplePrime_internalEdges_le_of_components_le (phi4WTriplePrime_quotientForest s)
      (fun c _ => c.internalEdges_le)
  -- card(Q.internalEdges) = card(A.complementEdges) = card G.I - card selectedOuter.I
  have hQcard : (phi4WTriplePrime_selectedOuterContractGraph s).internalEdges.card
      = G.internalEdges.card - (phi4WTriplePrime_selectedOuter s).internalEdges.card := by
    rw [phi4WTriplePrime_selectedOuterContractGraph,
      ResolvedAdmissibleSubgraph.contractWithStars_internalEdges, Multiset.card_map]
    show ((G.internalEdges - (phi4WTriplePrime_selectedOuter s).internalEdges)).card = _
    rw [Multiset.card_sub hSelLeG]
  -- card(qF.internalEdges) ≤ card(R) = card s.outer.I - card selectedOuter.I
  have hqFcardle : (phi4WTriplePrime_quotientForest s).internalEdges.card
      ≤ s.outer.internalEdges.card - (phi4WTriplePrime_selectedOuter s).internalEdges.card := by
    have h1 := Multiset.card_le_card (phi4WTriplePrime_quotientForest_internalEdges_le_residual s)
    rwa [Multiset.card_map, Multiset.card_sub hSelLe] at h1
  -- s.outer has positive complement: card s.outer.I < card G.I
  have hOutLtG : s.outer.internalEdges.card < G.internalEdges.card := by
    have hpos : 0 < s.outer.complementEdges.card :=
      ResolvedAdmissibleSubgraph.complementEdges_card_pos_of_isProperForest houterProper
    have : s.outer.complementEdges.card
        = G.internalEdges.card - s.outer.internalEdges.card := by
      show (G.internalEdges - s.outer.internalEdges).card = _
      rw [Multiset.card_sub hOutLeG]
    omega
  -- selectedOuter.I ≤ s.outer.I ≤ G.I gives the card ordering; conclude via card_sub
  have hcardSel : (phi4WTriplePrime_selectedOuter s).internalEdges.card ≤ s.outer.internalEdges.card :=
    Multiset.card_le_card hSelLe
  have hcardOut : s.outer.internalEdges.card ≤ G.internalEdges.card := Multiset.card_le_card hOutLeG
  show 0 < ((phi4WTriplePrime_selectedOuterContractGraph s).internalEdges
    - (phi4WTriplePrime_quotientForest s).internalEdges).card
  rw [Multiset.card_sub hqFQ, hQcard]
  omega

/-! ## Step 3 — IsProperForest (complement positivity now derived internally — no hypothesis) -/

/-- **body-606 (Step 3) — the quotient forest is a proper forest.**  The complement positivity is DERIVED
(body-500/501 input-residual route), so this takes only `{G} (s)`. -/
theorem phi4WTriplePrime_quotientForest_isProperForest
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) :
    @ResolvedAdmissibleSubgraph.IsProperForest phi4DivergenceMeasureFamily
      (phi4WTriplePrime_selectedOuterContractGraph s) (phi4WTriplePrime_quotientForest s) := by
  have houterMem := (mem_phi4WTriplePrimeIndex G s.outer).mp s.outer_mem
  have houterProper : s.outer.IsProperForest := houterMem.2.2.2.2.1
  -- HasNonemptyComponents
  have hNC : (phi4WTriplePrime_quotientForest s).HasNonemptyComponents := by
    intro c hc
    rcases phi4WTriplePrime_quotientForest_element_cases s hc with ⟨γ, hγR, rfl⟩ | ⟨o, rfl⟩
    · show 0 < (phi4WTriplePrime_survivor s hγR).vertices.card
      rw [phi4WTriplePrime_survivor_vertices]
      exact houterProper.2.1 γ hγR.choose
    · exact phi4WTriplePrime_remnant_isNonempty o
  -- HasPositiveInternalEdgesComponents
  have hPC : (phi4WTriplePrime_quotientForest s).HasPositiveInternalEdgesComponents := by
    intro c hc
    rcases phi4WTriplePrime_quotientForest_element_cases s hc with ⟨γ, hγR, rfl⟩ | ⟨o, rfl⟩
    · rw [phi4WTriplePrime_survivor_internalEdges]
      exact houterProper.2.2.2.1 γ hγR.choose
    · rw [phi4WTriplePrime_remnantComponent_internalEdges, phi4WTriplePrime_remnant_internalEdges_eq,
        Multiset.card_map]
      exact ResolvedAdmissibleSubgraph.complementEdges_card_pos_of_isProperForest
        (phi4WTriplePrime_occ_B_isProperForest o)
  -- 0 < internalEdges.card
  have hIE : 0 < (phi4WTriplePrime_quotientForest s).internalEdges.card := by
    obtain ⟨η, hη⟩ := phi4WTriplePrime_quotientForest_isNonempty s
    have hηle : η.internalEdges ≤ (phi4WTriplePrime_quotientForest s).internalEdges :=
      Finset.single_le_sum (f := fun x : ResolvedFeynmanSubgraph
          (phi4WTriplePrime_selectedOuterContractGraph s) => x.internalEdges)
        (fun i _ => Multiset.zero_le _) hη
    exact lt_of_lt_of_le (hPC η hη) (Multiset.card_le_card hηle)
  exact ⟨phi4WTriplePrime_quotientForest_isNonempty s, hNC, hIE, hPC,
    phi4WTriplePrime_quotient_complement_pos s⟩

/-! ## Step 4 — sixth/seventh axes + ambient gates on `Q` -/

/-- **body-606 (Step 4, sixth axis) — the quotient forest is externally-leg saturated on `Q`.** -/
theorem phi4WTriplePrime_quotientForest_forestSaturated
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) :
    ResolvedForestExternalLegSaturated (phi4WTriplePrime_quotientForest s) := by
  intro δ hδ
  rcases phi4WTriplePrime_quotientForest_element_cases s hδ with ⟨γ, hγR, rfl⟩ | ⟨o, rfl⟩
  · exact phi4WTriplePrime_survivor_saturated s hγR
  · exact phi4WTriplePrime_remnant_saturated o

/-- **body-606 (Step 4, seventh axis) — the quotient forest is internal-edge complete on `Q`.** -/
theorem phi4WTriplePrime_quotientForest_forestEdgeComplete
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) :
    ResolvedForestInternalEdgeComplete phi4DivergenceMeasureFamily
      (phi4WTriplePrime_quotientForest s) := by
  intro γ hγ
  rcases phi4WTriplePrime_quotientForest_element_cases s hγ with ⟨g, hγR, rfl⟩ | ⟨o, rfl⟩
  · exact phi4WTriplePrime_survivor_edgeComplete s hγR
  · exact phi4WTriplePrime_remnant_edgeComplete o

/-- **body-606 (Step 4) — `Q` is ambient-supported** (edges + legs), re-derived clean from `G`'s ambient
support through the `contractWithStars` retarget landing (NO polluted supply lemma consumed). -/
theorem phi4WTriplePrime_Q_ambientSupported
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) :
    ResolvedAmbientSupported (phi4WTriplePrime_selectedOuterContractGraph s) := by
  have hG : ResolvedAmbientSupported G := ((mem_phi4WTriplePrimeIndex G s.outer).mp s.outer_mem).1
  refine ⟨?_, ?_⟩
  · intro e' he'
    rw [phi4WTriplePrime_selectedOuterContractGraph,
      ResolvedAdmissibleSubgraph.contractWithStars_internalEdges] at he'
    obtain ⟨e, he, rfl⟩ := Multiset.mem_map.mp he'
    have heG : e ∈ G.internalEdges := Multiset.mem_of_le (Multiset.sub_le_self _ _) he
    obtain ⟨hs, ht⟩ := hG.1 e heG
    refine ⟨?_, ?_⟩
    · show (phi4WTriplePrime_selectedOuter s).retargetVertex _ e.source
        ∈ (phi4WTriplePrime_selectedOuterContractGraph s).vertices
      rw [phi4WTriplePrime_selectedOuterContractGraph]
      exact (phi4WTriplePrime_selectedOuter s).retargetVertex_mem_contractWithStars_vertices _ hs
    · show (phi4WTriplePrime_selectedOuter s).retargetVertex _ e.target
        ∈ (phi4WTriplePrime_selectedOuterContractGraph s).vertices
      rw [phi4WTriplePrime_selectedOuterContractGraph]
      exact (phi4WTriplePrime_selectedOuter s).retargetVertex_mem_contractWithStars_vertices _ ht
  · intro ℓ' hℓ'
    rw [phi4WTriplePrime_selectedOuterContractGraph,
      ResolvedAdmissibleSubgraph.contractWithStars_externalLegs] at hℓ'
    obtain ⟨ℓ, hℓ, rfl⟩ := Multiset.mem_map.mp hℓ'
    show (phi4WTriplePrime_selectedOuter s).retargetVertex _ ℓ.attachedTo
      ∈ (phi4WTriplePrime_selectedOuterContractGraph s).vertices
    rw [phi4WTriplePrime_selectedOuterContractGraph]
    exact (phi4WTriplePrime_selectedOuter s).retargetVertex_mem_contractWithStars_vertices _
      (hG.2 ℓ hℓ)

/-- **body-606 (Step 4) — `Q` has unique edge ids**, re-derived clean: `retargetEdge` keeps `edgeId`, so
equal ids on the retargeted complement pull back through `G.EdgeIdsUnique`. -/
theorem phi4WTriplePrime_Q_edgeIdsUnique
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) :
    (phi4WTriplePrime_selectedOuterContractGraph s).EdgeIdsUnique := by
  have hGId : G.EdgeIdsUnique := ((mem_phi4WTriplePrimeIndex G s.outer).mp s.outer_mem).2.2.1
  intro e₁' he₁' e₂' he₂' hid
  rw [phi4WTriplePrime_selectedOuterContractGraph,
    ResolvedAdmissibleSubgraph.contractWithStars_internalEdges] at he₁' he₂'
  obtain ⟨e₁, he₁, rfl⟩ := Multiset.mem_map.mp he₁'
  obtain ⟨e₂, he₂, rfl⟩ := Multiset.mem_map.mp he₂'
  have he₁G : e₁ ∈ G.internalEdges := Multiset.mem_of_le (Multiset.sub_le_self _ _) he₁
  have he₂G : e₂ ∈ G.internalEdges := Multiset.mem_of_le (Multiset.sub_le_self _ _) he₂
  have hidE : e₁.edgeId = e₂.edgeId := by
    simpa only [ResolvedAdmissibleSubgraph.retargetEdge, ResolvedFeynmanEdge.retarget_edgeId] using hid
  have hee : e₁ = e₂ := hGId e₁ he₁G e₂ he₂G hidE
  rw [hee]

/-- **body-606 (Step 4) — `Q` has unique leg ids**, re-derived clean via `retargetExternalLeg`'s
`legId`-preservation and `G.LegIdsUnique`. -/
theorem phi4WTriplePrime_Q_legIdsUnique
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) :
    (phi4WTriplePrime_selectedOuterContractGraph s).LegIdsUnique := by
  have hGId : G.LegIdsUnique := ((mem_phi4WTriplePrimeIndex G s.outer).mp s.outer_mem).2.2.2.1
  intro ℓ₁' hℓ₁' ℓ₂' hℓ₂' hid
  rw [phi4WTriplePrime_selectedOuterContractGraph,
    ResolvedAdmissibleSubgraph.contractWithStars_externalLegs] at hℓ₁' hℓ₂'
  obtain ⟨ℓ₁, hℓ₁, rfl⟩ := Multiset.mem_map.mp hℓ₁'
  obtain ⟨ℓ₂, hℓ₂, rfl⟩ := Multiset.mem_map.mp hℓ₂'
  have hidL : ℓ₁.legId = ℓ₂.legId := by
    simpa only [ResolvedAdmissibleSubgraph.retargetExternalLeg, ResolvedExternalLeg.retarget_legId]
      using hid
  have hll : ℓ₁ = ℓ₂ := hGId ℓ₁ hℓ₁ ℓ₂ hℓ₂ hidL
  rw [hll]

/-- **body-606 (Step 4) — `Q` is φ⁴ connected-divergent** (as a class).  This IS the canonical supply's
`hCD` at `selectedOuter`, since `Q` is definitionally that contraction. -/
theorem phi4WTriplePrime_Q_isConnectedDivergent
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) :
    ResolvedFeynmanGraphClass.IsConnectedDivergentFor phi4DivergenceMeasureFamily
      phi4PermInvariantDivergenceMeasureFamily
      (phi4WTriplePrime_selectedOuterContractGraph s).toResolvedClass :=
  phi4WTriplePrimeCanonicalSupply.hCD G (phi4WTriplePrime_selectedOuter s)
    (phi4WTriplePrime_selectedOuter_mem s)

/-! ## Step 5 — HEADLINE W‴ membership -/

/-- **body-606 (Step 5, HEADLINE) — the quotient forest of a W‴ filtered split choice lands back in the W‴
(fifth-axis) index on the quotient ambient `Q`.**  Type is `{G} (s)` ONLY — the complement positivity is
derived internally (body-500/501 input-residual route).  NO external gate / `Measure` / `E` / forbidden
class. -/
theorem phi4WTriplePrime_quotientForest_mem
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) :
    phi4WTriplePrime_quotientForest s
      ∈ phi4WTriplePrimeIndex (phi4WTriplePrime_selectedOuterContractGraph s) :=
  (mem_phi4WTriplePrimeIndex (phi4WTriplePrime_selectedOuterContractGraph s)
      (phi4WTriplePrime_quotientForest s)).mpr
    ⟨phi4WTriplePrime_Q_ambientSupported s, phi4WTriplePrime_Q_isConnectedDivergent s,
      phi4WTriplePrime_Q_edgeIdsUnique s, phi4WTriplePrime_Q_legIdsUnique s,
      phi4WTriplePrime_quotientForest_isProperForest s,
      phi4WTriplePrime_quotientForest_forestSaturated s,
      phi4WTriplePrime_quotientForest_forestEdgeComplete s⟩

end GaugeGeometry.QFT.Combinatorial
