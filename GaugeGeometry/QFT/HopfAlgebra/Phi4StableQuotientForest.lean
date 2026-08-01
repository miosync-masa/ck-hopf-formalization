import GaugeGeometry.QFT.HopfAlgebra.Phi4StableRemnantForest

/-!
# QFT-R1-body-637 — the LIVE stable quotient forest + W‴ membership

Body-634 built the STABLE right-survivor forest and body-636 the STABLE remnant forest, both on the stable
quotient ambient `Q := stableSelectedOuterContractGraph s.1`.  This body UNIONS them into `stableQuotientForest`
and lands it back in the fifth-axis index `phi4WTriplePrimeIndex Q` — so the quotient of a stable mixed split
choice is itself a LIVE W‴ forest on `Q`.  With body-634's `stableSelectedOuter` (a live W‴ member of `G`) this
completes the two-stage coproduct's geometric inputs: BOTH `stableSelectedOuter` AND `stableQuotientForest` are
now live W‴ members.  This is the STABLE mirror of body-606 — reproduced CLEAN on the stable carrier; body-606's
old-choice-keyed decls are NOT consumed, the argument is mirrored.

## Steps

* **Step 1 — cross disjointness** (`stableQuotient_crossDisjoint`).  A right survivor `γ_R` and a remnant
  `stableRemnantComponent o` (owner `γ_F = o.γ.1`) have different owners (choice-tag contradiction:
  `Sum.inl false ≠ Sum.inr B`), so `s.1.outer.pairwiseDisjoint` separates the `γ_F`-vertices from `γ_R`; the
  remnant's promoted global stars are fresh (outside `G`) while `γ_R.vertices ⊆ G.vertices`.  NO global τ.
* **Step 2 — the quotient forest** (`stableQuotientForest` + `_elements` / `_element_cases` returning the
  concrete RIGHT-survivor / remnant witness / `_isNonempty`).  Nonemptiness is the WHOLE union ONLY, from `s`'s
  not-all-LEFT (`stableMixedChoice_not_all_left`): some component's choice is `Sum.inl false` (right → survivor)
  or `Sum.inr B` (forest → remnant).  We do NOT claim either constituent forest nonempty.
* **Step 3 — the input-residual bound** (LOAD-BEARING).  `stableOwnerCount`,
  `stableSelectedOuter_internalEdges_le_outer`, `stableRightComponent_add_selectedOuter_le_outer`,
  `stableOccurrence_add_selectedOuter_le_outer`, `stableRightSurvivor_internalEdges_le_residual`,
  `stableRemnant_internalEdges_le_residual`, `stableQuotientForest_internalEdges_le_residual`,
  `stableQuotient_complement_pos`.  With `A := stableSelectedOuter s.1`, `r := A.retargetEdge (starOf …)`,
  `R := s.1.outer.internalEdges − A.internalEdges`: `stableQuotientForest.internalEdges ≤ R.map r` and
  `card R < card A.complementEdges = card Q.internalEdges` (because `s.1.outer` has a positive complement in `G`),
  so `0 < Q.complementEdges.card`.  A Multiset-multiplicity-preserving card inequality — NO edge-witness
  weakening.  The remnant bound is `remnant.internalEdges = B.1.complementEdges.map r` (body-635).
* **Step 4 — properness** (`stableQuotientForest_isProperForest`, five conjuncts UNCONDITIONAL).  Complement
  positivity is DERIVED (Step 3), so this takes ONLY `{G} (s)`.  NO external residual hypothesis.
* **Step 5 — W‴ landing.**  `stableQuotientForest_forestSaturated` / `_forestEdgeComplete` (element_cases →
  634/636); `stableQuotient_Q_ambientSupported` (contractWithStars primitives, clean);
  `stableQuotient_Q_isConnectedDivergent` (`phi4WTriplePrimeCanonicalSupply.hCD` at `stableSelectedOuter_mem`);
  `stableQuotient_Q_edgeIdsUnique` / `_legIdsUnique` (project `stableSelectedOuterContractGraph_stableIds`).
  **HEADLINE** `stableQuotientForest_mem : stableQuotientForest s ∈ phi4WTriplePrimeIndex
  (stableSelectedOuterContractGraph s.1)`, type takes ONLY `hSt` / `s`.

## HALT / red lines
Body-625's no-go and bodies 629-636 / the old carrier are UNEDITED.  body-606 is BLUEPRINT ONLY — its
old-choice-keyed theorems are NOT consumed as terms.  We do NOT claim any constituent forest's
`Nonempty` / `IsProperForest` / W‴ membership.  The right-factor aggregate (638), `quot_eq` (639), summand
agreement / forest-block Equiv / coassoc are NOT entered.  ZERO new `structure` / `class` / permanent `instance`
(one file-local `local instance` for the φ⁴ family); ZERO forbidden divergence class in any declaration TYPE;
ZERO `sorry` / `admit` / `native_decide`; NO global correcting permutation; NO `HEq` / `cast` / graph-data `▸`
(Prop-membership `▸` only); NO `toFinset` / dedup / orbit quotient.  Axiom-clean (`propext`, `Classical.choice`,
`Quot.sound`).
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

open ResolvedFeynmanSubgraph

variable {G : ResolvedFeynmanGraph}

set_option maxHeartbeats 3200000

/-- The concrete φ⁴ divergence measure family, registered file-locally (providable instance, NO forbidden
class). -/
noncomputable local instance instPhi4DivergenceMeasureFamily637 : (H : FeynmanGraph) → DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

variable {hSt : StableResolvedBoundaryIds G} {s : StablePhi4MixedSplitChoice G hSt}

/-! ## Step 1 — cross disjointness of survivors vs. remnants -/

/-- **body-637 (Step 1) — cross-disjointness of the RIGHT survivors vs. the remnants.**  A right survivor
`γ_R` and a remnant `stableRemnantComponent o` (owner `γ_F = o.γ.1`) have different owners — the choice tags
`Sum.inl false` vs. `Sum.inr o.B` disagree — so `s.1.outer.pairwiseDisjoint` separates the `γ_F`-vertices from
`γ_R`; the remnant's promoted global stars are fresh (outside `G`) while `γ_R.vertices ⊆ G.vertices`.  NO global
τ. -/
theorem stableQuotient_crossDisjoint (s : StablePhi4MixedSplitChoice G hSt) :
    ∀ γ ∈ (stableRightSurvivorForest s.1).elements,
      ∀ δ ∈ (stableRemnantForest s).elements, γ ≠ δ → γ.Disjoint δ := by
  intro γ hγ δ hδ _hne
  obtain ⟨γR, hγR, rfl⟩ := stableRightSurvivorForest_element_origin s.1 hγ
  obtain ⟨o, rfl⟩ := stableRemnantForest_element_origin hδ
  have hpfSel := stableSelectedOuter_isProperForest s.1
  have hneOwner : γR ≠ o.γ.1 := by
    intro heq
    subst heq
    exact absurd (hγR.choose_spec.symm.trans o.hchoice) (by simp)
  have hdd : o.γ.1.Disjoint γR :=
    s.1.outer.pairwiseDisjoint o.γ.2 hγR.choose (fun h => hneOwner h.symm)
  show _root_.Disjoint (stableRightSurvivor s.1 hγR).vertices
    (stableRemnantComponent o).vertices
  rw [stableRightSurvivor_vertices, Finset.disjoint_left]
  intro v hvγR hvrem
  rcases stableRemnant_origin o hvrem with hvγF | ⟨δ0, hδ0, hveq⟩
  · exact Finset.disjoint_left.mp hdd hvγF hvγR
  · exact stableRemnant_gen_star_not_mem (stableSelectedOuter s.1) hpfSel
      (stableRemnant_promoted_mem o hδ0) (hveq ▸ γR.vertices_subset hvγR)

/-! ## Step 2 — the quotient forest + honest nonemptiness -/

/-- **body-637 (Step 2) — the LIVE stable quotient forest** in the stable quotient ambient `Q`.  The union of
the RIGHT-survivor forest (634) and the remnant forest (636). -/
noncomputable def stableQuotientForest (s : StablePhi4MixedSplitChoice G hSt) :
    @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily
      (stableSelectedOuterContractGraph s.1) :=
  (stableRightSurvivorForest s.1).union (stableRemnantForest s)
    (stableQuotient_crossDisjoint s)

@[simp] theorem stableQuotientForest_elements (s : StablePhi4MixedSplitChoice G hSt) :
    (stableQuotientForest s).elements
      = (stableRightSurvivorForest s.1).elements ∪ (stableRemnantForest s).elements := by
  unfold stableQuotientForest
  ext c
  simp only [ResolvedAdmissibleSubgraph.union_elements, Finset.mem_union]

/-- **body-637 (Step 2) — element cases (concrete witnesses).**  Every quotient-forest element is either a
RIGHT survivor `stableRightSurvivor s.1 hγR` of a concrete RIGHT component OR a remnant `stableRemnantComponent o`
of a concrete forest-choice occurrence. -/
theorem stableQuotientForest_element_cases (s : StablePhi4MixedSplitChoice G hSt)
    {δ : ResolvedFeynmanSubgraph (stableSelectedOuterContractGraph s.1)}
    (hδ : δ ∈ (stableQuotientForest s).elements) :
    (∃ (γ : ResolvedFeynmanSubgraph G) (hγR : stableIsRightComponent s.1 γ),
        δ = stableRightSurvivor s.1 hγR)
      ∨ (∃ o : StableForestChoiceOccurrence s, δ = stableRemnantComponent o) := by
  rw [stableQuotientForest_elements, Finset.mem_union] at hδ
  rcases hδ with h | h
  · exact Or.inl (stableRightSurvivorForest_element_origin s.1 h)
  · exact Or.inr (stableRemnantForest_element_origin h)

/-- **body-637 (Step 2) — honest nonemptiness of the WHOLE quotient forest.**  From `s`'s not-all-LEFT
(`stableMixedChoice_not_all_left`): some component's choice is not `Sum.inl true`; a `Sum.inl false` (right)
yields a survivor in the union, a `Sum.inr B` (forest) yields a remnant in the union.  Proved ONLY for the whole
union — never for `stableRightSurvivorForest` / `stableRemnantForest` separately. -/
theorem stableQuotientForest_isNonempty (s : StablePhi4MixedSplitChoice G hSt) :
    (stableQuotientForest s).IsNonempty := by
  obtain ⟨a, hatt, ha⟩ := stableMixedChoice_not_all_left s
  show (stableQuotientForest s).elements.Nonempty
  rw [stableQuotientForest_elements]
  rcases hcase : s.1.choice a hatt with b | B
  · rcases b with _ | _
    · -- Sum.inl false → a.1 is a RIGHT component → survivor in the left of the union
      have haR : stableIsRightComponent s.1 a.1 := ⟨a.2, hcase⟩
      have hmemRC : a.1 ∈ stableRightComponents s.1 :=
        (stableMem_rightComponents s.1).mpr ⟨a.2, haR⟩
      refine ⟨stableRightSurvivor s.1 ((stableMem_rightComponents s.1).mp hmemRC).2, ?_⟩
      refine Finset.mem_union_left _ ?_
      rw [stableRightSurvivorForest_elements]
      exact Finset.mem_image.mpr ⟨⟨a.1, hmemRC⟩, Finset.mem_attach _ _, rfl⟩
    · -- Sum.inl true → contradicts `ha`
      exact absurd hcase ha
  · -- Sum.inr B → a.1 is a FOREST component → remnant in the right of the union
    have haF : stableIsForestComponent s a.1 := ⟨a.2, B, hcase⟩
    have hmemFC : a.1 ∈ stableForestComponents s :=
      (stableMem_forestComponents s).mpr ⟨a.2, haF⟩
    refine ⟨stableRemnantComponent
      (stableForestComponentOccurrence ⟨a.1, hmemFC⟩), ?_⟩
    refine Finset.mem_union_right _ ?_
    rw [stableRemnantForest_elements]
    exact Finset.mem_image.mpr ⟨⟨a.1, hmemFC⟩, Finset.mem_attach _ _, rfl⟩

/-! ## Step 3 — the input-residual bound (bodies 500/501 route, re-derived CLEAN on the stable carrier).
Let `A := stableSelectedOuter s.1`, `r := A.retargetEdge (starOf …)`, `R := s.1.outer.internalEdges − A.internalEdges`
(the input residual).  We prove `stableQuotientForest.internalEdges ≤ R.map r`, and
`card R < card A.complementEdges = card Q.internalEdges`, so the quotient complement is strictly positive. -/

/-- **body-637 (Step 3) — the owner count lemma** (multiplicity-safe, generic).  In a pairwise-disjoint forest,
an edge's multiplicity in the whole forest equals its multiplicity in the single component that carries it. -/
theorem stableOwnerCount {H : ResolvedFeynmanGraph}
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

/-- **body-637 (Step 3) — `stableSelectedOuter`'s internal edges are inside `s.1.outer`'s** (each component
lands in an `s.1.outer` component or is a promoted lift of one). -/
theorem stableSelectedOuter_internalEdges_le_outer (s : StablePhi4MixedSplitChoice G hSt) :
    (stableSelectedOuter s.1).internalEdges ≤ s.1.outer.internalEdges := by
  refine phi4WTriplePrime_internalEdges_le_of_components_le (stableSelectedOuter s.1)
    (fun c hc => ?_)
  rcases stableSelectedOuter_component_origin s.1 hc with ⟨hcmem, -⟩ | hP
  · exact Finset.single_le_sum (f := fun x : ResolvedFeynmanSubgraph G => x.internalEdges)
      (fun i _ => Multiset.zero_le _) hcmem
  · obtain ⟨γ, hγ, B, -, δ, hδ, rfl⟩ := hP
    have h1 : (stableRootRelativeInner γ δ).internalEdges ≤ γ.internalEdges := by
      show δ.internalEdges ≤ γ.internalEdges
      exact δ.internalEdges_le
    exact le_trans h1 (Finset.single_le_sum (f := fun x : ResolvedFeynmanSubgraph G => x.internalEdges)
      (fun i _ => Multiset.zero_le _) hγ)

/-- **body-637 (Step 3) — the selected-outer owner bound**: a `γ`-internal edge occurs no more often in
`stableSelectedOuter` than in the occurrence forest `B`. -/
theorem stableSelectedOuter_count_le_occurrence
    (o : StableForestChoiceOccurrence s) {e : ResolvedFeynmanEdge}
    (heγ : e ∈ o.γ.1.internalEdges) :
    Multiset.count e (stableSelectedOuter s.1).internalEdges
      ≤ Multiset.count e o.B.1.internalEdges := by
  by_cases hcS : Multiset.count e (stableSelectedOuter s.1).internalEdges = 0
  · rw [hcS]; exact Nat.zero_le _
  · have heS : e ∈ (stableSelectedOuter s.1).internalEdges :=
      Multiset.count_pos.mp (Nat.pos_of_ne_zero hcS)
    obtain ⟨σ, hσ, heσ⟩ := stableRemnant_mem_selectedOuter_internalEdges o heS
    have howner : Multiset.count e (stableSelectedOuter s.1).internalEdges
        = Multiset.count e σ.internalEdges := stableOwnerCount hσ heσ
    rcases stableSelectedOuter_component_origin s.1 hσ with ⟨hσmem, hleftσ⟩ | hP
    · exfalso
      by_cases hσγ : σ = o.γ.1
      · obtain ⟨hh, hσtrue⟩ := hleftσ
        subst hσγ
        exact absurd (hσtrue.symm.trans o.hchoice) (by simp)
      · exact Finset.disjoint_left.mp (s.1.outer.pairwiseDisjoint hσmem o.γ.2 hσγ)
          (σ.edges_supported e heσ).1 (o.γ.1.edges_supported e heγ).1
    · obtain ⟨γ', hγ', B', hchoice', δ, hδ, rfl⟩ := hP
      have hσγ' : γ' = o.γ.1 := by
        by_contra hne
        exact Finset.disjoint_left.mp (s.1.outer.pairwiseDisjoint hγ' o.γ.2 hne)
          (stableRootRelativeInner_vertices_subset γ' δ
            ((stableRootRelativeInner γ' δ).edges_supported e heσ).1)
          (o.γ.1.edges_supported e heγ).1
      subst hσγ'
      have hBeq : B' = o.B := Sum.inr.inj (hchoice'.symm.trans o.hchoice)
      subst hBeq
      rw [howner, stableRootRelativeInner_internalEdges]
      exact Multiset.count_le_of_le e
        (Finset.single_le_sum (fun i _ => Multiset.zero_le _) hδ)

/-- **body-637 (Step 3) — a RIGHT component + `stableSelectedOuter` fit disjointly inside `s.1.outer`.** -/
theorem stableRightComponent_add_selectedOuter_le_outer
    (s : StablePhi4MixedSplitChoice G hSt) {γ : ResolvedFeynmanSubgraph G}
    (hγR : stableIsRightComponent s.1 γ) :
    γ.internalEdges + (stableSelectedOuter s.1).internalEdges ≤ s.1.outer.internalEdges := by
  rw [Multiset.le_iff_count]
  intro e
  rw [Multiset.count_add]
  by_cases hcr : e ∈ γ.internalEdges
  · have hown : Multiset.count e s.1.outer.internalEdges = Multiset.count e γ.internalEdges :=
      stableOwnerCount hγR.choose hcr
    have hdisj : Disjoint γ.vertices (stableSelectedOuter s.1).vertices :=
      stableRightComponent_disjoint_selectedOuter s.1 hγR
    have hS0 : Multiset.count e (stableSelectedOuter s.1).internalEdges = 0 := by
      rw [Multiset.count_eq_zero]
      intro heS
      exact Finset.disjoint_left.mp hdisj (γ.edges_supported e hcr).1
        (stableRight_source_mem_vertices (stableSelectedOuter s.1) heS)
    rw [hown, hS0]
    omega
  · rw [Multiset.count_eq_zero.mpr hcr, Nat.zero_add]
    exact Multiset.count_le_of_le e (stableSelectedOuter_internalEdges_le_outer s)

/-- **body-637 (Step 3) — an occurrence's inner complement + `stableSelectedOuter` fit inside `s.1.outer`.** -/
theorem stableOccurrence_add_selectedOuter_le_outer
    (o : StableForestChoiceOccurrence s) :
    o.B.1.complementEdges + (stableSelectedOuter s.1).internalEdges
      ≤ s.1.outer.internalEdges := by
  rw [Multiset.le_iff_count]
  intro e
  rw [Multiset.count_add]
  by_cases hcB : e ∈ o.B.1.complementEdges
  · have heγ : e ∈ o.γ.1.internalEdges := by
      have h : e ∈ (stableLocalBoundaryCompletedGraph o.γ.1).internalEdges :=
        Multiset.mem_of_le (Multiset.sub_le_self _ _) hcB
      rwa [stableLocalBoundaryCompletedGraph_internalEdges] at h
    have hSB := stableSelectedOuter_count_le_occurrence o heγ
    have hcomp : Multiset.count e o.B.1.complementEdges
        = Multiset.count e o.γ.1.internalEdges - Multiset.count e o.B.1.internalEdges := by
      show Multiset.count e ((stableLocalBoundaryCompletedGraph o.γ.1).internalEdges
        - o.B.1.internalEdges) = _
      rw [Multiset.count_sub, stableLocalBoundaryCompletedGraph_internalEdges]
    have hBγ : Multiset.count e o.B.1.internalEdges ≤ Multiset.count e o.γ.1.internalEdges := by
      have h := Multiset.count_le_of_le e
        (phi4WTriplePrime_internalEdges_le_of_components_le o.B.1 (fun c _ => c.internalEdges_le))
      rwa [stableLocalBoundaryCompletedGraph_internalEdges] at h
    have hown : Multiset.count e s.1.outer.internalEdges = Multiset.count e o.γ.1.internalEdges :=
      stableOwnerCount o.γ.2 heγ
    rw [hcomp, hown]
    omega
  · rw [Multiset.count_eq_zero.mpr hcB, Nat.zero_add]
    exact Multiset.count_le_of_le e (stableSelectedOuter_internalEdges_le_outer s)

/-- **body-637 (Step 3) — the RIGHT survivor's residual bound** `survivor.internalEdges ≤ R.map r`. -/
theorem stableRightSurvivor_internalEdges_le_residual
    (s : StablePhi4MixedSplitChoice G hSt) {γ : ResolvedFeynmanSubgraph G}
    (hγR : stableIsRightComponent s.1 γ) :
    (stableRightSurvivor s.1 hγR).internalEdges
      ≤ (s.1.outer.internalEdges - (stableSelectedOuter s.1).internalEdges).map
          ((stableSelectedOuter s.1).retargetEdge
            (phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1))) := by
  have hle_R : γ.internalEdges
      ≤ s.1.outer.internalEdges - (stableSelectedOuter s.1).internalEdges :=
    (le_tsub_iff_right (stableSelectedOuter_internalEdges_le_outer s)).2
      (stableRightComponent_add_selectedOuter_le_outer s hγR)
  have hdisj : Disjoint γ.vertices (stableSelectedOuter s.1).vertices :=
    stableRightComponent_disjoint_selectedOuter s.1 hγR
  have hmapid : γ.internalEdges.map ((stableSelectedOuter s.1).retargetEdge
      (phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1)))
      = γ.internalEdges := by
    conv_rhs => rw [← Multiset.map_id γ.internalEdges]
    apply Multiset.map_congr rfl
    intro e he
    obtain ⟨hs, ht⟩ := γ.edges_supported e he
    unfold ResolvedAdmissibleSubgraph.retargetEdge ResolvedFeynmanEdge.retarget
    rw [(stableSelectedOuter s.1).retargetVertex_of_not_mem _
        (Finset.disjoint_left.mp hdisj hs),
      (stableSelectedOuter s.1).retargetVertex_of_not_mem _
        (Finset.disjoint_left.mp hdisj ht)]
    rfl
  rw [stableRightSurvivor_internalEdges, ← hmapid]
  exact Multiset.map_le_map hle_R

/-- **body-637 (Step 3) — the remnant's residual bound** `remnant.internalEdges ≤ R.map r`.  From body-635's
`stableRemnant_internalEdges_eq` (`remnant.internalEdges = B.1.complementEdges.map r`). -/
theorem stableRemnant_internalEdges_le_residual
    (o : StableForestChoiceOccurrence s) :
    (stableRemnantComponent o).internalEdges
      ≤ (s.1.outer.internalEdges - (stableSelectedOuter s.1).internalEdges).map
          ((stableSelectedOuter s.1).retargetEdge
            (phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1))) := by
  rw [stableRemnantComponent_internalEdges, stableRemnant_internalEdges_eq]
  refine Multiset.map_le_map ?_
  exact (le_tsub_iff_right (stableSelectedOuter_internalEdges_le_outer s)).2
    (stableOccurrence_add_selectedOuter_le_outer o)

/-- **body-637 (Step 3) — the whole quotient forest is inside the input residual** `R.map r`. -/
theorem stableQuotientForest_internalEdges_le_residual (s : StablePhi4MixedSplitChoice G hSt) :
    (stableQuotientForest s).internalEdges
      ≤ (s.1.outer.internalEdges - (stableSelectedOuter s.1).internalEdges).map
          ((stableSelectedOuter s.1).retargetEdge
            (phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1))) := by
  refine phi4WTriplePrime_internalEdges_le_of_components_le (stableQuotientForest s)
    (fun c hc => ?_)
  rcases stableQuotientForest_element_cases s hc with ⟨γ, hγR, rfl⟩ | ⟨o, rfl⟩
  · exact stableRightSurvivor_internalEdges_le_residual s hγR
  · exact stableRemnant_internalEdges_le_residual o

/-- **body-637 (Step 3, HEADLINE) — the quotient complement is strictly positive.**  The input residual
`R = s.1.outer.internalEdges − stableSelectedOuter.internalEdges` has strictly fewer edges than
`A.complementEdges = G.internalEdges − stableSelectedOuter.internalEdges` (because `s.1.outer` has a positive
complement in `G`), and `stableQuotientForest.internalEdges ≤ R.map r ≤ Q.internalEdges`, so
`0 < Q.complementEdges.card`.  NO external hypothesis, NO edge-witness weakening. -/
theorem stableQuotient_complement_pos (s : StablePhi4MixedSplitChoice G hSt) :
    0 < (stableQuotientForest s).complementEdges.card := by
  have houterProper : s.1.outer.IsProperForest :=
    ((mem_phi4WTriplePrimeIndex G s.1.outer).mp s.1.outer_mem).2.2.2.2.1
  have hSelLe : (stableSelectedOuter s.1).internalEdges ≤ s.1.outer.internalEdges :=
    stableSelectedOuter_internalEdges_le_outer s
  have hOutLeG : s.1.outer.internalEdges ≤ G.internalEdges :=
    phi4WTriplePrime_internalEdges_le_of_components_le s.1.outer (fun c _ => c.internalEdges_le)
  have hSelLeG : (stableSelectedOuter s.1).internalEdges ≤ G.internalEdges :=
    le_trans hSelLe hOutLeG
  -- qF.internalEdges ≤ Q.internalEdges
  have hqFQ : (stableQuotientForest s).internalEdges
      ≤ (stableSelectedOuterContractGraph s.1).internalEdges :=
    phi4WTriplePrime_internalEdges_le_of_components_le (stableQuotientForest s)
      (fun c _ => c.internalEdges_le)
  -- card(Q.internalEdges) = card G.I - card stableSelectedOuter.I
  have hQcard : (stableSelectedOuterContractGraph s.1).internalEdges.card
      = G.internalEdges.card - (stableSelectedOuter s.1).internalEdges.card := by
    rw [stableSelectedOuterContractGraph,
      ResolvedAdmissibleSubgraph.contractWithStars_internalEdges, Multiset.card_map]
    show ((G.internalEdges - (stableSelectedOuter s.1).internalEdges)).card = _
    rw [Multiset.card_sub hSelLeG]
  -- card(qF.internalEdges) ≤ card R = card s.1.outer.I - card stableSelectedOuter.I
  have hqFcardle : (stableQuotientForest s).internalEdges.card
      ≤ s.1.outer.internalEdges.card - (stableSelectedOuter s.1).internalEdges.card := by
    have h1 := Multiset.card_le_card (stableQuotientForest_internalEdges_le_residual s)
    rwa [Multiset.card_map, Multiset.card_sub hSelLe] at h1
  -- s.1.outer has a positive complement: card s.1.outer.I < card G.I
  have hOutLtG : s.1.outer.internalEdges.card < G.internalEdges.card := by
    have hpos : 0 < s.1.outer.complementEdges.card :=
      ResolvedAdmissibleSubgraph.complementEdges_card_pos_of_isProperForest houterProper
    have : s.1.outer.complementEdges.card
        = G.internalEdges.card - s.1.outer.internalEdges.card := by
      show (G.internalEdges - s.1.outer.internalEdges).card = _
      rw [Multiset.card_sub hOutLeG]
    omega
  have hcardSel : (stableSelectedOuter s.1).internalEdges.card ≤ s.1.outer.internalEdges.card :=
    Multiset.card_le_card hSelLe
  have hcardOut : s.1.outer.internalEdges.card ≤ G.internalEdges.card := Multiset.card_le_card hOutLeG
  show 0 < ((stableSelectedOuterContractGraph s.1).internalEdges
    - (stableQuotientForest s).internalEdges).card
  rw [Multiset.card_sub hqFQ, hQcard]
  omega

/-! ## Step 4 — IsProperForest (complement positivity derived internally — no hypothesis) -/

/-- **body-637 (Step 4) — the quotient forest is a proper forest.**  Five conjuncts UNCONDITIONAL: whole-union
nonempty (Step 2); component vertices nonempty (survivor via outer properness, remnant via body-636); component
internal edges positive (survivor via outer properness; remnant via `stableRemnant_internalEdges_eq` + `card_map`
+ inner-B complement positivity); aggregate internal edges positive (from a nonempty component); complement
positive (Step 3).  Takes only `{G} (s)` — NO external residual hypothesis. -/
theorem stableQuotientForest_isProperForest (s : StablePhi4MixedSplitChoice G hSt) :
    @ResolvedAdmissibleSubgraph.IsProperForest phi4DivergenceMeasureFamily
      (stableSelectedOuterContractGraph s.1) (stableQuotientForest s) := by
  have houterMem := (mem_phi4WTriplePrimeIndex G s.1.outer).mp s.1.outer_mem
  have houterProper : s.1.outer.IsProperForest := houterMem.2.2.2.2.1
  -- HasNonemptyComponents
  have hNC : (stableQuotientForest s).HasNonemptyComponents := by
    intro c hc
    rcases stableQuotientForest_element_cases s hc with ⟨γ, hγR, rfl⟩ | ⟨o, rfl⟩
    · show 0 < (stableRightSurvivor s.1 hγR).vertices.card
      rw [stableRightSurvivor_vertices]
      exact houterProper.2.1 γ hγR.choose
    · exact stableRemnant_isNonempty o
  -- HasPositiveInternalEdgesComponents
  have hPC : (stableQuotientForest s).HasPositiveInternalEdgesComponents := by
    intro c hc
    rcases stableQuotientForest_element_cases s hc with ⟨γ, hγR, rfl⟩ | ⟨o, rfl⟩
    · rw [stableRightSurvivor_internalEdges]
      exact houterProper.2.2.2.1 γ hγR.choose
    · rw [stableRemnantComponent_internalEdges, stableRemnant_internalEdges_eq,
        Multiset.card_map]
      exact ResolvedAdmissibleSubgraph.complementEdges_card_pos_of_isProperForest
        (stableForestOcc_B_isProperForest o)
  -- 0 < internalEdges.card
  have hIE : 0 < (stableQuotientForest s).internalEdges.card := by
    obtain ⟨η, hη⟩ := stableQuotientForest_isNonempty s
    have hηle : η.internalEdges ≤ (stableQuotientForest s).internalEdges :=
      Finset.single_le_sum (f := fun x : ResolvedFeynmanSubgraph
          (stableSelectedOuterContractGraph s.1) => x.internalEdges)
        (fun i _ => Multiset.zero_le _) hη
    exact lt_of_lt_of_le (hPC η hη) (Multiset.card_le_card hηle)
  exact ⟨stableQuotientForest_isNonempty s, hNC, hIE, hPC,
    stableQuotient_complement_pos s⟩

/-! ## Step 5 — sixth/seventh axes + ambient gates + HEADLINE W‴ membership -/

/-- **body-637 (Step 5, sixth axis) — the quotient forest is externally-leg saturated on `Q`.** -/
theorem stableQuotientForest_forestSaturated (s : StablePhi4MixedSplitChoice G hSt) :
    ResolvedForestExternalLegSaturated (stableQuotientForest s) := by
  intro δ hδ
  rcases stableQuotientForest_element_cases s hδ with ⟨γ, hγR, rfl⟩ | ⟨o, rfl⟩
  · exact stableRightSurvivor_saturated s.1 hγR
  · exact stableRemnant_externalLegSaturated o

/-- **body-637 (Step 5, seventh axis) — the quotient forest is internal-edge complete on `Q`.** -/
theorem stableQuotientForest_forestEdgeComplete (s : StablePhi4MixedSplitChoice G hSt) :
    ResolvedForestInternalEdgeComplete phi4DivergenceMeasureFamily (stableQuotientForest s) := by
  intro γ hγ
  rcases stableQuotientForest_element_cases s hγ with ⟨g, hγR, rfl⟩ | ⟨o, rfl⟩
  · exact stableRightSurvivor_edgeComplete s.1 hγR
  · exact stableRemnant_internalEdgeComplete o

/-- **body-637 (Step 5) — `Q` is ambient-supported** (edges + legs), from `G`'s ambient support through the
`contractWithStars` retarget landing.  Clean from the contractWithStars primitives. -/
theorem stableQuotient_Q_ambientSupported (s : StablePhi4MixedSplitChoice G hSt) :
    ResolvedAmbientSupported (stableSelectedOuterContractGraph s.1) := by
  have hG : ResolvedAmbientSupported G := ((mem_phi4WTriplePrimeIndex G s.1.outer).mp s.1.outer_mem).1
  refine ⟨?_, ?_⟩
  · intro e' he'
    rw [stableSelectedOuterContractGraph,
      ResolvedAdmissibleSubgraph.contractWithStars_internalEdges] at he'
    obtain ⟨e, he, rfl⟩ := Multiset.mem_map.mp he'
    have heG : e ∈ G.internalEdges := Multiset.mem_of_le (Multiset.sub_le_self _ _) he
    obtain ⟨hs, ht⟩ := hG.1 e heG
    refine ⟨?_, ?_⟩
    · show (stableSelectedOuter s.1).retargetVertex _ e.source
        ∈ (stableSelectedOuterContractGraph s.1).vertices
      rw [stableSelectedOuterContractGraph]
      exact (stableSelectedOuter s.1).retargetVertex_mem_contractWithStars_vertices _ hs
    · show (stableSelectedOuter s.1).retargetVertex _ e.target
        ∈ (stableSelectedOuterContractGraph s.1).vertices
      rw [stableSelectedOuterContractGraph]
      exact (stableSelectedOuter s.1).retargetVertex_mem_contractWithStars_vertices _ ht
  · intro ℓ' hℓ'
    rw [stableSelectedOuterContractGraph,
      ResolvedAdmissibleSubgraph.contractWithStars_externalLegs] at hℓ'
    obtain ⟨ℓ, hℓ, rfl⟩ := Multiset.mem_map.mp hℓ'
    show (stableSelectedOuter s.1).retargetVertex _ ℓ.attachedTo
      ∈ (stableSelectedOuterContractGraph s.1).vertices
    rw [stableSelectedOuterContractGraph]
    exact (stableSelectedOuter s.1).retargetVertex_mem_contractWithStars_vertices _
      (hG.2 ℓ hℓ)

/-- **body-637 (Step 5) — `Q` is φ⁴ connected-divergent** (as a class).  This IS the canonical supply's `hCD`
at `stableSelectedOuter`, since `Q` is definitionally that contraction. -/
theorem stableQuotient_Q_isConnectedDivergent (s : StablePhi4MixedSplitChoice G hSt) :
    ResolvedFeynmanGraphClass.IsConnectedDivergentFor phi4DivergenceMeasureFamily
      phi4PermInvariantDivergenceMeasureFamily
      (stableSelectedOuterContractGraph s.1).toResolvedClass :=
  phi4WTriplePrimeCanonicalSupply.hCD G (stableSelectedOuter s.1)
    (stableSelectedOuter_mem s.1)

/-- **body-637 (Step 5) — `Q` has unique edge ids**, projected from the stable boundary-ID certificate of `Q`
(`stableSelectedOuterContractGraph_stableIds`). -/
theorem stableQuotient_Q_edgeIdsUnique (s : StablePhi4MixedSplitChoice G hSt) :
    (stableSelectedOuterContractGraph s.1).EdgeIdsUnique :=
  (stableSelectedOuterContractGraph_stableIds s.1).edgeIdsUnique

/-- **body-637 (Step 5) — `Q` has unique leg ids**, projected from the stable boundary-ID certificate of `Q`. -/
theorem stableQuotient_Q_legIdsUnique (s : StablePhi4MixedSplitChoice G hSt) :
    (stableSelectedOuterContractGraph s.1).LegIdsUnique :=
  (stableSelectedOuterContractGraph_stableIds s.1).legIdsUnique

/-- **body-637 (Step 5, HEADLINE) — the LIVE stable quotient forest lands back in the W‴ (fifth-axis) index on
the stable quotient ambient `Q`.**  Type is `{G} (s)` ONLY — the complement positivity is derived internally
(Step 3 input-residual route).  NO external gate / `Measure` / `E` / residual hypothesis / forbidden class.  With
body-634's `stableSelectedOuter_mem`, both `stableSelectedOuter` (live on `G`) AND `stableQuotientForest` (live on
`Q`) are now W‴ members. -/
theorem stableQuotientForest_mem (s : StablePhi4MixedSplitChoice G hSt) :
    stableQuotientForest s
      ∈ phi4WTriplePrimeIndex (stableSelectedOuterContractGraph s.1) :=
  (mem_phi4WTriplePrimeIndex (stableSelectedOuterContractGraph s.1)
      (stableQuotientForest s)).mpr
    ⟨stableQuotient_Q_ambientSupported s, stableQuotient_Q_isConnectedDivergent s,
      stableQuotient_Q_edgeIdsUnique s, stableQuotient_Q_legIdsUnique s,
      stableQuotientForest_isProperForest s,
      stableQuotientForest_forestSaturated s,
      stableQuotientForest_forestEdgeComplete s⟩

end GaugeGeometry.QFT.Combinatorial
