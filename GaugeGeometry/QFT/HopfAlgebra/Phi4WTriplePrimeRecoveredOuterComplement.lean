import GaugeGeometry.QFT.HopfAlgebra.Phi4WTriplePrimeForestBlockCorrectedEquiv

/-!
# QFT-R1-body-618 — the recovered outer forest has POSITIVE complement in `G`

This body discharges the SOLE missing `IsProperForest` conjunct for the W‴ membership of
`O := phi4WTriplePrime_recoveredOuter z` (frontier #1 of body-617): its positive complement
`0 < O.complementEdges.card`.  It is the exact INVERSE MIRROR of body-606's forward residual
inequality + positive-complement route, computed by the **exact residual-count** — NEVER via an assumed
`O ≤ A` or any external positive-complement hypothesis.

Throughout, with `A := z.1.1`, `Q := A.contractWithStars (starOf G A)`, `B := z.2.1`,
`O := phi4WTriplePrime_recoveredOuter z`, `r := A.retargetEdge (starOf G A)`:

* **Step 1** — `phi4WTriplePrime_inv_A_internalEdges_le_recoveredOuter : A.internalEdges ≤ O.internalEdges`.
  Each `A`-component γ splits: LEFT → γ sits verbatim in `O`; not-LEFT → γ is touched by a UNIQUE owner `δ`,
  and the recovered parent (a component of `O`) contains γ (`touchedComponent_internalEdges_le`).  Closed as a
  multiset INCLUSION by owner uniqueness (`ownerCount`), NEVER double-counting.
* **Step 2** — `phi4WTriplePrime_inv_recoveredOuterResidual z := O.internalEdges - A.internalEdges`, with the
  exact decomposition `A.internalEdges + recoveredOuterResidual z = O.internalEdges` from Step 1.
* **Step 3 (LOAD-BEARING)** — `phi4WTriplePrime_inv_recoveredOuterResidual_map_le_B :
  (recoveredOuterResidual z).map r ≤ B.internalEdges`.  Component-origin dispatch, at the MULTISET/count
  level (never collapsing multiplicity):
    - LEFT edge: lives in `A.internalEdges`, cancelled by the subtraction (Step 2 cancel).
    - RIGHT edge: `recoveredRight`'s RAW `G`-native edge is `r`-FIXED (disjoint from `A`), lands in `δ ≤ B`.
    - FOREST touched-`A` edge: cancelled by the subtraction.
    - FOREST decontracted reconnection edge: by body-610 `delta_internalEdges_eq` the parent-Exact edges
      retarget EXACTLY to `δ.internalEdges` (`parentExactEdges.map r = δ.internalEdges`), landing in `B`.
  No global retarget injectivity is assumed — the only per-`δ` count fact used is the CLEAN body-610 identity
  `δ.internalEdges = parentExactEdges.map r` (derived there from the ambient `EdgeIdsUnique` on `δ`'s support).
* **Step 4** — the cardinal chain: `card residual ≤ card B.internalEdges` (`card_map`, no injectivity),
  `card B.internalEdges < card Q.internalEdges` (`B.IsProperForest`), `card Q.internalEdges = card G.internalEdges
  − card A.internalEdges`, so `card O.internalEdges < card G.internalEdges`.
* **Step 5** — `phi4WTriplePrime_recoveredOuter_internalEdges_card_lt` and
  `phi4WTriplePrime_recoveredOuter_complementEdges_card_pos` (via `Multiset.card_sub` + `omega`).

## HALT compliance
Axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only); ZERO forbidden divergence classes in any
declaration type.  NO assumed `O.internalEdges ≤ A.internalEdges`; the inequality direction is `A ≤ O` and the
positive complement is derived ADDITIVELY (`O = A + residual`, `residual ↦ B`, `B` proper in `Q = G/A`).  NO
external positive-complement hypothesis; NO global retarget injectivity; NO orbit quotient / dedup / global `τ`;
NO `HEq` / `cast`; NO multiplicity collapse (everything count/multiset-level); NO strict cross-presentation star
equality; NO `δ.boundaryEdgeCount = 0`.  NO W‴ membership assembly / `recoveredSplitChoice` / round-trip /
`Equiv` / summand / `sum_bij` / alpha / coassoc (those are body-619+).  No new `class` / `structure` / permanent
`instance`; no `sorry` / `admit` / `native_decide`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

open ResolvedFeynmanSubgraph

variable {G : ResolvedFeynmanGraph}

set_option maxHeartbeats 3200000

/-- The concrete φ⁴ divergence measure family, registered file-locally (providable instance, NO forbidden
class). -/
noncomputable local instance phi4Inst618 : (H : FeynmanGraph) → DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

/-- **body-618 (engine) — `Multiset.map` commutes with a `Finset.sum` of multisets.**  (`Multiset.map r` is an
additive map; re-derived clean by induction, NO forbidden class.) -/
theorem phi4WTriplePrime_map_finset_sum {ι : Type*}
    (r : ResolvedFeynmanEdge → ResolvedFeynmanEdge) (s : Finset ι)
    (f : ι → Multiset ResolvedFeynmanEdge) :
    (∑ x ∈ s, f x).map r = ∑ x ∈ s, (f x).map r := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t ha ih => rw [Finset.sum_insert ha, Multiset.map_add, ih, Finset.sum_insert ha]

/-! ## Step 1 — `A` is fully recovered into `recoveredOuter` (owner-unique multiset inclusion) -/

/-- **body-618 (Step 1, HEADLINE) — `A.internalEdges ≤ O.internalEdges`.**  Every `A`-component γ is either
LEFT (verbatim in `O`) or touched by a UNIQUE owner `δ` (its recovered parent, a component of `O`, contains
γ).  Owner uniqueness (`ownerCount`, on both `A` and `O`, pairwise-disjoint forests) closes it as a multiset
inclusion — NO double counting, NO assumed `O ≤ A`. -/
theorem phi4WTriplePrime_inv_A_internalEdges_le_recoveredOuter
    (z : Phi4WTriplePrimeInverseCodomain G) :
    z.1.1.internalEdges ≤ (phi4WTriplePrime_recoveredOuter z).internalEdges := by
  rw [Multiset.le_iff_count]
  intro e
  by_cases he : e ∈ z.1.1.internalEdges
  · obtain ⟨γ, hγA, heγ⟩ : ∃ γ ∈ z.1.1.elements, e ∈ γ.internalEdges := by
      simp only [ResolvedAdmissibleSubgraph.internalEdges, Multiset.mem_sum] at he; exact he
    have hAcount : Multiset.count e z.1.1.internalEdges = Multiset.count e γ.internalEdges :=
      phi4WTriplePrime_ownerCount hγA heγ
    rw [hAcount]
    by_cases hL : phi4WTriplePrime_inv_isLeftComponent z γ
    · have hγO : γ ∈ (phi4WTriplePrime_recoveredOuter z).elements :=
        phi4WTriplePrime_inv_left_mem_recoveredOuter z hγA hL
      exact (phi4WTriplePrime_ownerCount hγO heγ).ge
    · obtain ⟨δ, hstar⟩ := (phi4WTriplePrime_inv_not_isLeftComponent_iff z γ).mp hL
      have hst : phi4WTriplePrime_inv_isForestImage z δ :=
        ⟨phi4WTriplePrimeCanonicalSupply.starOf G z.1.1 γ, hstar,
          ResolvedAdmissibleSubgraph.mem_starVertices.mpr ⟨γ, hγA, rfl⟩⟩
      have hγTOF : γ ∈ (phi4WTriplePrime_touchedOuterForest z δ).elements := by
        rw [phi4WTriplePrime_touchedOuterForest_elements, Finset.mem_filter]; exact ⟨hγA, hstar⟩
      have hle : γ.internalEdges
          ≤ (phi4WTriplePrime_inv_recoveredParent
              (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hst)).internalEdges :=
        phi4WTriplePrime_inv_touchedComponent_internalEdges_le
          (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hst) hγTOF
      have hparMem : phi4WTriplePrime_inv_recoveredParent
          (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hst)
            ∈ (phi4WTriplePrime_recoveredOuter z).elements := by
        rw [← phi4WTriplePrime_inv_regionComponentOf_eq_parent z hst]
        exact phi4WTriplePrime_inv_regionComponent_mem_recoveredOuter z δ
      have heP : e ∈ (phi4WTriplePrime_inv_recoveredParent
          (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hst)).internalEdges :=
        Multiset.mem_of_le hle heγ
      exact le_trans (Multiset.count_le_of_le e hle) (phi4WTriplePrime_ownerCount hparMem heP).ge
  · rw [Multiset.count_eq_zero_of_notMem he]; exact Nat.zero_le _

/-! ## Step 2 — the inverse residual and its exact decomposition -/

/-- **body-618 (Step 2) — the inverse recovered-outer residual** `O.internalEdges − A.internalEdges`. -/
noncomputable def phi4WTriplePrime_inv_recoveredOuterResidual (z : Phi4WTriplePrimeInverseCodomain G) :
    Multiset ResolvedFeynmanEdge :=
  (phi4WTriplePrime_recoveredOuter z).internalEdges - z.1.1.internalEdges

/-- **body-618 (Step 2) — the exact decomposition** `A.internalEdges + residual = O.internalEdges`. -/
theorem phi4WTriplePrime_inv_A_add_recoveredOuterResidual (z : Phi4WTriplePrimeInverseCodomain G) :
    z.1.1.internalEdges + phi4WTriplePrime_inv_recoveredOuterResidual z
      = (phi4WTriplePrime_recoveredOuter z).internalEdges := by
  rw [phi4WTriplePrime_inv_recoveredOuterResidual,
    add_tsub_cancel_of_le (phi4WTriplePrime_inv_A_internalEdges_le_recoveredOuter z)]

/-! ## Step 3 — LOAD-BEARING residual transport `residual.map r ≤ B.internalEdges` -/

/-- The total touched-`A` internal edges across all quotient components (star-free `δ`s contribute nothing —
their touched outer forests are empty). -/
noncomputable def phi4WTriplePrime_inv_touchedTotal (z : Phi4WTriplePrimeInverseCodomain G) :
    Multiset ResolvedFeynmanEdge :=
  ∑ δ ∈ z.2.1.elements.attach, (phi4WTriplePrime_touchedOuterForest z δ).internalEdges

/-- **body-618 (Step 3, per-`δ` map identity) — the recovered quotient-region component's edges, retargeted.**
For a star-free `δ` the recovered right component is `G`-native so `r` FIXES it (lands in `δ.internalEdges`,
touched forest empty); for a star-touching `δ` the recovered parent's edges split (body-610) as touched-forest
+ parent-Exact, and the parent-Exact edges retarget EXACTLY to `δ.internalEdges` (`delta_internalEdges_eq`). -/
theorem phi4WTriplePrime_inv_regionComponent_map_r_decomp (z : Phi4WTriplePrimeInverseCodomain G)
    (δ : {x // x ∈ z.2.1.elements}) :
    (phi4WTriplePrime_inv_regionComponentOf z δ).internalEdges.map
        (z.1.1.retargetEdge (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1))
      = δ.1.internalEdges
        + (phi4WTriplePrime_touchedOuterForest z δ).internalEdges.map
            (z.1.1.retargetEdge (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1)) := by
  by_cases hst : phi4WTriplePrime_inv_isForestImage z δ
  · rw [phi4WTriplePrime_inv_regionComponentOf_eq_parent z hst,
      phi4WTriplePrime_inv_recoveredParent_internalEdges_decomp
        (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hst),
      Multiset.map_add,
      ← phi4WTriplePrime_inv_delta_internalEdges_eq
        (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hst),
      add_comm]
  · rw [phi4WTriplePrime_inv_regionComponentOf_eq_right z hst,
      phi4WTriplePrime_recoveredRight_internalEdges z hst]
    have hTT0 : (phi4WTriplePrime_touchedOuterForest z δ).internalEdges = 0 := by
      simp only [ResolvedAdmissibleSubgraph.internalEdges,
        phi4WTriplePrime_inv_touchedOuterForest_elements_empty_of_free z hst, Finset.sum_empty]
    rw [hTT0, Multiset.map_zero, add_zero]
    -- star-free δ: r FIXES every δ-edge (disjoint from A)
    conv_rhs => rw [← Multiset.map_id δ.1.internalEdges]
    apply Multiset.map_congr rfl
    intro e he
    obtain ⟨hs, ht⟩ := δ.1.edges_supported e he
    have hdisj : Disjoint δ.1.vertices z.1.1.vertices :=
      phi4WTriplePrime_inv_recoveredRight_disjoint z hst
    show z.1.1.retargetEdge (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1) e = id e
    unfold ResolvedAdmissibleSubgraph.retargetEdge ResolvedFeynmanEdge.retarget
    rw [z.1.1.retargetVertex_of_not_mem _ (Finset.disjoint_left.mp hdisj hs),
      z.1.1.retargetVertex_of_not_mem _ (Finset.disjoint_left.mp hdisj ht)]
    rfl

/-- **body-618 (Step 3, quotient-region transport) — the recovered quotient-region forest's edges retarget to
`B.internalEdges + touchedTotal.map r`.**  A per-`δ` sum over `B.elements` (`regionComponentOf` injective, NO
dedup); each `δ` contributes exactly `δ.internalEdges` (which sum to `B.internalEdges`) plus its touched-forest
edges. -/
theorem phi4WTriplePrime_inv_invQuotientForest_map (z : Phi4WTriplePrimeInverseCodomain G) :
    (phi4WTriplePrime_inv_quotientForest z).internalEdges.map
        (z.1.1.retargetEdge (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1))
      = z.2.1.internalEdges
        + (phi4WTriplePrime_inv_touchedTotal z).map
            (z.1.1.retargetEdge (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1)) := by
  have hsum : (phi4WTriplePrime_inv_quotientForest z).internalEdges
      = ∑ δ ∈ z.2.1.elements.attach, (phi4WTriplePrime_inv_regionComponentOf z δ).internalEdges := by
    simp only [ResolvedAdmissibleSubgraph.internalEdges, phi4WTriplePrime_inv_quotientForest,
      ResolvedAdmissibleSubgraph.ofElements_elements]
    rw [Finset.sum_image (fun x _ y _ h => phi4WTriplePrime_inv_regionComponentOf_injective z h)]
  rw [hsum, phi4WTriplePrime_map_finset_sum,
    Finset.sum_congr rfl (fun δ _ => phi4WTriplePrime_inv_regionComponent_map_r_decomp z δ),
    Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_attach z.2.1.elements (fun γ => γ.internalEdges)]; rfl
  · rw [phi4WTriplePrime_inv_touchedTotal, phi4WTriplePrime_map_finset_sum]

/-- **body-618 (Step 3) — `leftForest.internalEdges + touchedTotal ≤ A.internalEdges`.**  The LEFT components
and the (owner-unique) touched components are DISJOINT sub-collections of `A`; owner uniqueness (`ownerCount`,
plus `touchedOuter_unique`) closes it at the count level, NO double counting. -/
theorem phi4WTriplePrime_inv_leftForest_add_touchedTotal_le (z : Phi4WTriplePrimeInverseCodomain G) :
    (phi4WTriplePrime_inv_leftForest z).internalEdges + phi4WTriplePrime_inv_touchedTotal z
      ≤ z.1.1.internalEdges := by
  -- component bounds reused throughout
  have hlfle : (phi4WTriplePrime_inv_leftForest z).internalEdges ≤ z.1.1.internalEdges := by
    refine phi4WTriplePrime_internalEdges_le_of_components_le (phi4WTriplePrime_inv_leftForest z)
      (fun c hc => ?_)
    rw [phi4WTriplePrime_inv_leftForest, ResolvedAdmissibleSubgraph.filterElements_elements,
      Finset.mem_filter] at hc
    exact Finset.single_le_sum (f := fun x : ResolvedFeynmanSubgraph G => x.internalEdges)
      (fun i _ => Multiset.zero_le _) hc.1
  have htfle : ∀ δ : {x // x ∈ z.2.1.elements},
      (phi4WTriplePrime_touchedOuterForest z δ).internalEdges ≤ z.1.1.internalEdges := by
    intro δ
    refine phi4WTriplePrime_internalEdges_le_of_components_le (phi4WTriplePrime_touchedOuterForest z δ)
      (fun c hc => ?_)
    exact Finset.single_le_sum (f := fun x : ResolvedFeynmanSubgraph G => x.internalEdges)
      (fun i _ => Multiset.zero_le _) (phi4WTriplePrime_inv_touchedForest_subset_A hc)
  rw [Multiset.le_iff_count]
  intro e
  rw [Multiset.count_add]
  by_cases hex : ∃ γ ∈ z.1.1.elements, e ∈ γ.internalEdges
  · obtain ⟨γ, hγA, heγ⟩ := hex
    have hAcount : Multiset.count e z.1.1.internalEdges = Multiset.count e γ.internalEdges :=
      phi4WTriplePrime_ownerCount hγA heγ
    -- owner uniqueness helper: any component of A carrying e is γ
    have hownerγ : ∀ γ' ∈ z.1.1.elements, e ∈ γ'.internalEdges → γ' = γ := by
      intro γ' hγ'A heγ'
      by_contra hne
      exact Finset.disjoint_left.mp (z.1.1.pairwiseDisjoint hγ'A hγA hne)
        (γ'.edges_supported e heγ').1 (γ.edges_supported e heγ).1
    by_cases hL : phi4WTriplePrime_inv_isLeftComponent z γ
    · have hγLmem : γ ∈ (phi4WTriplePrime_inv_leftForest z).elements := by
        rw [phi4WTriplePrime_inv_leftForest, ResolvedAdmissibleSubgraph.filterElements_elements,
          Finset.mem_filter]
        exact ⟨hγA, hL⟩
      have hLcount : Multiset.count e (phi4WTriplePrime_inv_leftForest z).internalEdges
          = Multiset.count e γ.internalEdges := phi4WTriplePrime_ownerCount hγLmem heγ
      have hTTzero : Multiset.count e (phi4WTriplePrime_inv_touchedTotal z) = 0 := by
        rw [phi4WTriplePrime_inv_touchedTotal, Multiset.count_sum']
        refine Finset.sum_eq_zero (fun δ _ => ?_)
        rw [Multiset.count_eq_zero]
        intro hmem
        obtain ⟨γ', hγ'T, heγ'⟩ : ∃ γ' ∈ (phi4WTriplePrime_touchedOuterForest z δ).elements,
            e ∈ γ'.internalEdges := by
          simp only [ResolvedAdmissibleSubgraph.internalEdges, Multiset.mem_sum] at hmem; exact hmem
        have hγ'A : γ' ∈ z.1.1.elements := phi4WTriplePrime_inv_touchedForest_subset_A hγ'T
        have := hownerγ γ' hγ'A heγ'
        subst this
        rw [phi4WTriplePrime_touchedOuterForest_elements, Finset.mem_filter] at hγ'T
        exact hL δ hγ'T.2
      rw [hLcount, hTTzero, hAcount, Nat.add_zero]
    · obtain ⟨δ₀, hstar₀⟩ := (phi4WTriplePrime_inv_not_isLeftComponent_iff z γ).mp hL
      have hγT₀ : γ ∈ (phi4WTriplePrime_touchedOuterForest z δ₀).elements := by
        rw [phi4WTriplePrime_touchedOuterForest_elements, Finset.mem_filter]; exact ⟨hγA, hstar₀⟩
      have hLzero : Multiset.count e (phi4WTriplePrime_inv_leftForest z).internalEdges = 0 := by
        rw [Multiset.count_eq_zero]
        intro hmem
        obtain ⟨γ', hγ'L, heγ'⟩ : ∃ γ' ∈ (phi4WTriplePrime_inv_leftForest z).elements,
            e ∈ γ'.internalEdges := by
          simp only [ResolvedAdmissibleSubgraph.internalEdges, Multiset.mem_sum] at hmem; exact hmem
        rw [phi4WTriplePrime_inv_leftForest, ResolvedAdmissibleSubgraph.filterElements_elements,
          Finset.mem_filter] at hγ'L
        have := hownerγ γ' hγ'L.1 heγ'
        subst this
        exact hL hγ'L.2
      have hTTcount : Multiset.count e (phi4WTriplePrime_inv_touchedTotal z)
          = Multiset.count e γ.internalEdges := by
        rw [phi4WTriplePrime_inv_touchedTotal, Multiset.count_sum',
          Finset.sum_eq_single δ₀
            (fun δ _ hne => by
              rw [Multiset.count_eq_zero]
              intro hmem
              obtain ⟨γ', hγ'T, heγ'⟩ : ∃ γ' ∈ (phi4WTriplePrime_touchedOuterForest z δ).elements,
                  e ∈ γ'.internalEdges := by
                simp only [ResolvedAdmissibleSubgraph.internalEdges, Multiset.mem_sum] at hmem
                exact hmem
              have hγ'A : γ' ∈ z.1.1.elements := phi4WTriplePrime_inv_touchedForest_subset_A hγ'T
              have hγ'γ := hownerγ γ' hγ'A heγ'
              subst hγ'γ
              rw [phi4WTriplePrime_touchedOuterForest_elements, Finset.mem_filter] at hγ'T
              exact hne (phi4WTriplePrime_touchedOuter_unique z hγA hγ'T.2 hstar₀))
            (fun h => absurd (Finset.mem_attach _ δ₀) h)]
        exact phi4WTriplePrime_ownerCount hγT₀ heγ
      rw [hLzero, hTTcount, hAcount, Nat.zero_add]
  · push_neg at hex
    have hA0 : Multiset.count e z.1.1.internalEdges = 0 := by
      rw [Multiset.count_eq_zero]
      intro he
      obtain ⟨γ, hγA, heγ⟩ : ∃ γ ∈ z.1.1.elements, e ∈ γ.internalEdges := by
        simp only [ResolvedAdmissibleSubgraph.internalEdges, Multiset.mem_sum] at he; exact he
      exact hex γ hγA heγ
    have hLz : Multiset.count e (phi4WTriplePrime_inv_leftForest z).internalEdges = 0 :=
      Nat.le_zero.mp (hA0 ▸ Multiset.count_le_of_le e hlfle)
    have hTTz : Multiset.count e (phi4WTriplePrime_inv_touchedTotal z) = 0 := by
      rw [phi4WTriplePrime_inv_touchedTotal, Multiset.count_sum']
      refine Finset.sum_eq_zero (fun δ _ => ?_)
      exact Nat.le_zero.mp (hA0 ▸ Multiset.count_le_of_le e (htfle δ))
    rw [hLz, hTTz, hA0]

/-- **body-618 (Step 3, `O`-edge split) — `O.internalEdges = leftForest.internalEdges +
invQuotientForest.internalEdges`.**  `O = leftForest ∪ invQuotientForest` with DISJOINT element sets (a LEFT
component is vertex-disjoint from every recovered quotient-region component). -/
theorem phi4WTriplePrime_inv_recoveredOuter_internalEdges_split
    (z : Phi4WTriplePrimeInverseCodomain G) :
    (phi4WTriplePrime_recoveredOuter z).internalEdges
      = (phi4WTriplePrime_inv_leftForest z).internalEdges
        + (phi4WTriplePrime_inv_quotientForest z).internalEdges := by
  have hdisj : Disjoint (phi4WTriplePrime_inv_leftForest z).elements
      (phi4WTriplePrime_inv_quotientForest z).elements := by
    rw [Finset.disjoint_left]
    intro c hcL hcQ
    rw [phi4WTriplePrime_inv_leftForest, ResolvedAdmissibleSubgraph.filterElements_elements,
      Finset.mem_filter] at hcL
    rw [phi4WTriplePrime_inv_quotientForest, ResolvedAdmissibleSubgraph.ofElements_elements,
      Finset.mem_image] at hcQ
    obtain ⟨δ, -, hceq⟩ := hcQ
    have hdd := phi4WTriplePrime_inv_left_regionComponent_disjoint z hcL.1 hcL.2 δ
    rw [hceq] at hdd
    obtain ⟨v, hv⟩ := Finset.card_pos.mp ((phi4WTriplePrime_inv_A_isProperForest z).2.1 c hcL.1)
    exact Finset.disjoint_left.mp hdd hv hv
  -- element-set split (rfl on `union`), used only for the instance-agnostic `Finset.mem_union`
  have hOcases : ∀ c ∈ (phi4WTriplePrime_recoveredOuter z).elements,
      c ∈ (phi4WTriplePrime_inv_leftForest z).elements
        ∨ c ∈ (phi4WTriplePrime_inv_quotientForest z).elements := by
    intro c hc
    have hc' := hc
    simp only [phi4WTriplePrime_recoveredOuter, ResolvedAdmissibleSubgraph.union_elements,
      Finset.mem_union] at hc'
    exact hc'
  have hLmem : ∀ c ∈ (phi4WTriplePrime_inv_leftForest z).elements,
      c ∈ (phi4WTriplePrime_recoveredOuter z).elements := fun c hc =>
    (phi4WTriplePrime_mem_recoveredOuter_elements z).mpr (Or.inl (by
      rw [phi4WTriplePrime_inv_leftForest, ResolvedAdmissibleSubgraph.filterElements_elements,
        Finset.mem_filter] at hc
      exact hc))
  have hQmem : ∀ c ∈ (phi4WTriplePrime_inv_quotientForest z).elements,
      c ∈ (phi4WTriplePrime_recoveredOuter z).elements := fun c hc =>
    (phi4WTriplePrime_mem_recoveredOuter_elements z).mpr (Or.inr (by
      rw [phi4WTriplePrime_inv_quotientForest, ResolvedAdmissibleSubgraph.ofElements_elements,
        Finset.mem_image] at hc
      obtain ⟨δ, -, hceq⟩ := hc
      exact ⟨δ, hceq⟩))
  refine Multiset.ext.mpr (fun e => ?_)
  rw [Multiset.count_add]
  by_cases hex : ∃ c ∈ (phi4WTriplePrime_recoveredOuter z).elements, e ∈ c.internalEdges
  · obtain ⟨c₀, hc₀O, hec₀⟩ := hex
    have hOc : Multiset.count e (phi4WTriplePrime_recoveredOuter z).internalEdges
        = Multiset.count e c₀.internalEdges := phi4WTriplePrime_ownerCount hc₀O hec₀
    have huniq : ∀ c ∈ (phi4WTriplePrime_recoveredOuter z).elements, e ∈ c.internalEdges → c = c₀ := by
      intro c hcO hec
      by_contra hne
      exact Finset.disjoint_left.mp ((phi4WTriplePrime_recoveredOuter z).pairwiseDisjoint hcO hc₀O hne)
        (c.edges_supported e hec).1 (c₀.edges_supported e hec₀).1
    rcases hOcases c₀ hc₀O with hc₀L | hc₀Q
    · have hlfc : Multiset.count e (phi4WTriplePrime_inv_leftForest z).internalEdges
          = Multiset.count e c₀.internalEdges := phi4WTriplePrime_ownerCount hc₀L hec₀
      have hqf0 : Multiset.count e (phi4WTriplePrime_inv_quotientForest z).internalEdges = 0 := by
        rw [Multiset.count_eq_zero]
        intro hmem
        obtain ⟨c₁, hc₁Q, hec₁⟩ : ∃ c₁ ∈ (phi4WTriplePrime_inv_quotientForest z).elements,
            e ∈ c₁.internalEdges := by
          simp only [ResolvedAdmissibleSubgraph.internalEdges, Multiset.mem_sum] at hmem; exact hmem
        have := huniq c₁ (hQmem c₁ hc₁Q) hec₁
        exact Finset.disjoint_left.mp hdisj hc₀L (this ▸ hc₁Q)
      rw [hOc, hlfc, hqf0, Nat.add_zero]
    · have hqfc : Multiset.count e (phi4WTriplePrime_inv_quotientForest z).internalEdges
          = Multiset.count e c₀.internalEdges := phi4WTriplePrime_ownerCount hc₀Q hec₀
      have hlf0 : Multiset.count e (phi4WTriplePrime_inv_leftForest z).internalEdges = 0 := by
        rw [Multiset.count_eq_zero]
        intro hmem
        obtain ⟨c₁, hc₁L, hec₁⟩ : ∃ c₁ ∈ (phi4WTriplePrime_inv_leftForest z).elements,
            e ∈ c₁.internalEdges := by
          simp only [ResolvedAdmissibleSubgraph.internalEdges, Multiset.mem_sum] at hmem; exact hmem
        have := huniq c₁ (hLmem c₁ hc₁L) hec₁
        exact Finset.disjoint_left.mp hdisj hc₁L (this ▸ hc₀Q)
      rw [hOc, hqfc, hlf0, Nat.zero_add]
  · push_neg at hex
    have hO0 : Multiset.count e (phi4WTriplePrime_recoveredOuter z).internalEdges = 0 := by
      rw [Multiset.count_eq_zero]
      intro hmem
      obtain ⟨c, hcO, hec⟩ : ∃ c ∈ (phi4WTriplePrime_recoveredOuter z).elements, e ∈ c.internalEdges := by
        simp only [ResolvedAdmissibleSubgraph.internalEdges, Multiset.mem_sum] at hmem; exact hmem
      exact hex c hcO hec
    have hlf0 : Multiset.count e (phi4WTriplePrime_inv_leftForest z).internalEdges = 0 := by
      rw [Multiset.count_eq_zero]
      intro hmem
      obtain ⟨c, hcL, hec⟩ : ∃ c ∈ (phi4WTriplePrime_inv_leftForest z).elements, e ∈ c.internalEdges := by
        simp only [ResolvedAdmissibleSubgraph.internalEdges, Multiset.mem_sum] at hmem; exact hmem
      exact hex c (hLmem c hcL) hec
    have hqf0 : Multiset.count e (phi4WTriplePrime_inv_quotientForest z).internalEdges = 0 := by
      rw [Multiset.count_eq_zero]
      intro hmem
      obtain ⟨c, hcQ, hec⟩ : ∃ c ∈ (phi4WTriplePrime_inv_quotientForest z).elements, e ∈ c.internalEdges := by
        simp only [ResolvedAdmissibleSubgraph.internalEdges, Multiset.mem_sum] at hmem; exact hmem
      exact hex c (hQmem c hcQ) hec
    rw [hO0, hlf0, hqf0]

/-- **body-618 (Step 3, master) — `O.internalEdges.map r ≤ B.internalEdges + A.internalEdges.map r`.**  The
LEFT-and-touched sub-collection of `A` (mapped) exactly absorbs the extra touched edges of the quotient
region; the quotient region supplies `B` (per-`δ` transport). -/
theorem phi4WTriplePrime_recoveredOuter_internalEdges_map_le
    (z : Phi4WTriplePrimeInverseCodomain G) :
    (phi4WTriplePrime_recoveredOuter z).internalEdges.map
        (z.1.1.retargetEdge (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1))
      ≤ z.2.1.internalEdges
        + z.1.1.internalEdges.map (z.1.1.retargetEdge (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1)) := by
  rw [phi4WTriplePrime_inv_recoveredOuter_internalEdges_split z, Multiset.map_add,
    phi4WTriplePrime_inv_invQuotientForest_map z, add_left_comm, ← Multiset.map_add]
  exact add_le_add (le_refl _)
    (Multiset.map_le_map (phi4WTriplePrime_inv_leftForest_add_touchedTotal_le z))

/-- **body-618 (Step 3, HEADLINE) — the LOAD-BEARING residual transport** `residual.map r ≤ B.internalEdges`.
From the master bound + the exact residual decomposition (Step 2), cancelling `A.internalEdges.map r` on the
right (multiset cancellation — NO injectivity needed). -/
theorem phi4WTriplePrime_inv_recoveredOuterResidual_map_le_B
    (z : Phi4WTriplePrimeInverseCodomain G) :
    (phi4WTriplePrime_inv_recoveredOuterResidual z).map
        (z.1.1.retargetEdge (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1))
      ≤ z.2.1.internalEdges := by
  have hcancel : (phi4WTriplePrime_inv_recoveredOuterResidual z).map
        (z.1.1.retargetEdge (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1))
      + z.1.1.internalEdges.map (z.1.1.retargetEdge (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1))
      = (phi4WTriplePrime_recoveredOuter z).internalEdges.map
          (z.1.1.retargetEdge (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1)) := by
    rw [← Multiset.map_add, add_comm, phi4WTriplePrime_inv_A_add_recoveredOuterResidual z]
  have hle : (phi4WTriplePrime_inv_recoveredOuterResidual z).map
        (z.1.1.retargetEdge (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1))
      + z.1.1.internalEdges.map (z.1.1.retargetEdge (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1))
      ≤ z.2.1.internalEdges
        + z.1.1.internalEdges.map (z.1.1.retargetEdge (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1)) := by
    rw [hcancel]
    exact phi4WTriplePrime_recoveredOuter_internalEdges_map_le z
  exact le_of_add_le_add_right hle

/-! ## Steps 4–5 — cardinal chain + the positive complement -/

/-- **body-618 (Step 5, HEADLINE) — `O.internalEdges.card < G.internalEdges.card`.**  `card O = card A + card
residual ≤ card A + card B < card A + card Q = card A + (card G − card A) = card G`, using `card residual ≤
card B` (Step 3 + `card_map`), `card B < card Q` (`B.IsProperForest`), and `card Q = card G − card A`. -/
theorem phi4WTriplePrime_recoveredOuter_internalEdges_card_lt
    (z : Phi4WTriplePrimeInverseCodomain G) :
    (phi4WTriplePrime_recoveredOuter z).internalEdges.card < G.internalEdges.card := by
  have hAG : z.1.1.internalEdges ≤ G.internalEdges :=
    phi4WTriplePrime_internalEdges_le_of_components_le z.1.1 (fun c _ => c.internalEdges_le)
  have hBle : z.2.1.internalEdges
      ≤ (z.1.1.contractWithStars (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1)).internalEdges :=
    phi4WTriplePrime_internalEdges_le_of_components_le z.2.1 (fun c _ => c.internalEdges_le)
  -- Step 4a: card residual ≤ card B
  have hres_card : (phi4WTriplePrime_inv_recoveredOuterResidual z).card ≤ z.2.1.internalEdges.card := by
    have h := Multiset.card_le_card (phi4WTriplePrime_inv_recoveredOuterResidual_map_le_B z)
    rwa [Multiset.card_map] at h
  -- Step 4b: card B < card Q
  have hBpos : 0 < z.2.1.complementEdges.card :=
    ResolvedAdmissibleSubgraph.complementEdges_card_pos_of_isProperForest
      (phi4WTriplePrime_inv_B_isProperForest z)
  have hBcomp : z.2.1.complementEdges.card
      = (z.1.1.contractWithStars (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1)).internalEdges.card
        - z.2.1.internalEdges.card := by
    show ((z.1.1.contractWithStars (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1)).internalEdges
      - z.2.1.internalEdges).card = _
    rw [Multiset.card_sub hBle]
  -- Step 4c: card Q = card G − card A
  have hQcard : (z.1.1.contractWithStars (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1)).internalEdges.card
      = G.internalEdges.card - z.1.1.internalEdges.card := by
    rw [ResolvedAdmissibleSubgraph.contractWithStars_internalEdges, Multiset.card_map]
    show ((G.internalEdges - z.1.1.internalEdges)).card = _
    rw [Multiset.card_sub hAG]
  -- Step 4d: card O = card A + card residual
  have hOcard : (phi4WTriplePrime_recoveredOuter z).internalEdges.card
      = z.1.1.internalEdges.card + (phi4WTriplePrime_inv_recoveredOuterResidual z).card := by
    rw [← phi4WTriplePrime_inv_A_add_recoveredOuterResidual z, Multiset.card_add]
  have hAcard : z.1.1.internalEdges.card ≤ G.internalEdges.card := Multiset.card_le_card hAG
  omega

/-- **body-618 (Step 5, TARGET) — the recovered outer forest has POSITIVE complement in `G`** (the sole missing
`IsProperForest` conjunct for `O`'s W‴ membership, discharged by the exact residual count — NO external
positive-complement hypothesis). -/
theorem phi4WTriplePrime_recoveredOuter_complementEdges_card_pos
    (z : Phi4WTriplePrimeInverseCodomain G) :
    0 < (phi4WTriplePrime_recoveredOuter z).complementEdges.card := by
  have hOG : (phi4WTriplePrime_recoveredOuter z).internalEdges ≤ G.internalEdges :=
    phi4WTriplePrime_internalEdges_le_of_components_le (phi4WTriplePrime_recoveredOuter z)
      (fun c _ => c.internalEdges_le)
  have hlt := phi4WTriplePrime_recoveredOuter_internalEdges_card_lt z
  have hcard : (phi4WTriplePrime_recoveredOuter z).complementEdges.card
      = G.internalEdges.card - (phi4WTriplePrime_recoveredOuter z).internalEdges.card := by
    show (G.internalEdges - (phi4WTriplePrime_recoveredOuter z).internalEdges).card = _
    rw [Multiset.card_sub hOG]
  omega

end GaugeGeometry.QFT.Combinatorial
