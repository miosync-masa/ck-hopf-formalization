import GaugeGeometry.QFT.HopfAlgebra.Phi4WTriplePrimeRecoveredInverse

/-!
# QFT-R1-body-620 — forward-after-inverse FOREST reconciliation (ambient-free bcrg equality)

Two prior 620 attempts correctly STOPPED at the ILL-TYPED raw cross-ambient subgraph equality
`remnantComponent o = δ.1` (LHS in `ResolvedFeynmanSubgraph (selectedOuterContractGraph s)`, RHS in
`ResolvedFeynmanSubgraph (z.1.1.contractWithStars …)`; the ambient identification
`selectedOuter (recoveredSplitChoice z) = z.1.1` is only PROPOSITIONAL).  The fix: the 620 headline is now
the AMBIENT-FREE **bcrg** (`boundaryCompletedResolvedGraph`) equality — both sides are plain
`ResolvedFeynmanGraph`, so it is a genuine homogeneous raw `Eq`.  The dependent second-component bridging
is DEFERRED to body-621's `Sigma.ext`.

* **Step 1** — canonical inverse data `I / γ / B / s` for a star-touching target `δ`.
* **Step 2** — the 614 FOREST exact payload with owner fixed to `γ := recoveredParent I` FROM THE START:
  `recoveredChoice z ⟨γ, hγ⟩ = Sum.inr ⟨B, mem⟩`.  `Exists.choose` is pinned via owner determinacy +
  component injectivity + proof irrelevance; the `▸` transport in `recoveredForestTag` collapses under a
  `subst` of the choose (Prop-level definitional proof irrelevance) — NO `HEq` / `cast` / `Eq.ndrec`.
* **Step 3** — `phi4WTriplePrime_recoveredForwardOccurrence z hδ`, aligning the forward `o` and the
  inverse `O` ownership.
* **Step 4** — outer raw equality `selectedOuter (recoveredSplitChoice z) = z.1.1` (via a clean local
  element-set ext — the library `ResolvedAdmissibleSubgraph.ext_elements` carries a forbidden
  `[IsAmbientInvariantDivergence]` binder and is NOT consumed).  Identifies the ambient PROPOSITIONALLY only.
* **Step 5** — correcting-permutation action agreement on the VISIBLE SUPPORT (survivors + local stars),
  NEVER `remnantTau o = reconTau O`; fed through `Multiset.map_congr` / `Finset.image_congr` to compare the
  two mapped local-contract graphs.
* **Step 6 (SOLE HEADLINE)** — compose body-604 `remnant_contractTwice` with body-616 `correctedForestGraph_eq`,
  bridged by Step 5:
  `(remnantComponent (recoveredForwardOccurrence z δ hδ)).bcrg = δ.1.bcrg` — a homogeneous raw `Eq` between
  two `ResolvedFeynmanGraph`s (ID / multiplicity / sector preserving).

## HALT compliance
Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); ZERO forbidden divergence classes in any type.
NO `HEq` / `cast` / `Eq.ndrec` / hand-written motive transport; NO `remnantTau = reconTau`; NO global `τ`;
NO ill-typed raw-subgraph statement (`remnantComponent o = δ.1` / `= inv_correctedForestComponent O`);
NO `Sigma.ext` (body-621); NO whole `Equiv` / summand / `sum_bij` / alpha / coassoc; NO polluted machinery.
`recoveredForwardOccurrence` is a `def` (not a structure).  No `sorry` / `admit` / `native_decide`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

open ResolvedFeynmanSubgraph

variable {G : ResolvedFeynmanGraph}

set_option maxHeartbeats 3200000

/-- The concrete φ⁴ divergence measure family, registered file-locally (providable instance, NO forbidden
class). -/
noncomputable local instance phi4Inst620 : (H : FeynmanGraph) → DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

/-! ## Step 2a — the recovered forest tag transport collapse (proof-irrelevance `subst`) -/

/-- **body-620 (Step 2a) — the recovered-forest-tag transport collapses.**  For two star-touching targets
`d`, `δ` whose recovered parents coincide, the `Eq.rec` transport of the recovered inner W‴ forest at `d`
onto the recovered inner W‴ forest at `δ` is the identity.  Proof: owner determinacy + component
injectivity pin `d = δ`; after `subst`, the two `ForestDecontractionInput`s (a `Prop`) are DEFINITIONALLY
proof-irrelevant, so the recovered parents and inner forests are defeq and the transport reduces to `rfl`.
NO `HEq` / `cast`. -/
theorem phi4WTriplePrime_recoveredForestTag_transport
    (z : Phi4WTriplePrimeInverseCodomain G)
    {δ : {x // x ∈ z.2.1.elements}} (hδ : phi4WTriplePrime_inv_isForestImage z δ)
    {d : {x // x ∈ z.2.1.elements}} (hst_d : phi4WTriplePrime_inv_isForestImage z d)
    (heq_d : phi4WTriplePrime_inv_recoveredParent
              (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hst_d)
            = phi4WTriplePrime_inv_recoveredParent
              (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδ)) :
    heq_d ▸ (⟨phi4WTriplePrime_inv_recoveredInnerForest
                (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hst_d)
                (phi4WTriplePrime_inv_innerForest_CD_proof
                  (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hst_d)),
              phi4WTriplePrime_inv_recoveredInnerForest_mem_proof
                (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hst_d)⟩
             : (phi4WTriplePrimeCanonicalSupply.summandSupply
                 (phi4WTriplePrime_inv_recoveredParent
                   (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hst_d)).boundaryCompletedResolvedGraph).ForestIdx)
      = ⟨phi4WTriplePrime_inv_recoveredInnerForest
            (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδ)
            (phi4WTriplePrime_inv_innerForest_CD_proof
              (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδ)),
          phi4WTriplePrime_inv_recoveredInnerForest_mem_proof
            (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδ)⟩ := by
  have hdδ : d = δ := by
    apply phi4WTriplePrime_inv_regionComponentOf_injective z
    rw [phi4WTriplePrime_inv_regionComponentOf_eq_parent z hst_d,
        phi4WTriplePrime_inv_regionComponentOf_eq_parent z hδ]
    exact heq_d
  subst hdδ
  rfl

/-! ## Step 2b — the 614 FOREST exact payload (owner fixed to `γ := recoveredParent I`) -/

/-- **body-620 (Step 2b) — the recovered choice at a recovered-parent owner is the recovered inner W‴
forest (EXACT `Sum.inr` payload).**  Owner is `γ := recoveredParent I` FROM THE START (so both sides are
well-typed in `(summandSupply γ.bcrg).ForestIdx`).  `Exists.choose` is pinned to `δ` via
`regionComponentOf_injective`, and the tag transport is collapsed by Step 2a. -/
theorem phi4WTriplePrime_recoveredChoice_forest_value
    (z : Phi4WTriplePrimeInverseCodomain G)
    {δ : {x // x ∈ z.2.1.elements}} (hδ : phi4WTriplePrime_inv_isForestImage z δ)
    (hγ : phi4WTriplePrime_inv_recoveredParent
            (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδ)
          ∈ (phi4WTriplePrime_recoveredOuter z).elements) :
    phi4WTriplePrime_recoveredChoice z
        ⟨phi4WTriplePrime_inv_recoveredParent
            (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδ), hγ⟩
        (Finset.mem_attach _ _)
      = Sum.inr ⟨phi4WTriplePrime_inv_recoveredInnerForest
            (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδ)
            (phi4WTriplePrime_inv_innerForest_CD_proof
              (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδ)),
          phi4WTriplePrime_inv_recoveredInnerForest_mem_proof
            (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδ)⟩ := by
  unfold phi4WTriplePrime_recoveredChoice
  have hq : ∃ d : {x // x ∈ z.2.1.elements},
      phi4WTriplePrime_inv_regionComponentOf z d
        = phi4WTriplePrime_inv_recoveredParent
            (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδ) :=
    ⟨δ, phi4WTriplePrime_inv_regionComponentOf_eq_parent z hδ⟩
  rw [dif_pos hq]
  have hchoose : hq.choose = δ :=
    phi4WTriplePrime_inv_regionComponentOf_injective z
      (hq.choose_spec.trans (phi4WTriplePrime_inv_regionComponentOf_eq_parent z hδ).symm)
  have hst : phi4WTriplePrime_inv_isForestImage z hq.choose := by rw [hchoose]; exact hδ
  rw [dif_pos hst]
  refine congrArg Sum.inr ?_
  unfold phi4WTriplePrime_recoveredForestTag
  exact phi4WTriplePrime_recoveredForestTag_transport z hδ hst _

/-! ## Step 3 — the canonical forward occurrence -/

/-- **body-620 (Step 3) — the canonical forward FOREST occurrence** on `s := recoveredSplitChoice z`, keyed
on the star-touching witness `(z, δ, hδ)`.  Owner `γ := recoveredParent I`, inner forest `B :=
recoveredInnerForest I`, and `hchoice` supplied by Step 2b.  Aligns the forward `o` with the inverse `O`. -/
noncomputable def phi4WTriplePrime_recoveredForwardOccurrence
    (z : Phi4WTriplePrimeInverseCodomain G)
    {δ : {x // x ∈ z.2.1.elements}} (hδ : phi4WTriplePrime_inv_isForestImage z δ) :
    Phi4WTriplePrime_ForestChoiceOccurrence (phi4WTriplePrime_recoveredSplitChoice z) where
  γ := ⟨phi4WTriplePrime_inv_recoveredParent
          (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδ),
        (phi4WTriplePrime_inv_regionComponentOf_eq_parent z hδ)
          ▸ phi4WTriplePrime_inv_regionComponent_mem_recoveredOuter z δ⟩
  B := ⟨phi4WTriplePrime_inv_recoveredInnerForest
          (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδ)
          (phi4WTriplePrime_inv_innerForest_CD_proof
            (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδ)),
        phi4WTriplePrime_inv_recoveredInnerForest_mem_proof
          (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδ)⟩
  hchoice := phi4WTriplePrime_recoveredChoice_forest_value z hδ _

/-! ## Step 4 — the outer raw equality `selectedOuter (recoveredSplitChoice z) = z.1.1` -/

/-- **body-620 (Step 4a) — the promoted set at a recovered-parent forest owner is the touched outer
forest.**  Evaluates the recovered choice via Step 2b (`Sum.inr` of the recovered inner W‴ forest), then
promotes back via body-609 `promotion_recovery`. -/
theorem phi4WTriplePrime_promotedElemsAt_forestOwner
    (z : Phi4WTriplePrimeInverseCodomain G)
    {δ : {x // x ∈ z.2.1.elements}} (hδ : phi4WTriplePrime_inv_isForestImage z δ)
    (hmem : phi4WTriplePrime_inv_recoveredParent
              (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδ)
            ∈ (phi4WTriplePrime_recoveredSplitChoice z).outer.elements) :
    phi4WTriplePrime_promotedElemsAt (phi4WTriplePrime_recoveredSplitChoice z)
        ⟨phi4WTriplePrime_inv_recoveredParent
          (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδ), hmem⟩
      = (phi4WTriplePrime_touchedOuterForest z δ).elements := by
  unfold phi4WTriplePrime_promotedElemsAt
  rw [show (phi4WTriplePrime_recoveredSplitChoice z).choice
        ⟨phi4WTriplePrime_inv_recoveredParent
          (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδ), hmem⟩
        (Finset.mem_attach _ _)
        = Sum.inr ⟨phi4WTriplePrime_inv_recoveredInnerForest
            (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδ)
            (phi4WTriplePrime_inv_innerForest_CD_proof
              (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδ)),
          phi4WTriplePrime_inv_recoveredInnerForest_mem_proof
            (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδ)⟩
      from phi4WTriplePrime_recoveredChoice_forest_value z hδ hmem]
  simp only [Sum.elim_inr]
  exact phi4WTriplePrime_inv_promotion_recovery
    (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδ)
    (phi4WTriplePrime_inv_innerForest_CD_proof
      (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδ))

/-- **body-620 (Step 4b) — a clean element-set extensionality for φ⁴ admissible subgraphs.**  Bypasses the
polluted `ResolvedAdmissibleSubgraph.ext_elements` (which carries a forbidden `[IsAmbientInvariantDivergence]`
section binder): the two non-`elements` fields are `Prop`s, so equal element sets force equality by
`cases` + definitional proof irrelevance.  NO forbidden divergence class in the type. -/
theorem phi4WTriplePrime_admissible_ext_elements
    {A₁ A₂ : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G}
    (h : @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G A₁
       = @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G A₂) : A₁ = A₂ := by
  cases A₁; cases A₂; cases h; rfl

/-- **body-620 (Step 4, HEADLINE) — the outer raw equality.**  `selectedOuter (recoveredSplitChoice z)`
reconstructs the original outer forest `z.1.1` EXACTLY (a raw `ResolvedAdmissibleSubgraph` equality via
`ext_elements`): LEFT components come back verbatim; the FOREST promotions re-inflate to the touched outer
components (`promotion_recovery`).  Identifies the ambient PROPOSITIONALLY only. -/
theorem phi4WTriplePrime_selectedOuter_recoveredSplitChoice (z : Phi4WTriplePrimeInverseCodomain G) :
    phi4WTriplePrime_selectedOuter (phi4WTriplePrime_recoveredSplitChoice z) = z.1.1 := by
  apply phi4WTriplePrime_admissible_ext_elements
  rw [phi4WTriplePrime_selectedOuter_elements]
  ext c
  rw [Finset.mem_union]
  constructor
  · rintro (hL | hP)
    · -- c ∈ leftOf.elements → c ∈ A
      rw [phi4WTriplePrime_leftOf_elements, Finset.mem_filter] at hL
      obtain ⟨hcRO, hlp⟩ := hL
      rcases phi4WTriplePrime_recoveredOuter_component_origin z hcRO with ⟨hcA, _⟩ | ⟨δc, hδceq⟩
      · exact hcA
      · exfalso
        obtain ⟨hh, htrue⟩ := hlp
        have hq : ∃ d : {x // x ∈ z.2.1.elements},
            phi4WTriplePrime_inv_regionComponentOf z d = c := ⟨δc, hδceq⟩
        by_cases hst : phi4WTriplePrime_inv_isForestImage z hq.choose
        · rw [show (phi4WTriplePrime_recoveredSplitChoice z).choice ⟨c, hh⟩ (Finset.mem_attach _ _)
                = Sum.inr (phi4WTriplePrime_recoveredForestTag z ⟨c, hh⟩ hq hst) from by
                  rw [phi4WTriplePrime_recoveredSplitChoice_choice]
                  unfold phi4WTriplePrime_recoveredChoice
                  rw [dif_pos hq]; exact dif_pos hst] at htrue
          simp at htrue
        · rw [show (phi4WTriplePrime_recoveredSplitChoice z).choice ⟨c, hh⟩ (Finset.mem_attach _ _)
                = Sum.inl false from by
                  rw [phi4WTriplePrime_recoveredSplitChoice_choice]
                  unfold phi4WTriplePrime_recoveredChoice
                  rw [dif_pos hq]; exact dif_neg hst] at htrue
          simp at htrue
    · -- c ∈ promotedOf.elements → c ∈ A
      rw [phi4WTriplePrime_promotedOf_elements, Finset.mem_biUnion] at hP
      obtain ⟨a, -, hca⟩ := hP
      rcases hcc : (phi4WTriplePrime_recoveredSplitChoice z).choice a (Finset.mem_attach _ a) with b | B
      · -- primitive leg → promoted set empty
        exfalso
        rw [show phi4WTriplePrime_promotedElemsAt (phi4WTriplePrime_recoveredSplitChoice z) a = ∅
              from by unfold phi4WTriplePrime_promotedElemsAt; rw [hcc]; rfl] at hca
        simp at hca
      · -- forest leg → forest owner → touched outer forest ⊆ A
        have hq : ∃ d : {x // x ∈ z.2.1.elements},
            phi4WTriplePrime_inv_regionComponentOf z d = a.1 := by
          by_contra hnq
          rw [show (phi4WTriplePrime_recoveredSplitChoice z).choice a (Finset.mem_attach _ a)
                = Sum.inl true from by
                  rw [phi4WTriplePrime_recoveredSplitChoice_choice]; unfold phi4WTriplePrime_recoveredChoice; rw [dif_neg hnq]] at hcc
          simp at hcc
        have hst : phi4WTriplePrime_inv_isForestImage z hq.choose := by
          by_contra hns
          rw [show (phi4WTriplePrime_recoveredSplitChoice z).choice a (Finset.mem_attach _ a)
                = Sum.inl false from by
                  rw [phi4WTriplePrime_recoveredSplitChoice_choice]; unfold phi4WTriplePrime_recoveredChoice; rw [dif_pos hq, dif_neg hns]] at hcc
          simp at hcc
        have hav : a.1 = phi4WTriplePrime_inv_recoveredParent
                          (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hst) :=
          hq.choose_spec.symm.trans (phi4WTriplePrime_inv_regionComponentOf_eq_parent z hst)
        have ha_eq : a = ⟨phi4WTriplePrime_inv_recoveredParent
              (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hst), hav ▸ a.2⟩ :=
          Subtype.ext hav
        have hset : phi4WTriplePrime_promotedElemsAt (phi4WTriplePrime_recoveredSplitChoice z) a
            = (phi4WTriplePrime_touchedOuterForest z hq.choose).elements :=
          (congrArg (phi4WTriplePrime_promotedElemsAt (phi4WTriplePrime_recoveredSplitChoice z)) ha_eq).trans
            (phi4WTriplePrime_promotedElemsAt_forestOwner z hst (hav ▸ a.2))
        rw [hset] at hca
        exact phi4WTriplePrime_inv_touchedForest_subset_A hca
  · intro hc
    by_cases hL : phi4WTriplePrime_inv_isLeftComponent z c
    · -- LEFT → leftOf
      left
      rw [phi4WTriplePrime_leftOf_elements, Finset.mem_filter]
      refine ⟨phi4WTriplePrime_inv_left_mem_recoveredOuter z hc hL, ?_⟩
      exact ⟨phi4WTriplePrime_inv_left_mem_recoveredOuter z hc hL,
        phi4WTriplePrime_recoveredChoice_left z hc hL (Finset.mem_attach _ _)⟩
    · -- non-left → touched → promotedOf
      right
      obtain ⟨δ, hδv⟩ := (phi4WTriplePrime_inv_not_isLeftComponent_iff z c).mp hL
      have hδf : phi4WTriplePrime_inv_isForestImage z δ :=
        ⟨phi4WTriplePrimeCanonicalSupply.starOf G z.1.1 c, hδv,
          ResolvedAdmissibleSubgraph.mem_starVertices.mpr ⟨c, hc, rfl⟩⟩
      have hcT : c ∈ (phi4WTriplePrime_touchedOuterForest z δ).elements :=
        phi4WTriplePrime_inv_touched_of_starA_mem hc hδv
      rw [phi4WTriplePrime_promotedOf_elements, Finset.mem_biUnion]
      have hmem : phi4WTriplePrime_inv_recoveredParent
                    (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδf)
                  ∈ (phi4WTriplePrime_recoveredSplitChoice z).outer.elements :=
        (phi4WTriplePrime_inv_regionComponentOf_eq_parent z hδf)
          ▸ phi4WTriplePrime_inv_regionComponent_mem_recoveredOuter z δ
      refine ⟨⟨phi4WTriplePrime_inv_recoveredParent
                (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδf), hmem⟩,
        Finset.mem_attach _ _, ?_⟩
      rw [phi4WTriplePrime_promotedElemsAt_forestOwner z hδf hmem]
      exact hcT

/-! ## Step 5 — correcting-permutation action agreement on the visible support -/

/-- **body-620 (Step 5) — the two correcting permutations agree on the visible support of the local
contracted graph.**  On survivors both fix (`remnantTau_fix` / `reconTau_fix`); on local stars both send to
the SAME quotient star (`remnantTau_map` + promotion recovery + Step 4 outer equality vs. `reconTau_map`).
NEVER claims `remnantTau o = reconTau O` — only agreement on `(localContractGraph o).vertices`. -/
theorem phi4WTriplePrime_recon_agree_on_vertices
    (z : Phi4WTriplePrimeInverseCodomain G)
    {δ : {x // x ∈ z.2.1.elements}} (hδ : phi4WTriplePrime_inv_isForestImage z δ)
    {w : VertexId}
    (hw : w ∈ (phi4WTriplePrime_localContractGraph
              (phi4WTriplePrime_recoveredForwardOccurrence z hδ)).vertices) :
    phi4WTriplePrime_remnantTau (phi4WTriplePrime_recoveredForwardOccurrence z hδ) w
      = phi4WTriplePrime_inv_reconTau
          (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδ) w := by
  set o := phi4WTriplePrime_recoveredForwardOccurrence z hδ with ho
  set I := phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδ with hI
  rw [phi4WTriplePrime_localContractGraph,
    ResolvedAdmissibleSubgraph.contractWithStars_vertices, Finset.mem_union] at hw
  rcases hw with hsurv | hstar
  · -- survivor: both fix
    rw [Finset.mem_sdiff, ResolvedFeynmanSubgraph.boundaryCompletedResolvedGraph_vertices] at hsurv
    rw [phi4WTriplePrime_remnantTau_fix o (Finset.mem_sdiff.mpr hsurv),
        phi4WTriplePrime_inv_reconTau_fix I (Finset.mem_sdiff.mpr hsurv)]
  · -- star: both send to the same quotient star
    rw [ResolvedAdmissibleSubgraph.mem_starVertices] at hstar
    obtain ⟨δ₀, hδ₀, rfl⟩ := hstar
    obtain ⟨γ'', hγ'', hδ₀eq⟩ :=
      phi4WTriplePrime_inv_recoveredInnerForest_element_origin I
        (phi4WTriplePrime_inv_innerForest_CD_proof I) hδ₀
    subst hδ₀eq
    have hL : phi4WTriplePrime_remnantTau o
          (phi4WTriplePrimeCanonicalSupply.starOf o.γ.1.boundaryCompletedResolvedGraph o.B.1
            (phi4WTriplePrime_inv_innerComponent I γ'' hγ''))
        = phi4WTriplePrimeCanonicalSupply.starOf G z.1.1 γ'' := by
      rw [phi4WTriplePrime_remnantTau_map o ⟨phi4WTriplePrime_inv_innerComponent I γ'' hγ'', hδ₀⟩,
        phi4WTriplePrime_selectedOuter_recoveredSplitChoice z]
      exact congrArg _ (phi4WTriplePrime_inv_promotion_recovery_component I hγ'')
    have hR : phi4WTriplePrime_inv_reconTau I
          (phi4WTriplePrimeCanonicalSupply.starOf o.γ.1.boundaryCompletedResolvedGraph o.B.1
            (phi4WTriplePrime_inv_innerComponent I γ'' hγ''))
        = phi4WTriplePrimeCanonicalSupply.starOf G z.1.1 γ'' :=
      phi4WTriplePrime_inv_reconTau_map I ⟨γ'', hγ''⟩
    rw [hL, hR]

/-! ## Step 6 — the sole headline: the ambient-free bcrg reconciliation -/

/-- **body-620 (Step 6, SOLE HEADLINE) — the forward-after-inverse FOREST bcrg reconciliation.**  Composing
body-604 `remnant_contractTwice` (LHS `= localContractGraph.mapPerm (remnantTau o)`) with body-616
`correctedForestGraph_eq` (`= δ.1.bcrg`, whose base graph is DEFINITIONALLY `localContractGraph o` mapped by
`reconTau I`), bridged by Step 5's action agreement fed through `Finset.image_congr` / `Multiset.map_congr`:

`(remnantComponent (recoveredForwardOccurrence z δ hδ)).bcrg = δ.1.bcrg`

— both sides are plain `ResolvedFeynmanGraph`, a genuine homogeneous raw `Eq` preserving ID / multiplicity /
sector.  NO `remnantTau = reconTau`; NO ill-typed cross-ambient raw-subgraph equality; NO `Sigma.ext`. -/
theorem phi4WTriplePrime_forwardInverse_forest_bcrg_reconcile
    (z : Phi4WTriplePrimeInverseCodomain G)
    {δ : {x // x ∈ z.2.1.elements}} (hδ : phi4WTriplePrime_inv_isForestImage z δ) :
    (phi4WTriplePrime_remnantComponent
        (phi4WTriplePrime_recoveredForwardOccurrence z hδ)).boundaryCompletedResolvedGraph
      = δ.1.boundaryCompletedResolvedGraph := by
  rw [phi4WTriplePrime_remnant_contractTwice (phi4WTriplePrime_recoveredForwardOccurrence z hδ),
    ← phi4WTriplePrime_inv_correctedForestGraph_eq (phi4WTriplePrime_recoveredForestOccurrence z δ hδ)]
  -- goal (defeq): (localContractGraph o).mapPerm (remnantTau o) = (localContractGraph o).mapPerm (reconTau I)
  show (phi4WTriplePrime_localContractGraph
          (phi4WTriplePrime_recoveredForwardOccurrence z hδ)).mapPerm
        (phi4WTriplePrime_remnantTau (phi4WTriplePrime_recoveredForwardOccurrence z hδ))
      = (phi4WTriplePrime_localContractGraph
          (phi4WTriplePrime_recoveredForwardOccurrence z hδ)).mapPerm
        (phi4WTriplePrime_inv_reconTau
          (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδ))
  set o := phi4WTriplePrime_recoveredForwardOccurrence z hδ with ho
  set H := phi4WTriplePrime_localContractGraph o with hH
  set τ₁ := phi4WTriplePrime_remnantTau o with hτ₁
  set τ₂ := phi4WTriplePrime_inv_reconTau
    (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδ) with hτ₂
  -- every leg attach point of H lies in H.vertices (contractWithStars over the bcrg ambient)
  have hlegSupp : ∀ ℓ ∈ H.externalLegs, ℓ.attachedTo ∈ H.vertices := by
    intro ℓ hℓ
    rw [hH, phi4WTriplePrime_localContractGraph,
      ResolvedAdmissibleSubgraph.contractWithStars_externalLegs] at hℓ
    obtain ⟨ℓ₀, hℓ₀, rfl⟩ := Multiset.mem_map.mp hℓ
    show (ResolvedAdmissibleSubgraph.retargetVertex _ _ ℓ₀.attachedTo) ∈ H.vertices
    rw [hH, phi4WTriplePrime_localContractGraph]
    exact ResolvedAdmissibleSubgraph.retargetVertex_mem_contractWithStars_vertices _ _
      (ResolvedFeynmanSubgraph.boundaryCompletedResolvedExternalLegs_supported _ ℓ₀ hℓ₀)
  -- every edge endpoint of H lies in H.vertices
  have hedgeSupp : ∀ e ∈ H.internalEdges, e.source ∈ H.vertices ∧ e.target ∈ H.vertices := by
    intro e he
    exact phi4WTriplePrime_localContract_edge_endpoints o (by rw [← hH]; exact he)
  -- the master agreement on H.vertices
  have hagree : ∀ w ∈ H.vertices, τ₁ w = τ₂ w := by
    intro w hw
    rw [hτ₁, hτ₂]
    exact phi4WTriplePrime_recon_agree_on_vertices z hδ (by rw [← hH]; exact hw)
  -- assemble the three raw fields of mapPerm
  show ResolvedFeynmanGraph.mapPerm τ₁ H = ResolvedFeynmanGraph.mapPerm τ₂ H
  unfold ResolvedFeynmanGraph.mapPerm
  refine congr (congr (congrArg ResolvedFeynmanGraph.mk ?_) ?_) ?_
  · -- vertices
    exact Finset.image_congr (fun w hw => hagree w hw)
  · -- internal edges
    refine Multiset.map_congr rfl (fun e he => ?_)
    obtain ⟨hs, ht⟩ := hedgeSupp e he
    show ResolvedFeynmanEdge.map τ₁ e = ResolvedFeynmanEdge.map τ₂ e
    unfold ResolvedFeynmanEdge.map
    rw [hagree e.source hs, hagree e.target ht]
  · -- external legs
    refine Multiset.map_congr rfl (fun ℓ hℓ => ?_)
    have hatt := hlegSupp ℓ hℓ
    show ResolvedExternalLeg.map τ₁ ℓ = ResolvedExternalLeg.map τ₂ ℓ
    unfold ResolvedExternalLeg.map
    rw [hagree ℓ.attachedTo hatt]

end GaugeGeometry.QFT.Combinatorial
