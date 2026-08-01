import GaugeGeometry.QFT.HopfAlgebra.Phi4StableQuotientForest

/-!
# QFT-R1-body-638 — the STABLE right-factor aggregate (pure multiplicative reindexing)

Body-624 built the two-stage coproduct's LEFT factor; this body supplies the second factor it lacked: the
`stableRightFactorProduct` — the product of the per-outer-component `stableLocalRightFactor` (body-633) over
`s.1.outer.elements.attach` — is EXACTLY the single live quotient forest's stable LEFT aggregate
`stableLeftAggregate (stableQuotientForest s) Q`.  This is a PURE MULTIPLICATIVE REINDEXING: it does NOT re-expand
any `τ` / contract-twice geometry.  The RIGHT- and FOREST-sector products are merged into the survivor / remnant
LEFT aggregates by consuming ONLY the COMPLETED generator equalities `stableLocalRightFactor_right_eq_survivorGen`
(body-634) and `stableLocalRightFactor_forest_eq_remnantGen` (body-636), then the two aggregates are unioned into
the quotient aggregate via `stableQuotientForest_elements` + `Finset.prod_union`.

## Steps

* **Step 1 — source product + three-region split.**  `stableRightFactorProduct` is the `.attach` product of
  `stableLocalRightFactor`.  `stableRightFactorProduct_split` peels the LEFT sector (`Sum.inl true → 1`) via
  `Finset.prod_subset` and partitions the rest into the RIGHT sector (`Sum.inl false`) and the FOREST sector
  (`Sum.inr B`) via `Finset.prod_filter_mul_prod_filter_not`.
* **Step 2 — RIGHT aggregate** (`stableRightPrimitiveFactor_product`).  A `Finset.prod_bij` reindexing the RIGHT
  sector onto the survivor forest's `.elements.attach`; injectivity from `stableRightSurvivor_injOn`; each factor
  is the survivor's stable generator by `stableLocalRightFactor_right_eq_survivorGen`.
* **Step 3 — FOREST aggregate** (`stableForestFactor_product`).  A `Finset.prod_bij` reindexing the FOREST sector
  onto the remnant forest's `.elements.attach`; injectivity from `stableRemnant_injOn`; each factor is the
  remnant's stable generator by `stableLocalRightFactor_forest_eq_remnantGen` (COMPLETED equality — the 635/636 τ
  geometry is NOT re-expanded).
* **Step 4 — quotient union product** (`stableLeftAggregate_quotientForest`).  Survivor / remnant elements are
  Finset-disjoint by the tag-origin contradiction (`stableSurvivorRemnant_elements_disjoint`), so via
  `stableQuotientForest_elements` + `Finset.prod_union` the quotient LEFT aggregate splits into survivor × remnant.
  NO constituent forest is assumed `Nonempty`.
* **Step 5 — HEADLINE** (`stableRightFactorProduct_eq_quotientForest`).  Bundle Steps 1-4.

## HALT / red lines
`stableForestRightTerm outer = stableForestRightTerm quotientForest` (that is 639 `quot_eq`), summand agreement /
`sum_bij` / alpha / coassoc are NOT entered.  NO polluted abstract product lemma / body-258 consume; NO global
correcting permutation / contract-twice geometry re-proof; NO orbit quotient / dedup / exact residual / `toFinset`;
NO cross-ambient `Eq` / `HEq` / graph-data `▸` (Prop-membership `▸` only).  ZERO new `structure` / `class` /
permanent `instance` (one file-local `local instance` for the φ⁴ family); ZERO forbidden divergence class in any
declaration TYPE; ZERO `sorry` / `admit` / `native_decide`.  Body-625's no-go and bodies 629-637 / the old carrier
are UNEDITED.  Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

open ResolvedFeynmanSubgraph

variable {G : ResolvedFeynmanGraph}

set_option maxHeartbeats 3200000

/-- The concrete φ⁴ divergence measure family, registered file-locally (providable instance, NO forbidden
class). -/
noncomputable local instance instPhi4DivergenceMeasureFamily638 : (H : FeynmanGraph) → DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

variable {hSt : StableResolvedBoundaryIds G}

/-! ## Step 1 — the source product + the three-region split -/

/-- **body-638 (Step 1) — the stable right-factor product.**  The product of the per-outer-component
`stableLocalRightFactor` over `s.1.outer.elements.attach`. -/
noncomputable def stableRightFactorProduct (hSt : StableResolvedBoundaryIds G)
    (s : StablePhi4MixedSplitChoice G hSt) : StableResolvedPhi4HopfH :=
  ∏ γ ∈ s.1.outer.elements.attach,
    stableLocalRightFactor hSt γ.1 (s.1.outer.isConnectedDivergent γ.1 γ.2)
      (s.1.choice γ (Finset.mem_attach _ γ))

/-- **body-638 (Step 1) — the three-region split.**  The LEFT sector (`Sum.inl true`) contributes `1`, so the
whole product factors as (RIGHT sector `Sum.inl false`) × (FOREST sector `Sum.inr B`). -/
theorem stableRightFactorProduct_split (hSt : StableResolvedBoundaryIds G)
    (s : StablePhi4MixedSplitChoice G hSt) :
    stableRightFactorProduct hSt s
      = (∏ γ ∈ s.1.outer.elements.attach.filter
            (fun γ => s.1.choice γ (Finset.mem_attach _ γ) = Sum.inl false),
          stableLocalRightFactor hSt γ.1 (s.1.outer.isConnectedDivergent γ.1 γ.2)
            (s.1.choice γ (Finset.mem_attach _ γ)))
        * (∏ γ ∈ s.1.outer.elements.attach.filter
            (fun γ => s.1.choice γ (Finset.mem_attach _ γ) ≠ Sum.inl false
              ∧ s.1.choice γ (Finset.mem_attach _ γ) ≠ Sum.inl true),
          stableLocalRightFactor hSt γ.1 (s.1.outer.isConnectedDivergent γ.1 γ.2)
            (s.1.choice γ (Finset.mem_attach _ γ))) := by
  classical
  unfold stableRightFactorProduct
  rw [← Finset.prod_filter_mul_prod_filter_not s.1.outer.elements.attach
      (fun γ => s.1.choice γ (Finset.mem_attach _ γ) = Sum.inl false)]
  have hforest :
      (∏ γ ∈ s.1.outer.elements.attach.filter
          (fun γ => ¬ (s.1.choice γ (Finset.mem_attach _ γ) = Sum.inl false)),
        stableLocalRightFactor hSt γ.1 (s.1.outer.isConnectedDivergent γ.1 γ.2)
          (s.1.choice γ (Finset.mem_attach _ γ)))
        = ∏ γ ∈ s.1.outer.elements.attach.filter
            (fun γ => s.1.choice γ (Finset.mem_attach _ γ) ≠ Sum.inl false
              ∧ s.1.choice γ (Finset.mem_attach _ γ) ≠ Sum.inl true),
          stableLocalRightFactor hSt γ.1 (s.1.outer.isConnectedDivergent γ.1 γ.2)
            (s.1.choice γ (Finset.mem_attach _ γ)) := by
    symm
    apply Finset.prod_subset
    · intro x hx
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, hx.2.1⟩
    · intro x hx hxnot
      rw [Finset.mem_filter] at hx
      have hxL : s.1.choice x (Finset.mem_attach _ x) = Sum.inl true := by
        by_contra hne
        exact hxnot (Finset.mem_filter.mpr ⟨hx.1, hx.2, hne⟩)
      show stableLocalRightFactor hSt x.1 (s.1.outer.isConnectedDivergent x.1 x.2)
        (s.1.choice x (Finset.mem_attach _ x)) = 1
      rw [hxL, stableLocalRightFactor_inl_true]
  rw [hforest]

/-! ## Step 2 — the RIGHT-sector aggregate -/

/-- **body-638 (Step 2) — the RIGHT-sector product is the survivor forest's stable LEFT aggregate.**  A
`Finset.prod_bij` reindexing the RIGHT sector (choice `Sum.inl false`) onto the survivor forest's
`.elements.attach`; injectivity from `stableRightSurvivor_injOn`; the per-factor value is the survivor's stable
generator by `stableLocalRightFactor_right_eq_survivorGen`.  NO geometry re-expanded. -/
theorem stableRightPrimitiveFactor_product (s : StablePhi4MixedSplitChoice G hSt) :
    (∏ γ ∈ s.1.outer.elements.attach.filter
        (fun γ => s.1.choice γ (Finset.mem_attach _ γ) = Sum.inl false),
      stableLocalRightFactor hSt γ.1 (s.1.outer.isConnectedDivergent γ.1 γ.2)
        (s.1.choice γ (Finset.mem_attach _ γ)))
      = stableLeftAggregate (stableRightSurvivorForest s.1)
          (stableSelectedOuterContractGraph_stableIds s.1) := by
  classical
  have hmemR : ∀ (γ : {x // x ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G s.1.outer})
      (hR : s.1.choice γ (Finset.mem_attach _ γ) = Sum.inl false),
      stableRightSurvivor s.1 (⟨γ.2, hR⟩ : stableIsRightComponent s.1 γ.1)
        ∈ (stableRightSurvivorForest s.1).elements := by
    intro γ hR
    rw [stableRightSurvivorForest_elements]
    have hmemRC : γ.1 ∈ stableRightComponents s.1 :=
      (stableMem_rightComponents s.1).mpr ⟨γ.2, ⟨γ.2, hR⟩⟩
    exact Finset.mem_image.mpr ⟨⟨γ.1, hmemRC⟩, Finset.mem_attach _ _, rfl⟩
  simp only [stableLeftAggregate]
  refine Finset.prod_bij
    (fun γ hγ => (⟨stableRightSurvivor s.1 (⟨γ.2, (Finset.mem_filter.mp hγ).2⟩ :
        stableIsRightComponent s.1 γ.1),
        hmemR γ (Finset.mem_filter.mp hγ).2⟩ : {x // x ∈ (stableRightSurvivorForest s.1).elements}))
    (fun _ _ => Finset.mem_attach _ _)
    ?_ ?_ ?_
  · intro γ₁ hγ₁ γ₂ hγ₂ heq
    refine Subtype.ext (stableRightSurvivor_injOn s.1
      (⟨γ₁.2, (Finset.mem_filter.mp hγ₁).2⟩ : stableIsRightComponent s.1 γ₁.1)
      (⟨γ₂.2, (Finset.mem_filter.mp hγ₂).2⟩ : stableIsRightComponent s.1 γ₂.1) ?_)
    exact congrArg Subtype.val heq
  · intro δ _
    obtain ⟨γ0, hγR0, hδeq⟩ := stableRightSurvivorForest_element_origin s.1 δ.2
    have hfilt : (⟨γ0, hγR0.choose⟩ : {x // x ∈ @ResolvedAdmissibleSubgraph.elements
        phi4DivergenceMeasureFamily G s.1.outer})
        ∈ s.1.outer.elements.attach.filter
          (fun γ => s.1.choice γ (Finset.mem_attach _ γ) = Sum.inl false) := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_attach _ _, hγR0.choose_spec⟩
    exact ⟨⟨γ0, hγR0.choose⟩, hfilt, Subtype.ext hδeq.symm⟩
  · intro γ hγ
    have hR : s.1.choice γ (Finset.mem_attach _ γ) = Sum.inl false := (Finset.mem_filter.mp hγ).2
    rw [hR]
    exact stableLocalRightFactor_right_eq_survivorGen s.1
      (⟨γ.2, hR⟩ : stableIsRightComponent s.1 γ.1) (s.1.outer.isConnectedDivergent γ.1 γ.2)

/-! ## Step 3 — the FOREST-sector aggregate -/

/-- **body-638 (Step 3) — the forest-component recovery of a FOREST-sector element.**  A component whose stable
choice is neither `Sum.inl false` nor `Sum.inl true` is a forest component (its choice lands in `Sum.inr`). -/
theorem stableForestComponent_of_filter (s : StablePhi4MixedSplitChoice G hSt)
    (γ : {x // x ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G s.1.outer})
    (h1 : s.1.choice γ (Finset.mem_attach _ γ) ≠ Sum.inl false)
    (h2 : s.1.choice γ (Finset.mem_attach _ γ) ≠ Sum.inl true) :
    stableIsForestComponent s γ.1 := by
  rcases hh : s.1.choice γ (Finset.mem_attach _ γ) with b | B
  · rcases b with _ | _
    · exact absurd hh h1
    · exact absurd hh h2
  · exact ⟨γ.2, B, hh⟩

/-- **body-638 (Step 3) — the forest-choice occurrence of a FOREST-sector element.** -/
noncomputable def stableForestOccOfFilter (s : StablePhi4MixedSplitChoice G hSt)
    (γ : {x // x ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G s.1.outer})
    (h1 : s.1.choice γ (Finset.mem_attach _ γ) ≠ Sum.inl false)
    (h2 : s.1.choice γ (Finset.mem_attach _ γ) ≠ Sum.inl true) :
    StableForestChoiceOccurrence s :=
  stableForestComponentOccurrence
    ⟨γ.1, (stableMem_forestComponents s).mpr ⟨γ.2, stableForestComponent_of_filter s γ h1 h2⟩⟩

/-- **body-638 (Step 3) — the FOREST-sector product is the remnant forest's stable LEFT aggregate.**  A
`Finset.prod_bij` reindexing the FOREST sector onto the remnant forest's `.elements.attach`; injectivity from
`stableRemnant_injOn`; the per-factor value is the remnant's stable generator by
`stableLocalRightFactor_forest_eq_remnantGen` — the COMPLETED generator equality; the 635/636 τ geometry is NOT
re-expanded. -/
theorem stableForestFactor_product (s : StablePhi4MixedSplitChoice G hSt) :
    (∏ γ ∈ s.1.outer.elements.attach.filter
        (fun γ => s.1.choice γ (Finset.mem_attach _ γ) ≠ Sum.inl false
          ∧ s.1.choice γ (Finset.mem_attach _ γ) ≠ Sum.inl true),
      stableLocalRightFactor hSt γ.1 (s.1.outer.isConnectedDivergent γ.1 γ.2)
        (s.1.choice γ (Finset.mem_attach _ γ)))
      = stableLeftAggregate (stableRemnantForest s)
          (stableSelectedOuterContractGraph_stableIds s.1) := by
  classical
  have hmemRem : ∀ (γ : {x // x ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G s.1.outer})
      (h1 : s.1.choice γ (Finset.mem_attach _ γ) ≠ Sum.inl false)
      (h2 : s.1.choice γ (Finset.mem_attach _ γ) ≠ Sum.inl true),
      stableRemnantComponent (stableForestOccOfFilter s γ h1 h2) ∈ (stableRemnantForest s).elements := by
    intro γ h1 h2
    rw [stableRemnantForest_elements]
    exact Finset.mem_image.mpr
      ⟨⟨γ.1, (stableMem_forestComponents s).mpr ⟨γ.2, stableForestComponent_of_filter s γ h1 h2⟩⟩,
        Finset.mem_attach _ _, rfl⟩
  simp only [stableLeftAggregate]
  refine Finset.prod_bij
    (fun γ hγ => (⟨stableRemnantComponent (stableForestOccOfFilter s γ
        (Finset.mem_filter.mp hγ).2.1 (Finset.mem_filter.mp hγ).2.2),
        hmemRem γ (Finset.mem_filter.mp hγ).2.1 (Finset.mem_filter.mp hγ).2.2⟩
        : {x // x ∈ (stableRemnantForest s).elements}))
    (fun _ _ => Finset.mem_attach _ _)
    ?_ ?_ ?_
  · intro γ₁ hγ₁ γ₂ hγ₂ heq
    by_contra hne
    exact stableRemnant_injOn
      (stableForestOccOfFilter s γ₁ (Finset.mem_filter.mp hγ₁).2.1 (Finset.mem_filter.mp hγ₁).2.2)
      (stableForestOccOfFilter s γ₂ (Finset.mem_filter.mp hγ₂).2.1 (Finset.mem_filter.mp hγ₂).2.2)
      (fun hgeq => hne (Subtype.ext hgeq))
      (congrArg Subtype.val heq)
  · intro δ _
    have hδmem : δ.1 ∈ (stableForestComponents s).attach.image
        (fun γF => stableRemnantComponent (stableForestComponentOccurrence γF)) := by
      rw [← stableRemnantForest_elements]; exact δ.2
    obtain ⟨γF, -, hγFeq⟩ := Finset.mem_image.mp hδmem
    have hmemOuter : γF.1 ∈ s.1.outer.elements := ((stableMem_forestComponents s).mp γF.2).1
    obtain ⟨h0, B0, hch0⟩ := ((stableMem_forestComponents s).mp γF.2).2
    have hchOuter : s.1.choice (⟨γF.1, hmemOuter⟩ : {x // x ∈ @ResolvedAdmissibleSubgraph.elements
        phi4DivergenceMeasureFamily G s.1.outer}) (Finset.mem_attach _ _) = Sum.inr B0 := hch0
    have hfilt : (⟨γF.1, hmemOuter⟩ : {x // x ∈ @ResolvedAdmissibleSubgraph.elements
        phi4DivergenceMeasureFamily G s.1.outer})
        ∈ s.1.outer.elements.attach.filter
          (fun γ => s.1.choice γ (Finset.mem_attach _ γ) ≠ Sum.inl false
            ∧ s.1.choice γ (Finset.mem_attach _ γ) ≠ Sum.inl true) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, ?_, ?_⟩
      · rw [hchOuter]; simp
      · rw [hchOuter]; simp
    exact ⟨⟨γF.1, hmemOuter⟩, hfilt, Subtype.ext hγFeq⟩
  · intro γ hγ
    have h1 : s.1.choice γ (Finset.mem_attach _ γ) ≠ Sum.inl false := (Finset.mem_filter.mp hγ).2.1
    have h2 : s.1.choice γ (Finset.mem_attach _ γ) ≠ Sum.inl true := (Finset.mem_filter.mp hγ).2.2
    have hval : s.1.choice γ (Finset.mem_attach _ γ)
        = Sum.inr (stableForestOccOfFilter s γ h1 h2).B := (stableForestOccOfFilter s γ h1 h2).hchoice
    rw [hval]
    exact stableLocalRightFactor_forest_eq_remnantGen (stableForestOccOfFilter s γ h1 h2)
      (s.1.outer.isConnectedDivergent γ.1 γ.2)
      (stableLocalBoundaryCompletedGraph_exists_self_isConnectedDivergent
        (stableRemnantComponent (stableForestOccOfFilter s γ h1 h2))
        (stableRemnant_isConnectedDivergent (stableForestOccOfFilter s γ h1 h2)))
      (stableResolvedBoundaryIds_stableLocalBoundaryCompletedGraph
        (stableRemnantComponent (stableForestOccOfFilter s γ h1 h2))
        (stableSelectedOuterContractGraph_stableIds s.1))

/-! ## Step 4 — the quotient union product -/

/-- **body-638 (Step 4) — the survivor and remnant element-Finsets are disjoint.**  A right survivor `= a`
remnant would give a nonempty right-component vertex lying in a remnant; the remnant-origin cases contradict
either the outer pairwise disjointness / choice-tag disagreement (`Sum.inl false` vs `Sum.inr B`) or the
freshness of the promoted global stars.  NO global τ. -/
theorem stableSurvivorRemnant_elements_disjoint (s : StablePhi4MixedSplitChoice G hSt) :
    Disjoint (stableRightSurvivorForest s.1).elements (stableRemnantForest s).elements := by
  rw [Finset.disjoint_left]
  intro δ hδS hδR
  obtain ⟨γR, hγR, rfl⟩ := stableRightSurvivorForest_element_origin s.1 hδS
  obtain ⟨o, hoeq⟩ := stableRemnantForest_element_origin hδR
  have hpfSel := stableSelectedOuter_isProperForest s.1
  have houterNE : s.1.outer.HasNonemptyComponents :=
    (((mem_phi4WTriplePrimeIndex G s.1.outer).mp s.1.outer_mem).2.2.2.2.1).2.1
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (houterNE γR hγR.choose)
  have hvS : v ∈ (stableRightSurvivor s.1 hγR).vertices := by
    rw [stableRightSurvivor_vertices]; exact hv
  have hvR : v ∈ (stableRemnantComponent o).vertices := by
    rw [← hoeq]; exact hvS
  rcases stableRemnant_origin o hvR with hvγF | ⟨δ0, hδ0, hveq⟩
  · by_cases hEq : γR = o.γ.1
    · subst hEq
      exact absurd (hγR.choose_spec.symm.trans o.hchoice) (by simp)
    · exact Finset.disjoint_left.mp (s.1.outer.pairwiseDisjoint hγR.choose o.γ.2 hEq) hv hvγF
  · exact stableRemnant_gen_star_not_mem (stableSelectedOuter s.1) hpfSel
      (stableRemnant_promoted_mem o hδ0) (hveq ▸ γR.vertices_subset hv)

/-- **body-638 (Step 4) — the quotient forest's stable LEFT aggregate splits into survivor × remnant.**  Via
`stableQuotientForest_elements` (survivor ∪ remnant) + `Finset.prod_union` on the Finset-disjoint elements, over
the proof-independent totalized generator (`stableLeftAggregate_eq_prod`).  Neither constituent forest is assumed
`Nonempty`. -/
theorem stableLeftAggregate_quotientForest (s : StablePhi4MixedSplitChoice G hSt) :
    stableLeftAggregate (stableQuotientForest s) (stableSelectedOuterContractGraph_stableIds s.1)
      = stableLeftAggregate (stableRightSurvivorForest s.1) (stableSelectedOuterContractGraph_stableIds s.1)
        * stableLeftAggregate (stableRemnantForest s) (stableSelectedOuterContractGraph_stableIds s.1) := by
  rw [stableLeftAggregate_eq_prod, stableLeftAggregate_eq_prod, stableLeftAggregate_eq_prod,
    stableQuotientForest_elements]
  exact Finset.prod_union (stableSurvivorRemnant_elements_disjoint s)

/-! ## Step 5 — HEADLINE -/

/-- **body-638 (Step 5, HEADLINE) — the stable right-factor product IS the quotient forest's stable LEFT
aggregate.**  Bundles the three-region split (Step 1, LEFT `= 1`) with the RIGHT / FOREST aggregates (Steps 2-3)
and the quotient union split (Step 4).  This supplies the second factor body-624 lacked, by a PURE MULTIPLICATIVE
REINDEXING — NO `τ` / contract-twice geometry is re-expanded, and `quot_eq` (639) is NOT entered. -/
theorem stableRightFactorProduct_eq_quotientForest (hSt : StableResolvedBoundaryIds G)
    (s : StablePhi4MixedSplitChoice G hSt) :
    stableRightFactorProduct hSt s
      = stableLeftAggregate (stableQuotientForest s)
          (stableSelectedOuterContractGraph_stableIds s.1) := by
  rw [stableRightFactorProduct_split, stableRightPrimitiveFactor_product,
    stableForestFactor_product, ← stableLeftAggregate_quotientForest]

end GaugeGeometry.QFT.Combinatorial
