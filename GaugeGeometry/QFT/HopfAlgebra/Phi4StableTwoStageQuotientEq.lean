import GaugeGeometry.QFT.HopfAlgebra.Phi4StableTwoStageRetarget

/-!
# QFT-R1-body-639d — the STABLE two-stage `quot_eq` (final sub-body: the crowning)

Body-639a delivered the EXACT two-stage residual; body-639b the final-star ownership; body-639c the single
global correcting permutation `stableTwoStageTau` and the retarget composition coordinate law
`stableTwoStage_retarget_comp`.  This body PROJECTS 639a's exact residual + 639c's coordinate law onto the three
graph fields, proves the RAW graph equality up to `τ`, the resolved-class equality `stableTwoStage_contract_class_eq`,
and the HEADLINE right-factor equality `stableForestRightTerm_outer_eq_quotientForest` — completing `quot_eq`.

With `s : StablePhi4MixedSplitChoice G hSt` and `Q := stableSelectedOuterContractGraph s.1`:

## Steps
* **Step 1 — exact surviving internal edges.**  `stableTwoStage_survivingInternalEdges_eq` :
  `Q.internalEdges − (stableQuotientForest s).internalEdges =
    (G.internalEdges − s.1.outer.internalEdges).map (A.retargetEdge (starOf G A))` (an EXACT Multiset `Eq`).
  From the exact `qF.internalEdges = (outer.internalEdges − A.internalEdges).map rA` (owner forest sums:
  survivors keep `γ`-edges verbatim, remnants are `B.complementEdges` retargeted) + 639a's `stableOuter_residual_eq`
  + the additive `G.I − A.I = (G.I − outer.I) + (outer.I − A.I)` cancellation.  NO card weakening; NO retarget
  injectivity; `stableOuter_residual_eq` is NOT re-proved.
* **Step 2 — edge/leg coordinate composition.**  `stableTwoStage_retargetEdge_comp` /
  `stableTwoStage_retargetExternalLeg_comp`: `map τ (retarget₂ (retarget₁ x)) = retargetOuter x` per endpoint,
  `edgeId`/`legId`/`sector` preserved by `map`/`retarget` (`rfl`), the endpoint coordinate via
  `stableTwoStage_retarget_comp`.
* **Step 3 — three field equalities** (common RHS `stableOneStageRightGraph s`):
  `stableTwoStageRightGraph_mapPerm_vertices` (via 639c coordinate law + a `contractWithStars.vertices = image
  retargetVertex` identity), `_internalEdges` (Step 1 exact residual + Step 2 edge composition),
  `_externalLegs` (a RAW Multiset `Eq` with id/sector/multiplicity, via `Multiset.map_map` + Step 2 leg
  composition).
* **Step 4 — RAW graph equality.**  `stableTwoStageRightGraph_mapPerm_eq`:
  `(stableTwoStageRightGraph s).mapPerm (stableTwoStageTau s) = stableOneStageRightGraph s` (a raw graph `Eq`
  AFTER the correcting permutation, bundled by the three fields).
* **Step 5 — contracted class equality.**  `stableTwoStage_contract_class_eq`:
  `(stableOneStageRightGraph s).toResolvedClass = (stableTwoStageRightGraph s).toResolvedClass`, erasing `τ` via
  `toResolvedClass_mapPerm` ONLY.
* **Step 6 (HEADLINE) — the right-factor equality.**  `stableForestRightTerm_outer_eq_quotientForest`:
  `stableForestRightTerm s.1.outer … = stableForestRightTerm (stableQuotientForest s) …`, wired through
  body-629 `stableForestRightTerm_class_eq` on Step 5; witness differences by proof irrelevance.

## HALT / red lines
NO re-proof of 639a residual / 639b stars / 639c `τ`+coordinate law.  NO `stableTwoStageTau = stableRemnantTau`;
NO strict canonical-star equality.  Step 1 and Step 3 `externalLegs` are EXACT Multiset `Eq`s (NO card / profile
weakening).  NO `contractClass_eq_of_rightTermFor_eq` backflow.  summand agreement / tensor / `sum_bij` for the
alpha layer / coassoc are NOT entered (the local `Finset.sum_bij` here is a pure owner-forest reindex).  ZERO new
`structure` / `class` / permanent `instance` (one file-local `local instance`; one `private` `ext`); ZERO
forbidden divergence class in any declaration TYPE; ZERO `sorry` / `admit` / `native_decide`; NO `HEq` / `cast` /
graph-data `▸` (Prop-membership `▸` only).  Body-625's no-go and bodies 629-639c / the old carrier are UNEDITED.
Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

open ResolvedFeynmanSubgraph

variable {G : ResolvedFeynmanGraph}

/-- The concrete φ⁴ divergence measure family, registered file-locally (providable instance, NO forbidden
class). -/
noncomputable local instance instPhi4DivergenceMeasureFamily639d : (H : FeynmanGraph) → DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

variable {hSt : StableResolvedBoundaryIds G}

/-- File-local raw-graph extensionality (three fields).  A pure structure `ext`; no forbidden machinery. -/
private theorem resolvedGraph_ext {G₁ G₂ : ResolvedFeynmanGraph}
    (hv : G₁.vertices = G₂.vertices) (hi : G₁.internalEdges = G₂.internalEdges)
    (he : G₁.externalLegs = G₂.externalLegs) : G₁ = G₂ := by
  cases G₁; cases G₂; cases hv; cases hi; cases he; rfl

/-- A proper-forest star-contraction's vertex set is the image of the ambient vertices under the retarget. -/
private theorem contractWithStars_vertices_eq_image {H : ResolvedFeynmanGraph}
    (A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily H)
    (starOf : ResolvedFeynmanSubgraph H → VertexId)
    (hne : A.HasNonemptyComponents) :
    (A.contractWithStars starOf).vertices = H.vertices.image (A.retargetVertex starOf) := by
  rw [ResolvedAdmissibleSubgraph.contractWithStars_vertices]
  ext v
  simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_image,
    ResolvedAdmissibleSubgraph.mem_starVertices]
  constructor
  · rintro (⟨hvH, hvA⟩ | ⟨γ, hγ, rfl⟩)
    · exact ⟨v, hvH, A.retargetVertex_of_not_mem starOf hvA⟩
    · obtain ⟨u, hu⟩ := Finset.card_pos.mp (hne γ hγ)
      exact ⟨u, γ.vertices_subset hu, stableRemnant_retargetVertex_eq_star A starOf hγ hu⟩
  · rintro ⟨u, huH, rfl⟩
    by_cases huA : u ∈ A.vertices
    · obtain ⟨γ, hγ, huγ⟩ := ResolvedAdmissibleSubgraph.mem_vertices.mp huA
      exact Or.inr ⟨γ, hγ, (stableRemnant_retargetVertex_eq_star A starOf hγ huγ).symm⟩
    · refine Or.inl ⟨?_, ?_⟩
      · rw [A.retargetVertex_of_not_mem starOf huA]; exact huH
      · rw [A.retargetVertex_of_not_mem starOf huA]; exact huA

/-! ## Step 1 — the exact surviving internal edges -/

/-- The additive residual split: `A ≤ outer ≤ G` gives `G.I − A.I = (G.I − outer.I) + (outer.I − A.I)`. -/
private theorem stableTwoStage_GI_sub_decomp (s : StablePhi4MixedSplitChoice G hSt) :
    G.internalEdges - (stableSelectedOuter s.1).internalEdges
      = (G.internalEdges - s.1.outer.internalEdges)
        + (s.1.outer.internalEdges - (stableSelectedOuter s.1).internalEdges) := by
  have hAO : (stableSelectedOuter s.1).internalEdges ≤ s.1.outer.internalEdges :=
    stableSelectedOuter_internalEdges_le_outer s
  have hOG : s.1.outer.internalEdges ≤ G.internalEdges :=
    phi4WTriplePrime_internalEdges_le_of_components_le s.1.outer (fun c _ => c.internalEdges_le)
  ext e
  rw [Multiset.count_add, Multiset.count_sub, Multiset.count_sub, Multiset.count_sub]
  have h1 := Multiset.count_le_of_le e hAO
  have h2 := Multiset.count_le_of_le e hOG
  omega

/-- The RIGHT residual is fixed by the selected-outer retarget (right components are disjoint from `A`). -/
private theorem stableBaseRightResidual_map_id (s : StablePhi4MixedSplitChoice G hSt) :
    (stableBaseRightResidual s).map
        ((stableSelectedOuter s.1).retargetEdge
          (phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1)))
      = stableBaseRightResidual s := by
  rw [stableBaseRightResidual, phi4WTriplePrime_map_finset_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  cases hc : s.1.choice a (Finset.mem_attach _ a) with
  | inl b =>
    cases b with
    | true => simp only [Sum.elim_inl, cond_true, Multiset.map_zero]
    | false =>
      simp only [Sum.elim_inl, cond_false]
      have hγR : stableIsRightComponent s.1 a.1 := ⟨a.2, hc⟩
      have hdisj : Disjoint a.1.vertices (stableSelectedOuter s.1).vertices :=
        stableRightComponent_disjoint_selectedOuter s.1 hγR
      conv_rhs => rw [← Multiset.map_id a.1.internalEdges]
      apply Multiset.map_congr rfl
      intro e he
      obtain ⟨hs, ht⟩ := a.1.edges_supported e he
      unfold ResolvedAdmissibleSubgraph.retargetEdge ResolvedFeynmanEdge.retarget
      rw [(stableSelectedOuter s.1).retargetVertex_of_not_mem _
          (Finset.disjoint_left.mp hdisj hs),
        (stableSelectedOuter s.1).retargetVertex_of_not_mem _
          (Finset.disjoint_left.mp hdisj ht)]
      rfl
  | inr B => simp only [Sum.elim_inr, Multiset.map_zero]

/-- The RIGHT-survivor forest's internal edges are the RIGHT residual (survivors keep `γ`'s edges verbatim). -/
private theorem stableRightSurvivorForest_internalEdges_eq_baseRight
    (s : StablePhi4MixedSplitChoice G hSt) :
    (stableRightSurvivorForest s.1).internalEdges = stableBaseRightResidual s := by
  have houterNE : s.1.outer.HasNonemptyComponents :=
    (((mem_phi4WTriplePrimeIndex G s.1.outer).mp s.1.outer_mem).2.2.2.2.1).2.1
  -- LHS = ∑ over right components of γ.internalEdges
  have hL : (stableRightSurvivorForest s.1).internalEdges
      = (stableRightComponents s.1).sum (fun γ => γ.internalEdges) := by
    show (stableRightSurvivorForest s.1).elements.sum (fun c => c.internalEdges) = _
    rw [stableRightSurvivorForest_elements,
      Finset.sum_image (fun x _ y _ hxy => ?_)]
    · rw [Finset.sum_congr rfl (fun γR _ => stableRightSurvivor_internalEdges s.1 _)]
      exact Finset.sum_attach (stableRightComponents s.1) (fun γ => γ.internalEdges)
    · -- injectivity of the survivor map on right components
      have hvert : x.1.vertices = y.1.vertices := by
        have h := congrArg
          (fun (γ : ResolvedFeynmanSubgraph (stableSelectedOuterContractGraph s.1)) => γ.vertices) hxy
        simpa only [stableRightSurvivor_vertices] using h
      have hxO : x.1 ∈ s.1.outer.elements := ((stableMem_rightComponents s.1).mp x.2).1
      have hyO : y.1 ∈ s.1.outer.elements := ((stableMem_rightComponents s.1).mp y.2).1
      obtain ⟨u, hu⟩ := Finset.card_pos.mp (houterNE x.1 hxO)
      have huY : u ∈ y.1.vertices := hvert ▸ hu
      by_cases hEq : x.1 = y.1
      · exact Subtype.ext hEq
      · exact absurd huY (Finset.disjoint_left.mp (s.1.outer.pairwiseDisjoint hxO hyO hEq) hu)
  -- baseRight = ∑ over right components of γ.internalEdges
  have hR : stableBaseRightResidual s
      = (stableRightComponents s.1).sum (fun γ => γ.internalEdges) := by
    have h1 : (stableRightComponents s.1).sum (fun γ => γ.internalEdges)
        = ∑ a ∈ s.1.outer.elements.attach,
            (if stableIsRightComponent s.1 a.1 then a.1.internalEdges else 0) := by
      show (s.1.outer.elements.filter (stableIsRightComponent s.1)).sum (fun γ => γ.internalEdges) = _
      rw [Finset.sum_filter]
      exact (Finset.sum_attach s.1.outer.elements
        (fun c => if stableIsRightComponent s.1 c then c.internalEdges else 0)).symm
    rw [h1, stableBaseRightResidual]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    cases hc : s.1.choice a (Finset.mem_attach _ a) with
    | inl b =>
      cases b with
      | false =>
        rw [if_pos ⟨a.2, hc⟩]
        simp only [Sum.elim_inl, cond_false]
      | true =>
        rw [if_neg (by
          rintro ⟨h', hlt⟩; rw [hc] at hlt; simp at hlt)]
        simp only [Sum.elim_inl, cond_true]
    | inr B =>
      rw [if_neg (by
        rintro ⟨h', hlt⟩; rw [hc] at hlt; simp at hlt)]
      simp only [Sum.elim_inr]
  rw [hL, hR]

/-- The remnant forest's internal edges are the inner-FOREST-complement residual, retargeted. -/
private theorem stableRemnantForest_internalEdges_eq_baseForest_map
    (s : StablePhi4MixedSplitChoice G hSt) :
    (stableRemnantForest s).internalEdges
      = (stableBaseForestResidual s).map
          ((stableSelectedOuter s.1).retargetEdge
            (phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1))) := by
  -- LHS = (∑ over forest occurrences of B.complementEdges).map rA
  have hL : (stableRemnantForest s).internalEdges
      = (∑ γF ∈ (stableForestComponents s).attach,
            (stableForestComponentOccurrence γF).B.1.complementEdges).map
          ((stableSelectedOuter s.1).retargetEdge
            (phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1))) := by
    rw [phi4WTriplePrime_map_finset_sum]
    show (stableRemnantForest s).elements.sum (fun c => c.internalEdges) = _
    rw [stableRemnantForest_elements,
      Finset.sum_image (fun x _ y _ hxy => ?_)]
    · refine Finset.sum_congr rfl (fun γF _ => ?_)
      rw [stableRemnantComponent_internalEdges, stableRemnant_internalEdges_eq]
    · -- injectivity of the remnant map on forest components
      have hvert : (stableRemnantComponent (stableForestComponentOccurrence x)).vertices
          = (stableRemnantComponent (stableForestComponentOccurrence y)).vertices :=
        congrArg
          (fun (γ : ResolvedFeynmanSubgraph (stableSelectedOuterContractGraph s.1)) => γ.vertices) hxy
      by_contra hne
      have hxy' : x ≠ y := fun h => hne (by rw [h])
      obtain ⟨u, hu⟩ :=
        Finset.card_pos.mp (stableRemnant_isNonempty (stableForestComponentOccurrence x))
      have huY : u ∈ (stableRemnantComponent (stableForestComponentOccurrence y)).vertices := hvert ▸ hu
      exact absurd huY (Finset.disjoint_left.mp
        (stableRemnant_pairwiseDisjoint _ _
          (fun h => hxy' (Subtype.ext (by
            have := (stableForestComponentOccurrence_owner x).symm.trans (h.trans
              (stableForestComponentOccurrence_owner y))
            exact this)))) hu)
  -- baseForest = ∑ over forest occurrences of B.complementEdges
  have hsub : (s.1.outer.elements.attach.filter
        (fun a => (s.1.choice a (Finset.mem_attach _ a)).isRight = true)).sum
        (fun a => Sum.elim (fun _ => (0 : Multiset ResolvedFeynmanEdge))
          (fun B => B.1.complementEdges) (s.1.choice a (Finset.mem_attach _ a)))
      = stableBaseForestResidual s := by
    rw [stableBaseForestResidual]
    refine Finset.sum_subset (Finset.filter_subset _ _) (fun a _ ha => ?_)
    have ha' : ¬ ((s.1.choice a (Finset.mem_attach _ a)).isRight = true) := fun hp =>
      ha (Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, hp⟩)
    cases hc : s.1.choice a (Finset.mem_attach _ a) with
    | inl b => simp only [Sum.elim_inl]
    | inr B => exact absurd (by rw [hc]; rfl) ha'
  have hR : stableBaseForestResidual s
      = ∑ γF ∈ (stableForestComponents s).attach,
          (stableForestComponentOccurrence γF).B.1.complementEdges := by
    rw [← hsub]
    refine (Finset.sum_bij
      (fun γF _ => (stableForestComponentOccurrence γF).γ)
      (fun γF _ => ?_) (fun x _ y _ hxy => ?_) (fun a ha => ?_) (fun γF _ => ?_)).symm
    · -- lands in the filter
      refine Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, ?_⟩
      simp only [(stableForestComponentOccurrence γF).hchoice, Sum.isRight]
    · -- injective
      apply Subtype.ext
      have h := congrArg Subtype.val hxy
      rw [stableForestComponentOccurrence_owner, stableForestComponentOccurrence_owner] at h
      exact h
    · -- surjective
      have hp : (s.1.choice a (Finset.mem_attach _ a)).isRight = true := (Finset.mem_filter.mp ha).2
      have hF : stableIsForestComponent s a.1 := by
        cases hc : s.1.choice a (Finset.mem_attach _ a) with
        | inl b => rw [hc] at hp; simp at hp
        | inr B => exact ⟨a.2, B, hc⟩
      exact ⟨⟨a.1, (stableMem_forestComponents s).mpr ⟨a.2, hF⟩⟩, Finset.mem_attach _ _,
        Subtype.ext (stableForestComponentOccurrence_owner _)⟩
    · -- summand match
      simp only [(stableForestComponentOccurrence γF).hchoice, Sum.elim_inr]
  rw [hL, hR]

/-- **body-639d (Step 1, helper) — the EXACT quotient-forest internal edges** as the input residual retargeted:
`qF.internalEdges = (outer.internalEdges − A.internalEdges).map (A.retargetEdge (starOf G A))`.  NO card
weakening; NO retarget injectivity.  Survivors keep `γ`-edges verbatim (`baseRight` is `rA`-fixed), remnants are
the inner-complement retargeted; owner-forest sums + 639a's `stableOuter_residual_eq`. -/
theorem stableQuotientForest_internalEdges_eq_residual (s : StablePhi4MixedSplitChoice G hSt) :
    (stableQuotientForest s).internalEdges
      = (s.1.outer.internalEdges - (stableSelectedOuter s.1).internalEdges).map
          ((stableSelectedOuter s.1).retargetEdge
            (phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1))) := by
  -- qF.internalEdges = RSF.internalEdges + RF.internalEdges
  have hUnion : (stableQuotientForest s).internalEdges
      = (stableRightSurvivorForest s.1).internalEdges + (stableRemnantForest s).internalEdges := by
    show (stableQuotientForest s).elements.sum (fun c => c.internalEdges) = _
    rw [stableQuotientForest_elements]
    exact Finset.sum_union (stableSurvivorRemnant_elements_disjoint s)
  rw [hUnion, stableRightSurvivorForest_internalEdges_eq_baseRight s,
    stableRemnantForest_internalEdges_eq_baseForest_map s,
    stableOuter_residual_eq s, Multiset.map_add, stableBaseRightResidual_map_id s]

/-- **body-639d (Step 1, HEADLINE) — the EXACT surviving internal edges.**  The two-stage quotient complement
edges are EXACTLY the one-stage input residual retargeted through the selected outer.  An EXACT Multiset `Eq`. -/
theorem stableTwoStage_survivingInternalEdges_eq (s : StablePhi4MixedSplitChoice G hSt) :
    (stableSelectedOuterContractGraph s.1).internalEdges - (stableQuotientForest s).internalEdges
      = (G.internalEdges - s.1.outer.internalEdges).map
          ((stableSelectedOuter s.1).retargetEdge
            (phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1))) := by
  have hQI : (stableSelectedOuterContractGraph s.1).internalEdges
      = (G.internalEdges - (stableSelectedOuter s.1).internalEdges).map
          ((stableSelectedOuter s.1).retargetEdge
            (phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1))) := by
    show ((stableSelectedOuter s.1).contractWithStars
        (phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1))).internalEdges = _
    rw [ResolvedAdmissibleSubgraph.contractWithStars_internalEdges,
      ResolvedAdmissibleSubgraph.complementEdges]
  rw [hQI, stableQuotientForest_internalEdges_eq_residual s,
    stableTwoStage_GI_sub_decomp s, Multiset.map_add,
    add_tsub_cancel_right]

/-! ## Step 2 — edge/leg coordinate composition (per endpoint, via 639c HEADLINE) -/

/-- **body-639d (Step 2, EDGE) — the two-stage retarget edge composition.**  `map τ (retarget₂ (retarget₁ e)) =
retargetOuter e` for an internal edge with `G`-supported endpoints; `edgeId`/`sector` preserved, endpoints via
`stableTwoStage_retarget_comp`. -/
theorem stableTwoStage_retargetEdge_comp (s : StablePhi4MixedSplitChoice G hSt)
    {e : ResolvedFeynmanEdge} (hs : e.source ∈ G.vertices) (ht : e.target ∈ G.vertices) :
    ResolvedFeynmanEdge.map (stableTwoStageTau s)
        ((stableQuotientForest s).retargetEdge
          (phi4WTriplePrimeCanonicalSupply.starOf (stableSelectedOuterContractGraph s.1)
            (stableQuotientForest s))
          ((stableSelectedOuter s.1).retargetEdge
            (phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1)) e))
      = s.1.outer.retargetEdge (phi4WTriplePrimeCanonicalSupply.starOf G s.1.outer) e := by
  unfold ResolvedAdmissibleSubgraph.retargetEdge ResolvedFeynmanEdge.retarget ResolvedFeynmanEdge.map
  rw [stableTwoStage_retarget_comp s hs, stableTwoStage_retarget_comp s ht]

/-- **body-639d (Step 2, LEG) — the two-stage retarget leg composition.**  `map τ (retarget₂ (retarget₁ ℓ)) =
retargetOuter ℓ` for an external leg with `G`-supported attachment; `legId`/`sector` preserved, attachment via
`stableTwoStage_retarget_comp`. -/
theorem stableTwoStage_retargetExternalLeg_comp (s : StablePhi4MixedSplitChoice G hSt)
    {ℓ : ResolvedExternalLeg} (h : ℓ.attachedTo ∈ G.vertices) :
    ResolvedExternalLeg.map (stableTwoStageTau s)
        ((stableQuotientForest s).retargetExternalLeg
          (phi4WTriplePrimeCanonicalSupply.starOf (stableSelectedOuterContractGraph s.1)
            (stableQuotientForest s))
          ((stableSelectedOuter s.1).retargetExternalLeg
            (phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1)) ℓ))
      = s.1.outer.retargetExternalLeg (phi4WTriplePrimeCanonicalSupply.starOf G s.1.outer) ℓ := by
  unfold ResolvedAdmissibleSubgraph.retargetExternalLeg ResolvedExternalLeg.retarget ResolvedExternalLeg.map
  rw [stableTwoStage_retarget_comp s h]

/-! ## Step 3 — the three field equalities (common RHS `stableOneStageRightGraph s`) -/

/-- **body-639d (Step 3, VERTICES).** -/
theorem stableTwoStageRightGraph_mapPerm_vertices (s : StablePhi4MixedSplitChoice G hSt) :
    ((stableTwoStageRightGraph s).mapPerm (stableTwoStageTau s)).vertices
      = (stableOneStageRightGraph s).vertices := by
  have hAne : (stableSelectedOuter s.1).HasNonemptyComponents :=
    (stableSelectedOuter_isProperForest s.1).2.1
  have hqFne : (stableQuotientForest s).HasNonemptyComponents :=
    (stableQuotientForest_isProperForest s).2.1
  have houterne : s.1.outer.HasNonemptyComponents :=
    (((mem_phi4WTriplePrimeIndex G s.1.outer).mp s.1.outer_mem).2.2.2.2.1).2.1
  have hQV : (stableSelectedOuterContractGraph s.1).vertices
      = G.vertices.image ((stableSelectedOuter s.1).retargetVertex
          (phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1))) := by
    show ((stableSelectedOuter s.1).contractWithStars _).vertices = _
    exact contractWithStars_vertices_eq_image (stableSelectedOuter s.1) _ hAne
  show (stableTwoStageRightGraph s).vertices.image (stableTwoStageTau s)
      = (stableOneStageRightGraph s).vertices
  rw [stableTwoStageRightGraph, stableOneStageRightGraph,
    contractWithStars_vertices_eq_image (stableQuotientForest s) _ hqFne,
    contractWithStars_vertices_eq_image s.1.outer _ houterne,
    Finset.image_image, hQV, Finset.image_image]
  refine Finset.image_congr (fun v hv => ?_)
  simp only [Function.comp]
  exact stableTwoStage_retarget_comp s hv

/-- **body-639d (Step 3, INTERNAL EDGES).** -/
theorem stableTwoStageRightGraph_mapPerm_internalEdges (s : StablePhi4MixedSplitChoice G hSt) :
    ((stableTwoStageRightGraph s).mapPerm (stableTwoStageTau s)).internalEdges
      = (stableOneStageRightGraph s).internalEdges := by
  have hAmb : ResolvedAmbientSupported G :=
    ((mem_phi4WTriplePrimeIndex G s.1.outer).mp s.1.outer_mem).1
  show (stableTwoStageRightGraph s).internalEdges.map (ResolvedFeynmanEdge.map (stableTwoStageTau s))
      = (stableOneStageRightGraph s).internalEdges
  rw [stableTwoStageRightGraph, stableOneStageRightGraph,
    ResolvedAdmissibleSubgraph.contractWithStars_internalEdges,
    ResolvedAdmissibleSubgraph.contractWithStars_internalEdges,
    ResolvedAdmissibleSubgraph.complementEdges,
    ResolvedAdmissibleSubgraph.complementEdges,
    stableTwoStage_survivingInternalEdges_eq s,
    Multiset.map_map, Multiset.map_map]
  refine Multiset.map_congr rfl (fun e he => ?_)
  have heG : e ∈ G.internalEdges := Multiset.mem_of_le (Multiset.sub_le_self _ _) he
  obtain ⟨hs, ht⟩ := hAmb.1 e heG
  simp only [Function.comp]
  exact stableTwoStage_retargetEdge_comp s hs ht

/-- **body-639d (Step 3, EXTERNAL LEGS).**  RAW Multiset `Eq` with id/sector/multiplicity. -/
theorem stableTwoStageRightGraph_mapPerm_externalLegs (s : StablePhi4MixedSplitChoice G hSt) :
    ((stableTwoStageRightGraph s).mapPerm (stableTwoStageTau s)).externalLegs
      = (stableOneStageRightGraph s).externalLegs := by
  have hAmb : ResolvedAmbientSupported G :=
    ((mem_phi4WTriplePrimeIndex G s.1.outer).mp s.1.outer_mem).1
  have hQE : (stableSelectedOuterContractGraph s.1).externalLegs
      = G.externalLegs.map ((stableSelectedOuter s.1).retargetExternalLeg
          (phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1))) := by
    show ((stableSelectedOuter s.1).contractWithStars _).externalLegs = _
    rw [ResolvedAdmissibleSubgraph.contractWithStars_externalLegs]
  show (stableTwoStageRightGraph s).externalLegs.map (ResolvedExternalLeg.map (stableTwoStageTau s))
      = (stableOneStageRightGraph s).externalLegs
  rw [stableTwoStageRightGraph, stableOneStageRightGraph,
    ResolvedAdmissibleSubgraph.contractWithStars_externalLegs,
    ResolvedAdmissibleSubgraph.contractWithStars_externalLegs,
    hQE, Multiset.map_map, Multiset.map_map]
  refine Multiset.map_congr rfl (fun ℓ hℓ => ?_)
  simp only [Function.comp]
  exact stableTwoStage_retargetExternalLeg_comp s (hAmb.2 ℓ hℓ)

/-! ## Step 4 — the RAW graph equality (after the correcting permutation) -/

/-- **body-639d (Step 4) — the RAW two-stage right graph equality up to `τ`.**  `(stableTwoStageRightGraph s)`
relabeled by the single global correcting permutation `stableTwoStageTau s` IS the one-stage right graph.  A raw
`ResolvedFeynmanGraph` equality, bundling the three Step-3 fields. -/
theorem stableTwoStageRightGraph_mapPerm_eq (s : StablePhi4MixedSplitChoice G hSt) :
    (stableTwoStageRightGraph s).mapPerm (stableTwoStageTau s) = stableOneStageRightGraph s :=
  resolvedGraph_ext
    (stableTwoStageRightGraph_mapPerm_vertices s)
    (stableTwoStageRightGraph_mapPerm_internalEdges s)
    (stableTwoStageRightGraph_mapPerm_externalLegs s)

/-! ## Step 5 — the contracted class equality (erasing `τ`) -/

/-- **body-639d (Step 5) — the two-stage contracted CLASS equality.**  The one-stage and two-stage right graphs
have the same resolved id-preserving class; `τ` is erased by `toResolvedClass_mapPerm` ONLY. -/
theorem stableTwoStage_contract_class_eq (s : StablePhi4MixedSplitChoice G hSt) :
    (stableOneStageRightGraph s).toResolvedClass = (stableTwoStageRightGraph s).toResolvedClass := by
  rw [← stableTwoStageRightGraph_mapPerm_eq s, ResolvedFeynmanGraph.toResolvedClass_mapPerm]

/-! ## Step 6 (HEADLINE) — the right-factor equality -/

/-- **body-639d (Step 6, HEADLINE) — the stable right-factor `quot_eq`.**  The OUTER right term
`stableForestRightTerm s.1.outer …` equals the QUOTIENT-FOREST right term `stableForestRightTerm
(stableQuotientForest s) …`, wired through body-629 `stableForestRightTerm_class_eq` on the two-stage contracted
class equality (Step 5); the CD / stable witnesses differ only by proof irrelevance.  This is the load-bearing
`quot_eq` factor of the stable Δᵣ-coassociativity. -/
theorem stableForestRightTerm_outer_eq_quotientForest (s : StablePhi4MixedSplitChoice G hSt) :
    stableForestRightTerm s.1.outer
        (phi4WTriplePrimeCanonicalSupply.starOf G s.1.outer)
        (phi4WTriplePrimeCanonicalSupply.hCD G s.1.outer s.1.outer_mem)
        (stableResolvedBoundaryIds_contractWithStars s.1.outer
          (phi4WTriplePrimeCanonicalSupply.starOf G s.1.outer) hSt)
      = stableForestRightTerm (stableQuotientForest s)
          (phi4WTriplePrimeCanonicalSupply.starOf (stableSelectedOuterContractGraph s.1)
            (stableQuotientForest s))
          (phi4WTriplePrimeCanonicalSupply.hCD (stableSelectedOuterContractGraph s.1)
            (stableQuotientForest s) (stableQuotientForest_mem s))
          (stableResolvedBoundaryIds_contractWithStars (stableQuotientForest s)
            (phi4WTriplePrimeCanonicalSupply.starOf (stableSelectedOuterContractGraph s.1)
              (stableQuotientForest s))
            (stableSelectedOuterContractGraph_stableIds s.1)) :=
  stableForestRightTerm_class_eq _ _ _ _ _ _ _ _ (stableTwoStage_contract_class_eq s)

end GaugeGeometry.QFT.Combinatorial
