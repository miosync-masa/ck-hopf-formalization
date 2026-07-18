import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocMultisetLegLift

/-!
# R-6c-body-376 — bank-3a: `legLift` reduced to the CK leg-completeness condition (PROVED)

Three-hundred-and-seventy-sixth genuine-body step — the leg socket, narrowed from the full `ResolvedTouchedLegLiftDatum`
witness to the honest CK condition `touchedLegComplete`, via body-375's non-injective multiset lift and an ADDITIVE
decomposition (no multiset subtraction / no `map`-subtraction lemma).

**The retarget is `touchedOuterForest`-specific, so the ambient coverage is NOT the generic `externalLegs_le`.**  The
touched retarget differs from `z.1.1`'s full retarget on the untouched components, so `δ.externalLegs ≤
G.externalLegs.map (touched retarget)` is a GENUINE CK completeness fact about the concrete model's touched components,
not derivable from `δ.externalLegs_le`.  `touchedLegComplete` therefore bundles the two honest touched-leg inclusions:

```text
C := (touchedOuterForest).externalLegs.map retarget
touchedLegComplete := (C ≤ δ.externalLegs) ∧ (δ.externalLegs ≤ G.externalLegs.map retarget)
```

From it: `G.externalLegs = T + S`, `δ.externalLegs = C + R` (additive), the ambient gives `C + R ≤ C + S.map retarget`,
cancel to `R ≤ S.map retarget`, body-375 lifts `R = L.map retarget` with `L ≤ S`, and `legs := T + L` discharges all
four datum fields by `map_add` / `le_add_right` / `add_le_add_left` — no subtraction anywhere.

Landed axiom-clean: `touchedLegComplete`, `touchedLegLiftDatum_of_complete`, `valueCore_of_legComplete`.

Per the HALT: bank-3a's leg residual is now exactly `touchedLegComplete` + its canonical-lift `parentCD` (coupled, NOT a
different `legLift`); carrier membership stays ZERO; `parentCD` is an honest power-counting input, not derived.  No
facade, no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

set_option linter.unusedSectionVars false

/-- **R-6c-body-376 — admissible external legs bounded by the ambient** (pairwise-disjoint analogue of the
internal-edge lemma). -/
theorem resolvedAdmissibleSubgraph_externalLegs_le_of_pairwise
    (A : ResolvedAdmissibleSubgraph G) (hA : A.IsPairwiseDisjoint) :
    A.externalLegs ≤ G.externalLegs := by
  classical
  rw [Multiset.le_iff_count]
  intro ℓ
  by_cases hℓA : ℓ ∈ A.externalLegs
  · obtain ⟨γ, hγ, hℓγ⟩ := Multiset.mem_sum.mp hℓA
    have hzero : ∀ δ ∈ A.elements, δ ≠ γ → δ.externalLegs.count ℓ = 0 := by
      intro δ hδ hne
      by_cases hℓδ : ℓ ∈ δ.externalLegs
      · have hdisj := hA hδ hγ hne
        exact False.elim ((Finset.disjoint_left.mp hdisj (δ.legs_supported ℓ hℓδ))
          (γ.legs_supported ℓ hℓγ))
      · exact Multiset.count_eq_zero.mpr hℓδ
    unfold ResolvedAdmissibleSubgraph.externalLegs
    rw [multiset_count_finset_sum]
    calc (∑ x ∈ A.elements, Multiset.count ℓ x.externalLegs)
        = γ.externalLegs.count ℓ := by
          rw [Finset.sum_eq_single γ]
          · intro δ hδ hne; exact hzero δ hδ hne
          · intro hγnot; exact False.elim (hγnot hγ)
      _ ≤ G.externalLegs.count ℓ := Multiset.count_le_of_le ℓ γ.externalLegs_le
  · rw [Multiset.count_eq_zero.mpr hℓA]; exact Nat.zero_le _

/-- **R-6c-body-376 — the CK leg-completeness condition.**  The touched forest's retargeted legs are contained in
`δ`'s, and `δ`'s legs are covered by the touched retarget of `G`'s legs. -/
def touchedLegComplete (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))) : Prop :=
  (touchedOuterForest z δ).externalLegs.map ((touchedOuterForest z δ).retargetExternalLeg (D.starOf G z.1.1))
      ≤ δ.externalLegs ∧
  δ.externalLegs
      ≤ G.externalLegs.map ((touchedOuterForest z δ).retargetExternalLeg (D.starOf G z.1.1))

/-- **R-6c-body-376 — the leg-lift datum from CK completeness** (additive decomposition + body-375). -/
noncomputable def touchedLegLiftDatum_of_complete (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
    (hcomplete : touchedLegComplete z δ) : ResolvedTouchedLegLiftDatum z δ := by
  have hCle := hcomplete.1
  have hDamb := hcomplete.2
  have hTle : (touchedOuterForest z δ).externalLegs ≤ G.externalLegs :=
    resolvedAdmissibleSubgraph_externalLegs_le_of_pairwise _ (touchedOuterForest z δ).isPairwiseDisjoint
  set S := (Multiset.le_iff_exists_add.mp hTle).choose with hSdef
  have hGeq : G.externalLegs = (touchedOuterForest z δ).externalLegs + S :=
    (Multiset.le_iff_exists_add.mp hTle).choose_spec
  set R := (Multiset.le_iff_exists_add.mp hCle).choose with hRdef
  have hDeq : δ.externalLegs = (touchedOuterForest z δ).externalLegs.map
      ((touchedOuterForest z δ).retargetExternalLeg (D.starOf G z.1.1)) + R :=
    (Multiset.le_iff_exists_add.mp hCle).choose_spec
  have hcancel : R ≤ S.map ((touchedOuterForest z δ).retargetExternalLeg (D.starOf G z.1.1)) := by
    apply le_of_add_le_add_left (a := (touchedOuterForest z δ).externalLegs.map
      ((touchedOuterForest z δ).retargetExternalLeg (D.starOf G z.1.1)))
    calc (touchedOuterForest z δ).externalLegs.map
              ((touchedOuterForest z δ).retargetExternalLeg (D.starOf G z.1.1)) + R
        = δ.externalLegs := hDeq.symm
      _ ≤ G.externalLegs.map ((touchedOuterForest z δ).retargetExternalLeg (D.starOf G z.1.1)) := hDamb
      _ = ((touchedOuterForest z δ).externalLegs + S).map
              ((touchedOuterForest z δ).retargetExternalLeg (D.starOf G z.1.1)) := by rw [hGeq]
      _ = (touchedOuterForest z δ).externalLegs.map
              ((touchedOuterForest z δ).retargetExternalLeg (D.starOf G z.1.1))
            + S.map ((touchedOuterForest z δ).retargetExternalLeg (D.starOf G z.1.1)) :=
          Multiset.map_add _ _ _
  set L := (multiset_exists_le_of_le_map hcancel).choose with hLdef
  have hLS : L ≤ S := (multiset_exists_le_of_le_map hcancel).choose_spec.1
  have hLeq : L.map ((touchedOuterForest z δ).retargetExternalLeg (D.starOf G z.1.1)) = R :=
    (multiset_exists_le_of_le_map hcancel).choose_spec.2
  exact
    { legs := (touchedOuterForest z δ).externalLegs + L
      legs_le := by rw [hGeq]; gcongr
      map_eq := by
        rw [Multiset.map_add, hLeq, touchedLocalComponent_externalLegs]; exact hDeq.symm
      touched_le := Multiset.le_add_right _ _ }

/-- **R-6c-body-376 — the value core from CK leg-completeness**, with `parentCD` coupled to the canonical lift. -/
noncomputable def valueCore_of_legComplete
    (hE : ∀ {G : ResolvedFeynmanGraph} (_z : ForestBlockCodType D G), ∀ e ∈ G.internalEdges,
      e.source ∈ G.vertices ∧ e.target ∈ G.vertices)
    (hL : ∀ {G : ResolvedFeynmanGraph} (_z : ForestBlockCodType D G), ∀ ℓ ∈ G.externalLegs,
      ℓ.attachedTo ∈ G.vertices)
    (legComplete : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
      (δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) // x ∈ forestDomain z}),
      touchedLegComplete z δ.1)
    (parentCD : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
      (δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) // x ∈ forestDomain z}),
      (localizedParentWithTouchedLegs z δ.1
        (touchedLegLiftDatum_of_complete z δ.1 (legComplete z δ)) (hE z) (hL z)).forget.IsConnectedDivergent) :
    ResolvedMultiStarDecontractionValueCoreSupply D where
  hE := hE
  hL := hL
  legLift := fun z δ => touchedLegLiftDatum_of_complete z δ.1 (legComplete z δ)
  parentCD := parentCD

end GaugeGeometry.QFT.Combinatorial
