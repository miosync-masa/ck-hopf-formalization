import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSummandAgreeValueCanonical
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestBlockBijection
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaValueForwardLayer
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaInverseCover

/-!
# R-6c-body-481 — the alpha filtered bijection side + native conditional coassoc (PROVED)

Four-hundred-and-eighty-first genuine-body step — the major connection point.  The strong alpha cover (body-480) is kept
at full strength internally, and weakened to the raid-boss's raw/`Finset` shape ONLY at the boundary (the finite-domain
restriction hypotheses required by `ResolvedForestBlockBijectionSupply`'s field types).  The whole path stays on the
alpha filtered `V`, keeping filtered quotient ownership to the end — no detour through the old `V`.

* `ResolvedSummandAgreeAlphaValueSupply` / `summand_agree_alpha_value_of_value` — body-259 mirrored with the ownership
  corrected: `V.quotientForestRaw q` / `V.hcross q` / `V.union_eq q` / `V.hRdisj q` / `V.quot_eq q` on the FILTERED `q`,
  survivor / remnant / Measure still total on `q.1`;
* `ResolvedFilteredAlphaBijectionSideSupply` — the alpha bijection side (`F`, filtered `V`, the strong alpha cover, and
  the base model leaves); the forward quotient membership is body-472-FREE, so it is NOT a field;
* `toForestBlockBijectionSupply` — the raid-boss adapter (`toFun := fwdMapFilteredAlphaValue`, `invFun :=
  (cover.witnessSplit r).1`, `toFun_mem` outer = `mem_attach` / quotient = body-472 free, `invFun_mem` / round-trips from
  the cover, `summand_agree` derived); the finite codomain restriction `hr` is consumed only to satisfy the field type;
* `coassoc_gen` / `coassoc_gen_of_recovered_preimage_alpha_value` — native `Δᵣ`-coassociativity, the latter issued from a
  body-479 round-trip leaf via `R.toCover`, deriving the forward membership internally;
* the compatibility anchors (alpha summand over `V.toFiltered` is the legacy summand by `rfl`; the adapter's `toFun` is the
  alpha forward map by `rfl`).

Per the HALT/guards: this is NOT plugged into the body-445 final construction; the 71-file in-place migration is NOT
started; `quotient_mem` / `quot_eq` are NOT proved (carried as `V` ownership); `forest_value_eq` / the forward geometry
leaves are NOT derived; strict `StarProm` / `InnerStarRaw` NOT restored; the old cover is NOT claimed to yield the strong
alpha cover; body-445 stays a valid conditional.  NOT the unconditional theorem.  No facade, no flat term, no `forgetHopf`,
no rep/perm, and NO `promote_collapse` / singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

variable {D : ResolvedCoproductProperForestData}

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-- **R-6c-body-481 — the alpha value summand agreement supply.**  The term equality with outer/quotient from
`fwdMapFilteredAlphaValue` (alpha value root). -/
structure ResolvedSummandAgreeAlphaValueSupply (F : ResolvedSelectedOuterFilteredMemSupply D)
    (V : ResolvedFilteredConcreteSummandValueSupply D) where
  /-- The resolved split-choice term factors as `leftTerm(outer) ⊗ (leftTerm(quot) ⊗ rightTerm(quot))`, all over the
  alpha value root. -/
  summand_agree_value : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G),
    D.resolvedSplitChoiceTerm (q.1 : ResolvedCoassocSplitChoice D G)
      = (D.supply G).leftTerm (fwdMapFilteredAlphaValue F V q).1 ⊗ₜ[ℚ]
          ((D.supply ((fwdMapFilteredAlphaValue F V q).1.1.contractWithStars
              (D.starOf G (fwdMapFilteredAlphaValue F V q).1.1))).leftTerm (fwdMapFilteredAlphaValue F V q).2
            ⊗ₜ[ℚ] (D.supply ((fwdMapFilteredAlphaValue F V q).1.1.contractWithStars
              (D.starOf G (fwdMapFilteredAlphaValue F V q).1.1))).rightTerm (fwdMapFilteredAlphaValue F V q).2)

/-- **R-6c-body-481 — the canonical alpha value summand agreement.**  Body-259 mirrored: the quotient-owned factor
inputs read the FILTERED `q` (`V.quotientForestRaw q` / `V.hcross q` / `V.union_eq q` / `V.hRdisj q` / `V.quot_eq q`);
survivor / remnant / Measure stay total on `q.1`. -/
noncomputable def summand_agree_alpha_value_of_value (F : ResolvedSelectedOuterFilteredMemSupply D)
    (V : ResolvedFilteredConcreteSummandValueSupply D) : ResolvedSummandAgreeAlphaValueSupply F V where
  summand_agree_value := fun {G} q => by
    have hL := resolved_selectedOuter_left_factor_eq_of_parts_raw q.1
      ((resolvedConcreteForestPromoteSupply D G).leftOf q.1)
      ((resolvedConcreteForestPromoteSupply D G).promotedOf q.1)
      ((resolvedConcreteForestPromoteSupply D G).cross q.1)
      (V.Measure.leftHDisj q.1)
      (left_primitive_factor_concrete q.1)
      (promoted_factor_of_hPD q.1 (V.Measure.promotedHPD q.1))
    have hR := resolved_quotientForest_right_factor_eq_of_parts q.1 _
      (V.quotientForestRaw q)
      (V.Survivor.survivor.rightSurvivorForest q.1)
      (V.Remnant.remnant.remnantForest q.1)
      (V.hcross q) (V.union_eq q) (V.hRdisj q)
      (V.Survivor.toRightPrimitiveSurvivalTransportSupply.right_primitive_factor q.1)
      (V.Remnant.remnant_factor q.1)
    exact resolved_splitChoice_summand_agree_of_factor_eqs q.1.1 q.1.2
      (fwdMapFilteredAlphaValue F V q).1 (fwdMapFilteredAlphaValue F V q).2 hL hR (V.quot_eq q)

/-- **R-6c-body-481 — the alpha filtered bijection side.**  Everything on the alpha filtered `V`; the strong alpha cover
(body-480) is held at full strength; the forward quotient membership is body-472-FREE (not a field); the summand agreement
is derived from `F + V`. -/
structure ResolvedFilteredAlphaBijectionSideSupply (D : ResolvedCoproductProperForestData) where
  /-- The filtered selected-outer carrier closure (body-245). -/
  F : ResolvedSelectedOuterFilteredMemSupply D
  /-- The alpha-native filtered summand value root (body-470). -/
  V : ResolvedFilteredConcreteSummandValueSupply D
  /-- The strong alpha witnessSplit cover — the filtered inverse map + its unconditional round-trips (body-480). -/
  cover : ResolvedWitnessSplitFilteredAlphaValueCoverSupply F V
  /-- Every carrier forest is a proper forest (base model leaf). -/
  carrier_isProperForest : ∀ (G : ResolvedFeynmanGraph) (A : ResolvedAdmissibleSubgraph G),
    A ∈ D.carrier G → A.IsProperForest
  /-- A representative graph for each generator (base model leaf). -/
  rep : ResolvedHopfGen → ResolvedFeynmanGraph
  /-- The representative is connected-divergent. -/
  repCD : ∀ x : ResolvedHopfGen, (rep x).forget.toClass.IsConnectedDivergent
  /-- The representative's generator IS `x`. -/
  rep_gen : ∀ x : ResolvedHopfGen, x = (rep x).toResolvedHopfGen (repCD x)

namespace ResolvedFilteredAlphaBijectionSideSupply

/-- **R-6c-body-481 — inhabiting the raid-boss `ResolvedForestBlockBijectionSupply`** from the alpha filtered side.  The
inverse comes from the strong alpha cover (its filtered witness's `.1`); the finite codomain restriction `hr` is consumed
only to satisfy the raid-boss field types, never used to build the inverse. -/
noncomputable def toForestBlockBijectionSupply (B : ResolvedFilteredAlphaBijectionSideSupply D) :
    ResolvedForestBlockBijectionSupply D where
  toFun := fun _ q hq => fwdMapFilteredAlphaValue B.F B.V ⟨q, hq⟩
  invFun := fun _ r _ => (B.cover.witnessSplit r).1
  toFun_mem := fun G q hq => by
    simp only [forestBlockCodFinset, Finset.mem_sigma]
    exact ⟨Finset.mem_attach _ _, (forwardQuotientMemAlphaValueOfValue B.F B.V).quotient_mem ⟨q, hq⟩⟩
  invFun_mem := fun _ r _hr => (B.cover.witnessSplit r).2
  left_inv := fun _ q hq => congrArg Subtype.val (B.cover.backward_witness ⟨q, hq⟩)
  right_inv := fun _ r _hr => B.cover.forward_witness r
  summand_agree := fun _ q hq => (summand_agree_alpha_value_of_value B.F B.V).summand_agree_value ⟨q, hq⟩
  carrier_isProperForest := B.carrier_isProperForest
  rep := B.rep
  repCD := B.repCD
  rep_gen := B.rep_gen

/-- **R-6c-body-481 — the adapter's forward map is the alpha forward map** (`rfl`, regression anchor). -/
theorem toForestBlockBijectionSupply_toFun (B : ResolvedFilteredAlphaBijectionSideSupply D)
    {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G) (hq : q ∈ forestBlockDomFinset G) :
    B.toForestBlockBijectionSupply.toFun G q hq = fwdMapFilteredAlphaValue B.F B.V ⟨q, hq⟩ :=
  rfl

/-- **R-6c-body-481 — native `Δᵣ`-coassociativity from the alpha filtered bijection side.** -/
theorem coassoc_gen (B : ResolvedFilteredAlphaBijectionSideSupply D) (x : ResolvedHopfGen) :
    D.coassocLeft (MvPolynomial.X x) = D.coassocRight (MvPolynomial.X x) :=
  B.toForestBlockBijectionSupply.coassoc_gen x

end ResolvedFilteredAlphaBijectionSideSupply

/-- **R-6c-body-481 ∎ — native coassoc from a round-trip leaf supply.**  The alpha round-trip leaf (body-479) issues the
strong cover via `R.toCover`; the forward quotient membership is derived internally (body-472).  This is the first native
`Δᵣ`-coassociativity reached on the alpha filtered-`V` front, with filtered quotient ownership kept to the end. -/
theorem coassoc_gen_of_recovered_preimage_alpha_value
    {F : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedFilteredConcreteSummandValueSupply D}
    (R : ResolvedRecoveredPreimageAlphaValueRoundTripLeafSupply F V)
    (carrier_isProperForest : ∀ (G : ResolvedFeynmanGraph) (A : ResolvedAdmissibleSubgraph G),
      A ∈ D.carrier G → A.IsProperForest)
    (rep : ResolvedHopfGen → ResolvedFeynmanGraph)
    (repCD : ∀ x : ResolvedHopfGen, (rep x).forget.toClass.IsConnectedDivergent)
    (rep_gen : ∀ x : ResolvedHopfGen, x = (rep x).toResolvedHopfGen (repCD x))
    (x : ResolvedHopfGen) :
    D.coassocLeft (MvPolynomial.X x) = D.coassocRight (MvPolynomial.X x) :=
  (ResolvedFilteredAlphaBijectionSideSupply.mk F V R.toCover carrier_isProperForest rep repCD rep_gen).coassoc_gen x

/-- **R-6c-body-481 — the legacy compatibility anchor.**  The alpha summand agreement over the body-471 legacy adapter
`V.toFiltered` is the legacy value summand agreement (proof-irrelevant `rfl`; the alpha forward map agrees by body-471). -/
theorem summand_agree_alpha_value_of_value_toFiltered (F : ResolvedSelectedOuterFilteredMemSupply D)
    (V : ResolvedConcreteSummandValueSupply D) {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom D G) :
    (summand_agree_alpha_value_of_value F V.toFiltered).summand_agree_value q
      = (summand_agree_value_of_value F V).summand_agree_value q :=
  rfl

end GaugeGeometry.QFT.Combinatorial
