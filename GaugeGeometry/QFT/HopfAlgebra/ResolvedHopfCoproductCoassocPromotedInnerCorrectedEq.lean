import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocPromotedCorrectedSource
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocInnerCorrectedRemnantRoundTrip

/-!
# R-6c-body-457 — the forward-corrected source equals the inner-corrected source (PROVED)

Four-hundred-and-fifty-seventh genuine-body step — the CENTRAL cross-ambient equality: the forward-owned corrected
source graph (body-456) and the recovered-side corrected source graph (body-454) are the SAME `ResolvedFeynmanGraph`,
under the occurrence↔recovered alignment (`hparent`, `hidx`, `houter`).  NO permutation extensional equality is used —
only a component-level star agreement fed into `contractWithStars` congruence, plus the two canonical representations.

Component identity (transport-free, on `innerRaw`): for `B ∈ innerRaw.elements`,
`(M.parent z δ).promote B = (innerSource B).1` (by `innerSource_spec` + `promote_toInner`), so the intrinsic promoted
star `D.starOf G z.1.1 ((M.parent z δ).promote ·)` agrees with `touchedInnerStarTotal` on the inner forest.

* `intrinsicPromotedInnerStar` — the promoted star expressed intrinsically on `innerRaw`'s ambient (no `o`);
* `intrinsicPromotedInnerStar_eq_touched` — the component-level star agreement (step 1);
* `innerRaw_contract_intrinsic_eq_touched` — the same-forest contraction congruence (step 2, body-357 congr lemmas);
* `occurrenceSource_eq` / `occurrenceContract_transport` — free-`γ'`/`HEq` helpers isolating the `o.B ↔ innerRaw`
  transport (`subst` + `eq_of_heq`, NO dependent `rw` on the whole occurrence);
* `promotedCorrectedSource_eq_innerCorrectedSource` — the central equality (step 3);
* `promotedCorrectedSource_vertices/internalEdges/externalLegs_eq_inner` — the three projections (step 4).

Per the HALT/guards: strict `StarProm` / `InnerStarRaw` NOT used; NO permutation extensional equality; the provider /
reembed / `VBuild` are NOT built here; `houter` is used ONLY to align the star-forest argument; the component identity is
`innerSource_spec` + `promote_toInner` only; body-445 stays a valid conditional.  NOT the unconditional theorem.  No
facade, no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}
  (M : ResolvedMultiStarDecontractionSupply D) (z : ForestBlockCodType D G)
  (δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) // x ∈ forestDomain z})

/-- **R-6c-body-457 — the intrinsic promoted star on `innerRaw`'s ambient.**  The outer star of the promotion of an inner
component (no occurrence `o`). -/
noncomputable def intrinsicPromotedInnerStar :
    ResolvedFeynmanSubgraph (M.parent z δ).toResolvedFeynmanGraph → VertexId :=
  fun B => D.starOf G z.1.1 ((M.parent z δ).promote B)

/-- **R-6c-body-457 — step 1: the component-level star agreement** (transport-free, on `innerRaw`). -/
theorem intrinsicPromotedInnerStar_eq_touched
    {B : ResolvedFeynmanSubgraph (M.parent z δ).toResolvedFeynmanGraph}
    (hB : B ∈ (innerRaw z δ.1 (M.legLift z δ) (M.hE z) (M.hL z)).elements) :
    intrinsicPromotedInnerStar M z δ B
      = touchedInnerStarTotal z δ.1 (M.legLift z δ) (M.hE z) (M.hL z) B := by
  have hpromote : (M.parent z δ).promote B
      = (innerSource z δ.1 (M.legLift z δ) (M.hE z) (M.hL z) ⟨B, hB⟩).1 := by
    conv_lhs => rw [show B
        = toInner z δ.1 (M.legLift z δ) (M.hE z) (M.hL z)
            (innerSource z δ.1 (M.legLift z δ) (M.hE z) (M.hL z) ⟨B, hB⟩)
        from (innerSource_spec z δ.1 (M.legLift z δ) (M.hE z) (M.hL z) ⟨B, hB⟩).symm]
    exact promote_toInner z δ.1 (M.legLift z δ) (M.hE z) (M.hL z)
      (innerSource z δ.1 (M.legLift z δ) (M.hE z) (M.hL z) ⟨B, hB⟩)
  rw [touchedInnerStarTotal_of_mem z δ.1 (M.legLift z δ) (M.hE z) (M.hL z) B hB, touchedInnerStar]
  show D.starOf G z.1.1 ((M.parent z δ).promote B)
    = D.starOf G z.1.1 (innerSource z δ.1 (M.legLift z δ) (M.hE z) (M.hL z) ⟨B, hB⟩).1
  rw [hpromote]

/-- **R-6c-body-457 — step 2: the same-forest contraction congruence.**  `innerRaw`'s intrinsic-promoted-star contraction
equals its touched-star contraction (body-357 congruence, from step 1). -/
theorem innerRaw_contract_intrinsic_eq_touched :
    (innerRaw z δ.1 (M.legLift z δ) (M.hE z) (M.hL z)).contractWithStars (intrinsicPromotedInnerStar M z δ)
      = (innerRaw z δ.1 (M.legLift z δ) (M.hE z) (M.hL z)).contractWithStars
          (touchedInnerStarTotal z δ.1 (M.legLift z δ) (M.hE z) (M.hL z)) := by
  have hstar : ∀ η ∈ (innerRaw z δ.1 (M.legLift z δ) (M.hE z) (M.hL z)).elements,
      intrinsicPromotedInnerStar M z δ η
        = touchedInnerStarTotal z δ.1 (M.legLift z δ) (M.hE z) (M.hL z) η :=
    fun η hη => intrinsicPromotedInnerStar_eq_touched M z δ hη
  exact ResolvedFeynmanGraph.ext'
    (contractWithStars_vertices_congr _ _ _ hstar)
    (contractWithStars_internalEdges_congr _ _ _ hstar)
    (contractWithStars_externalLegs_congr _ _ _ hstar)

variable (q : FilteredForestBlockDom D G)
  (o : ResolvedCoassocSplitChoice.ForestChoiceOccurrence q.1)

/-- **R-6c-body-457 — helper: the occurrence's hardcoded-star contraction transported to `innerRaw`.**  Free `γ'`/`HEq`,
`subst` + `eq_of_heq`, NO dependent `rw` on the occurrence. -/
theorem occurrenceSource_eq (γ' : ResolvedFeynmanSubgraph G)
    (B' : (D.supply γ'.toResolvedFeynmanGraph).ForestIdx)
    (hγ : γ' = M.parent z δ) (hB : HEq B' (M.innerIdx z δ)) :
    B'.1.contractWithStars (D.starOf γ'.toResolvedFeynmanGraph B'.1)
      = (innerRaw z δ.1 (M.legLift z δ) (M.hE z) (M.hL z)).contractWithStars
          (D.starOf (M.parent z δ).toResolvedFeynmanGraph
            (innerRaw z δ.1 (M.legLift z δ) (M.hE z) (M.hL z))) := by
  subst hγ
  obtain rfl := eq_of_heq hB
  rfl

/-- **R-6c-body-457 — helper: the occurrence's promoted-star contraction transported to the touched-star contraction.** -/
theorem occurrenceContract_transport (γ' : ResolvedFeynmanSubgraph G)
    (B' : (D.supply γ'.toResolvedFeynmanGraph).ForestIdx)
    (hγ : γ' = M.parent z δ) (hB : HEq B' (M.innerIdx z δ))
    (houter : (resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf q.1 = z.1.1) :
    B'.1.contractWithStars (fun b => D.starOf G
        ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf q.1) (γ'.promote b))
      = (innerRaw z δ.1 (M.legLift z δ) (M.hE z) (M.hL z)).contractWithStars
          (touchedInnerStarTotal z δ.1 (M.legLift z δ) (M.hE z) (M.hL z)) := by
  subst hγ
  obtain rfl := eq_of_heq hB
  simp only [houter]
  exact innerRaw_contract_intrinsic_eq_touched M z δ

variable (Fstar : ResolvedCanonicalStarFacts D)

/-- **R-6c-body-457 ∎ — the central cross-ambient equality.**  The forward-owned corrected source graph (body-456) and
the recovered-side corrected source graph (body-454) are the same graph — WITHOUT permutation equality. -/
theorem promotedCorrectedSource_eq_innerCorrectedSource
    (hparent : o.γ.1 = M.parent z δ) (hidx : HEq o.B (M.innerIdx z δ))
    (houter : (resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf q.1 = z.1.1) :
    promotedCorrectedOccurrenceSourceGraph Fstar q o
      = innerCorrectedOccurrenceSourceGraph Fstar M z δ o := by
  have h1 : o.B.1.contractWithStars (promotedOccurrenceStar q o)
      = (innerRaw z δ.1 (M.legLift z δ) (M.hE z) (M.hL z)).contractWithStars
          (touchedInnerStarTotal z δ.1 (M.legLift z δ) (M.hE z) (M.hL z)) :=
    occurrenceContract_transport M z δ q o.γ.1 o.B hparent hidx houter
  have h2 : o.contractedSourceGraph
      = (innerRaw z δ.1 (M.legLift z δ) (M.hE z) (M.hL z)).contractWithStars
          (D.starOf (M.parent z δ).toResolvedFeynmanGraph
            (innerRaw z δ.1 (M.legLift z δ) (M.hE z) (M.hL z))) :=
    occurrenceSource_eq M z δ o.γ.1 o.B hparent hidx
  rw [← promotedCorrectedSource_eq Fstar q o, h1, innerStarCorrected_contract_eq Fstar M z δ,
    innerCorrectedOccurrenceSourceGraph, h2]

/-- **R-6c-body-457 — the central equality on vertices.** -/
theorem promotedCorrectedSource_vertices_eq_inner
    (hparent : o.γ.1 = M.parent z δ) (hidx : HEq o.B (M.innerIdx z δ))
    (houter : (resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf q.1 = z.1.1) :
    (promotedCorrectedOccurrenceSourceGraph Fstar q o).vertices
      = (innerCorrectedOccurrenceSourceGraph Fstar M z δ o).vertices :=
  congrArg ResolvedFeynmanGraph.vertices
    (promotedCorrectedSource_eq_innerCorrectedSource M z δ q o Fstar hparent hidx houter)

/-- **R-6c-body-457 — the central equality on internal edges.** -/
theorem promotedCorrectedSource_internalEdges_eq_inner
    (hparent : o.γ.1 = M.parent z δ) (hidx : HEq o.B (M.innerIdx z δ))
    (houter : (resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf q.1 = z.1.1) :
    (promotedCorrectedOccurrenceSourceGraph Fstar q o).internalEdges
      = (innerCorrectedOccurrenceSourceGraph Fstar M z δ o).internalEdges :=
  congrArg ResolvedFeynmanGraph.internalEdges
    (promotedCorrectedSource_eq_innerCorrectedSource M z δ q o Fstar hparent hidx houter)

/-- **R-6c-body-457 — the central equality on external legs.** -/
theorem promotedCorrectedSource_externalLegs_eq_inner
    (hparent : o.γ.1 = M.parent z δ) (hidx : HEq o.B (M.innerIdx z δ))
    (houter : (resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf q.1 = z.1.1) :
    (promotedCorrectedOccurrenceSourceGraph Fstar q o).externalLegs
      = (innerCorrectedOccurrenceSourceGraph Fstar M z δ o).externalLegs :=
  congrArg ResolvedFeynmanGraph.externalLegs
    (promotedCorrectedSource_eq_innerCorrectedSource M z δ q o Fstar hparent hidx houter)

end GaugeGeometry.QFT.Combinatorial
