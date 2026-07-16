import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocClassifierLeafOrderingAudit
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCarrierProperProvider
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocLeftPrimitiveFactor
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCross
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocPromotedOf

/-!
# R-6c-body-310 — the `mixed_ne_pR` exclusion: `p_R` ⇒ empty selected outer ⇒ contradiction (PROVED)

Three-hundred-and-tenth genuine-body step — the first classifier-leaf proof, following the body-309 verdict B
re-stratification.  It fixes the correct **L2 root** on the Lean side — `ResolvedRawForwardOuterValueSupply`, carrying
ONLY `Tags` + the classifier-free `forward_outer_value` identity (NO `Data`, NO mixed membership) — and proves the p_R
exclusion `mixed_ne_pR` from it, non-circularly.

## The classifier-free chain (L2 → L3, first arrow)

```text
(recoveredPreimageValue z).2 = p_R                        (assume, for contradiction)
→ selectedOuterRawOf (recoveredPreimageValue z) = ∅       (selectedOuterRawOf_eq_empty_of_eq_pR)
→ z.1.1.elements = ∅                                      (forward_outer_value)
→ ⊥                                                        (carrier_isProperForest z.1.1 → IsNonempty, body-228)
```

* **`selectedOuterRawOf_eq_empty_of_eq_pR`** — for any split choice `q` with `q.2 = fun _ _ => Sum.inl false` (the
  all-right-primitive `p_R`): `leftOf` filters on `leftSelectedConcrete` (`choiceAt = inl true`), empty under `p_R`;
  `promotedOf`'s `promotedElements` biUnions `promotedComponentElements`, each `∅` on an `inl` choice
  (PromotedOf.lean:58-60); so `selectedOuterRawOf = leftOf ∪ promotedOf` has empty elements.  The `∪`
  `Classical.decEq` diamond is handled at membership level (`union_elements` simp + `Finset.union_eq_empty`).

* **`mixed_ne_pR_of_forward_outer`** — assume `(R.Tags.recoveredPreimageValue z).2 = p_R`; the empty lemma gives
  `selectedOuterRawOf (recoveredPreimageValue z) = ∅`; `R.forward_outer_value z` rewrites its outer to `z.1.1`, so
  `z.1.1.elements = ∅`; but `P.carrier_isProperForest G z.1.1 z.1.2` (body-228 banked provider) gives
  `z.1.1.IsProperForest`, whose `.1` is `z.1.1.elements.Nonempty` — contradiction.  The classifier hypothesis
  `¬ resolvedIsForestImage` is NOT needed (the p_R exclusion is unconditional), so this weakens trivially into the
  body-283 field shape later.

## Non-circular (body-309 guards honored)

Takes only `P` (body-228 provider) and `R : ResolvedRawForwardOuterValueSupply` (the L2 root: `Tags` +
`forward_outer_value`).  Does NOT take body-283's `Data`, does NOT use `recoveredPreimageValue_mem` (body-308), does NOT
use `toOuterMixingInverse`, does NOT route through the forest classifier.  `forward_outer_value` is the classifier-free
identity (proved standalone at ForwardOuterValue.lean:175, body-289) — here it is a bare `R`-field, so the exclusion sits
strictly at layer 3 above the raw forward fact, no back-flow.

Per the HALT: only the `p_R` exclusion is proved; `mixed_ne_pL`, `forest_nonempty`, `forest_value_eq`, and the carrier
closure are later bodies; the L2 root is fixed but the round-trip supply is NOT re-plumbed here; no facade, no flat term,
no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData}

set_option linter.unusedSectionVars false

/-- **R-6c-body-310 — the selected outer of an all-right-primitive (`p_R`) choice is empty.**  `leftOf` (the
`inl true` filter) and `promotedOf` (the `inr` biUnion) are both empty under `q.2 = fun _ _ => Sum.inl false`. -/
theorem selectedOuterRawOf_eq_empty_of_eq_pR {G : ResolvedFeynmanGraph}
    (q : ResolvedCoassocSplitChoice D G) (hpR : q.2 = fun _ _ => Sum.inl false) :
    ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf q).elements = ∅ := by
  have hleft : ((resolvedConcreteForestPromoteSupply D G).leftOf q).elements = ∅ := by
    show ((resolvedConcreteLeftSelectionSupply D G).leftOf q).elements = ∅
    rw [resolved_leftOf_elements_eq, Finset.filter_eq_empty_iff]
    intro x hx hlsc
    obtain ⟨hx', hchoice⟩ := hlsc
    have hc : q.choiceAt ⟨x, hx'⟩ = Sum.inl false := by
      simp only [ResolvedCoassocSplitChoice.choiceAt, hpR]
    exact absurd (Sum.inl.inj (hchoice.symm.trans hc)) (by decide)
  have hpromo : ((resolvedConcreteForestPromoteSupply D G).promotedOf q).elements = ∅ := by
    show ((resolvedPromotedOfSupply D G).promotedOf q).elements = ∅
    rw [ResolvedPromotedOfSupply.promotedOf_elements]
    unfold ResolvedCoassocSplitChoice.promotedElements
    rw [Finset.eq_empty_iff_forall_notMem]
    intro x hx
    obtain ⟨γ, -, hxγ⟩ := Finset.mem_biUnion.mp hx
    have hc : q.choiceAt γ = Sum.inl false := by
      simp only [ResolvedCoassocSplitChoice.choiceAt, hpR]
    have he : q.promotedComponentElements γ = ∅ := by
      unfold ResolvedCoassocSplitChoice.promotedComponentElements; rw [hc]
    rw [he] at hxγ
    exact Finset.notMem_empty _ hxγ
  simp only [ResolvedForestPromoteSupply.selectedOuterRawOf,
    ResolvedAdmissibleSubgraph.union_elements]
  rw [hleft, hpromo]
  simp

/-- **R-6c-body-310 — the L2 root: raw `Tags` + the classifier-free forward-outer identity.**  Carries NO `Data`, NO
mixed membership — the correct layer to feed the p_R exclusion (body-309 re-stratification). -/
structure ResolvedRawForwardOuterValueSupply (F : ResolvedSelectedOuterFilteredMemSupply D)
    (V : ResolvedConcreteSummandValueSupply D) where
  /-- The raw region-tag supply (body-282). -/
  Tags : ResolvedRegionTagValueSupply F V
  /-- The reconstruction's re-promoted outer is the original outer (proved standalone at body-289). -/
  forward_outer_value : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    (resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf (Tags.recoveredPreimageValue z) = z.1.1

namespace ResolvedRawForwardOuterValueSupply

variable {F : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}

/-- **R-6c-body-310 — the `mixed_ne_pR` exclusion.**  The recovered choice is never all-right-primitive `p_R`:
`p_R` would empty the selected outer, but `forward_outer_value` equates it with the proper-forest outer `z.1.1`
(nonempty via `carrier_isProperForest`).  Unconditional — no classifier hypothesis. -/
theorem mixed_ne_pR_of_forward_outer (P : ResolvedCarrierProperProvider D)
    (R : ResolvedRawForwardOuterValueSupply F V)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) :
    (R.Tags.recoveredPreimageValue z).2 ≠ (fun _ _ => Sum.inl false) := by
  intro hpR
  have hempty : ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf
      (R.Tags.recoveredPreimageValue z)).elements = ∅ :=
    selectedOuterRawOf_eq_empty_of_eq_pR _ hpR
  rw [R.forward_outer_value z] at hempty
  have hne : (z.1.1).elements.Nonempty := (P.carrier_isProperForest G z.1.1 z.1.2).1
  rw [hempty] at hne
  exact Finset.not_nonempty_empty hne

end ResolvedRawForwardOuterValueSupply

end GaugeGeometry.QFT.Combinatorial
