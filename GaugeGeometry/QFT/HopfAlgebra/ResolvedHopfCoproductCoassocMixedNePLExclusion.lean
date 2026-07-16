import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocMixedNePRExclusion
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocComponentPartition
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightSurvivor
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRemnant
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocConcreteSummandValue

/-!
# R-6c-body-311 — the `mixed_ne_pL` exclusion: `p_L` ⇒ empty quotient forest ⇒ contradiction (PROVED)

Three-hundred-and-eleventh genuine-body step — the second (and last) mixed classifier-leaf proof, symmetric to
body-310.  It fixes the L2 quotient root `ResolvedRawForwardQuotientValueSupply` (`Tags` + the two classifier-free
forward identities, NO `Data`) and proves the p_L exclusion `mixed_ne_pL` non-circularly.

## The classifier-free chain (L2 → L3, second arrow)

```text
(recoveredPreimageValue z).2 = p_L                          (assume, for contradiction)
→ quotientForestRaw (recoveredPreimageValue z).1.elements = ∅   (quotientForestRaw_eq_empty_of_eq_pL)
→ z.2.1.elements.card = 0                                    (card_eq_of_heq_forestIdx: forward_quotient HEq + forward_outer align)
→ ⊥                                                          (carrier_isProperForest z.2.1 → 0 < card, body-228)
```

* **`quotientForestRaw_eq_empty_of_eq_pL`** — under `q.2 = fun _ _ => Sum.inl true` (all-left `p_L`): `rightComponents`
  (the `inl false` filter) and `forestComponents` (the `inr` filter) both empty, so `rightSurvivorForest` /
  `remnantForest` (images over those component sets, `rfl`) are empty; `union_eq` gives the whole quotient forest empty.

* **`card_eq_of_heq_forestIdx`** — the reverse of body-203 `heq_forestIdx`: given the outer equality `A₁ = A₂` and
  `HEq B₁ B₂`, `cases` the outer (abstract bound vars, no projection wall) then `eq_of_heq` yields the **`ℕ` card
  equality** `B₁.1.elements.card = B₂.1.elements.card` — type-independent, so no HEq survives into the caller.

* **`mixed_ne_pL_of_forward_quotient`** — assume `p_L`; the empty lemma gives `card = 0` on the reconstruction side;
  `card_eq_of_heq_forestIdx` (fed `forward_outer_value` for the type alignment + `forward_quotient_value` HEq) carries it
  to `z.2.1.elements.card = 0`; but `carrier_isProperForest z.2.1` gives `0 < card`.  Contradiction (`omega`).
  Unconditional — no classifier hypothesis, so it weakens trivially into the body-283 field shape.

## Why `forward_outer_value` is in the quotient root

The `forward_quotient_value` HEq relates `ForestIdx` of two DIFFERENT contracted graphs
(`(selectedOuterRawOf (recPre z)).contractWithStars …` vs `z.1.1.contractWithStars …`); extracting any homogeneous fact
needs the outer equality to align the types — exactly why body-285's `forward_roundtrip_value` pairs the HEq with
`forward_outer_value` under `Sigma.ext`.  Both identities are classifier-free and `Data`-free (proved standalone at
ForwardOuterValue.lean:175 / ForwardQuotientValue.lean:100), so the root stays at the correct L2 layer.

## Non-circular (body-309 guards honored)

Takes only `P` (body-228 provider) and `R : ResolvedRawForwardQuotientValueSupply` (`Tags` + the two forward identities).
Does NOT use `ResolvedRecoveredPreimageValueMemSupply` (body-283), does NOT depend on `mixed_ne_pR` (body-310), does NOT
use `recoveredPreimageValue_mem` / the cover / codomain filter, does NOT touch floor-297/298.

Per the HALT: only the `p_L` exclusion is proved; `forest_nonempty` (the last membership leaf) and the round-trip
re-plumbing + carrier closure are later bodies; no facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-311 — the quotient forest of an all-left (`p_L`) choice is empty.**  `rightComponents` (`inl false`)
and `forestComponents` (`inr`) are both empty under `q.2 = fun _ _ => Sum.inl true`, so the survivor/remnant images —
hence their union, the quotient forest — are empty. -/
theorem quotientForestRaw_eq_empty_of_eq_pL {G : ResolvedFeynmanGraph}
    (V : ResolvedConcreteSummandValueSupply D)
    (q : ResolvedCoassocSplitChoice D G) (hpL : q.2 = fun _ _ => Sum.inl true) :
    (V.quotientForestRaw q).1.elements = ∅ := by
  have hR : q.rightComponents = ∅ := by
    rw [ResolvedCoassocSplitChoice.rightComponents, Finset.filter_eq_empty_iff]
    intro γ _ hRP
    have hRP' : q.choiceAt γ = Sum.inl false := hRP
    have hc : q.choiceAt γ = Sum.inl true := by
      simp only [ResolvedCoassocSplitChoice.choiceAt, hpL]
    rw [hc] at hRP'
    exact absurd (Sum.inl.inj hRP') (by decide)
  have hF : q.forestComponents = ∅ := by
    rw [ResolvedCoassocSplitChoice.forestComponents, Finset.filter_eq_empty_iff]
    intro γ _ hFC
    obtain ⟨B, hB⟩ := hFC
    have hc : q.choiceAt γ = Sum.inl true := by
      simp only [ResolvedCoassocSplitChoice.choiceAt, hpL]
    rw [hc] at hB
    simp at hB
  have hSurv : Finset.image (V.Survivor.survivor.survivorComponent q) q.rightComponents.attach = ∅ := by
    rw [Finset.image_eq_empty, Finset.attach_eq_empty_iff]; exact hR
  have hRem : Finset.image
      (fun γ => V.Remnant.remnant.remnantComponent q (q.forestComponentOccurrence γ))
      q.forestComponents.attach = ∅ := by
    rw [Finset.image_eq_empty, Finset.attach_eq_empty_iff]; exact hF
  rw [V.union_eq q, ResolvedAdmissibleSubgraph.union_elements,
    ResolvedRightSurvivorSupply.rightSurvivorForest_elements,
    ResolvedRemnantComponentSupply.remnantForest_elements, hSurv, hRem]
  rfl

/-- **R-6c-body-311 — the reverse of `heq_forestIdx`: an outer equality collapses a `ForestIdx` `HEq` to a `ℕ` card
equality.**  `cases` the outer (abstract bound vars), then `eq_of_heq`. -/
theorem card_eq_of_heq_forestIdx {G : ResolvedFeynmanGraph} {A₁ A₂ : ResolvedAdmissibleSubgraph G}
    (B₁ : (D.supply (A₁.contractWithStars (D.starOf G A₁))).ForestIdx)
    (B₂ : (D.supply (A₂.contractWithStars (D.starOf G A₂))).ForestIdx)
    (houter : A₁ = A₂) (h : HEq B₁ B₂) :
    B₁.1.elements.card = B₂.1.elements.card := by
  cases houter
  rw [eq_of_heq h]

/-- **R-6c-body-311 — the L2 quotient root: raw `Tags` + the two classifier-free forward identities.**  Carries NO
`Data`, NO mixed membership; `forward_outer_value` is present only to align the `forward_quotient_value` HEq's types. -/
structure ResolvedRawForwardQuotientValueSupply (F : ResolvedSelectedOuterFilteredMemSupply D)
    (V : ResolvedConcreteSummandValueSupply D) where
  /-- The raw region-tag supply (body-282). -/
  Tags : ResolvedRegionTagValueSupply F V
  /-- The reconstruction's re-promoted outer is the original outer (proved standalone at body-289). -/
  forward_outer_value : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    (resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf (Tags.recoveredPreimageValue z) = z.1.1
  /-- The reconstruction's quotient forest is the original `B` (heterogeneous; proved standalone at body-290). -/
  forward_quotient_value : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    HEq (V.quotientForestRaw (Tags.recoveredPreimageValue z)) z.2

namespace ResolvedRawForwardQuotientValueSupply

variable {F : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}

/-- **R-6c-body-311 — the `mixed_ne_pL` exclusion.**  The recovered choice is never all-left `p_L`: `p_L` would empty the
quotient forest, but `forward_quotient_value` (aligned by `forward_outer_value`) equates its card with the proper-forest
codomain `z.2` (positive via `carrier_isProperForest`).  Unconditional — no classifier hypothesis. -/
theorem mixed_ne_pL_of_forward_quotient (P : ResolvedCarrierProperProvider D)
    (R : ResolvedRawForwardQuotientValueSupply F V)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) :
    (R.Tags.recoveredPreimageValue z).2 ≠ (fun _ _ => Sum.inl true) := by
  intro hpL
  have hempty : (V.quotientForestRaw (R.Tags.recoveredPreimageValue z)).1.elements = ∅ :=
    quotientForestRaw_eq_empty_of_eq_pL V _ hpL
  have hcard := card_eq_of_heq_forestIdx (V.quotientForestRaw (R.Tags.recoveredPreimageValue z)) z.2
    (R.forward_outer_value z) (R.forward_quotient_value z)
  rw [hempty, Finset.card_empty] at hcard
  have hne : (z.2.1.elements).Nonempty := (P.carrier_isProperForest _ z.2.1 z.2.2).1
  rw [← Finset.card_pos] at hne
  omega

end ResolvedRawForwardQuotientValueSupply

end GaugeGeometry.QFT.Combinatorial
