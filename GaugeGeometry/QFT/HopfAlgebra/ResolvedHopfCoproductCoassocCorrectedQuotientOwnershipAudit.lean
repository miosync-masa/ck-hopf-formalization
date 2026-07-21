import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCorrectedSurvivorRemnantCross
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocFwdMapFiltered

/-!
# R-6c-body-468 — `hRdisj` theorem + the total quotient-ownership no-go audit (PROVED / AUDIT)

Four-hundred-and-sixty-eighth genuine-body step — the survivor/remnant element-disjointness (`hRdisj`) as a theorem, and
the formal bank of the TOTAL quotient-ownership no-go (a `∀ raw q` `quotient_mem` is inconsistent with the canonical `W'`).
Per the HALT this STOPS before `.mpr`-ing the `W'` membership iff and before migrating any existing `V` / body-445.

## `hRdisj` (THEOREM)

* `canonicalCorrectedSurvivorRemnant_elements_disjoint` — the two forests' element sets are disjoint: a shared element is
  self-cross-disjoint (body-467, UNCONDITIONAL) on a `rightComponentNonempty_of_measure` witness.

## Total quotient-ownership no-go (formal bank)

For a split choice `s` with the all-left primitive choice `p_L` (`fun _ _ => Sum.inl true`, body-311's structure),
`rightComponents s = ∅` and `forestComponents s = ∅`, so:

* `canonicalCorrectedQuotientUnion_elements_eq_empty` — the survivor ∪ remnant element set is EMPTY;
* `canonicalCorrectedQuotientUnion_not_mem` — no outer carrier witness `A` is a member.

So the quotient forest of such a `q` is NOT `IsNonempty`, hence NOT `IsProperForest`; a `∀ raw q` `quotient_mem` composed
with `(mem_canonicalUniqueSupportedCarrier_iff …).mp` (which returns `IsProperForest`) is INCONSISTENT.  Verdict:
`quotient_mem : ∀ raw q` is INCONSISTENT with the canonical `W'`; `quotient_mem : ∀ filtered q` is the FAITHFUL repair
(the real consumer `fwdMapFilteredValue` already carries a filtered `q`).  This is exactly the body-242 `selectedOuter_mem
: ∀ s` defect, caught before building a non-existent `VBuild` certificate.

## Filtered quotient-ownership interface (prototype, un-consumed)

* `ResolvedFilteredQuotientOwnershipSupply` — the quotient-owned field `quotientForestRaw` retyped to
  `FilteredForestBlockDom` (the `Measure / Survivor / Remnant` and the now-theorem `hcross / hRdisj` stay raw-total).

Per the HALT/guards: NO `W'` five-condition proof; NO `V` / body-445 migration; the `hRdisj` theorem and the no-go are
banked, the filtered interface is a prototype only; strict `StarProm` / `InnerStarRaw` NOT used; body-445 stays a valid
conditional.  NOT the unconditional theorem.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO
`promote_collapse` / singleton / floor-297.
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
  (Fstar : ResolvedCanonicalStarFacts D) (Measure : ResolvedMeasureLeafSupply D)
  (CarrierProper : ResolvedCarrierProperProvider D) (s : ResolvedCoassocSplitChoice D G)

/-- **R-6c-body-468 — `hRdisj` as a theorem.**  The survivor and corrected-remnant forests' element sets are disjoint. -/
theorem canonicalCorrectedSurvivorRemnant_elements_disjoint :
    Disjoint ((survivorSupply_of_measure Measure G).rightSurvivorForest s).elements
      ((canonicalCorrectedRemnantComponentSupply Fstar CarrierProper).remnantForest s).elements := by
  rw [Finset.disjoint_left]
  intro δ hδ hδ'
  rw [ResolvedRightSurvivorSupply.rightSurvivorForest_elements] at hδ
  rw [ResolvedRemnantComponentSupply.remnantForest_elements] at hδ'
  obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hδ
  obtain ⟨γ, _, hγeq⟩ := Finset.mem_image.mp hδ'
  have hcross := correctedRightSurvivor_remnant_disjoint Fstar Measure s r (s.forestComponentOccurrence γ)
  have hγeq' : (canonicalCorrectedRemnantReembedSupply s Fstar).correctedRemnantComponent
        (s.forestComponentOccurrence γ)
      = (survivorSupply_of_measure Measure G).survivorComponent s r := hγeq
  rw [hγeq'] at hcross
  obtain ⟨w, hw⟩ := rightComponentNonempty_of_measure Measure s r
  exact Finset.disjoint_left.mp hcross hw hw

/-- **R-6c-body-468 — the total no-go core.**  When a split choice has no right / forest components (the `p_L` choice),
the survivor ∪ remnant element set is empty. -/
theorem canonicalCorrectedQuotientUnion_elements_eq_empty
    (hR : s.rightComponents = ∅) (hF : s.forestComponents = ∅) :
    ((survivorSupply_of_measure Measure G).rightSurvivorForest s).elements
        ∪ ((canonicalCorrectedRemnantComponentSupply Fstar CarrierProper).remnantForest s).elements
      = ∅ := by
  rw [ResolvedRightSurvivorSupply.rightSurvivorForest_elements,
    ResolvedRemnantComponentSupply.remnantForest_elements]
  refine Finset.union_eq_empty.mpr ⟨Finset.image_eq_empty.mpr ?_, Finset.image_eq_empty.mpr ?_⟩
  · exact Finset.attach_eq_empty_iff.mpr hR
  · exact Finset.attach_eq_empty_iff.mpr hF

/-- **R-6c-body-468 ∎ — the total no-go witness.**  No outer carrier witness `A` is a member of the empty quotient union
of a `p_L` choice — so its quotient forest is not `IsNonempty`, not `IsProperForest`. -/
theorem canonicalCorrectedQuotientUnion_not_mem
    (hR : s.rightComponents = ∅) (hF : s.forestComponents = ∅)
    (A : ResolvedFeynmanSubgraph s.selectedOuterContractGraph) :
    A ∉ ((survivorSupply_of_measure Measure G).rightSurvivorForest s).elements
        ∪ ((canonicalCorrectedRemnantComponentSupply Fstar CarrierProper).remnantForest s).elements := by
  rw [canonicalCorrectedQuotientUnion_elements_eq_empty Fstar Measure CarrierProper s hR hF]
  simp

/-- **R-6c-body-468 — prototype: the filtered quotient-ownership interface** (un-consumed).  The quotient-owned field
`quotientForestRaw` retyped to a filtered `q` — the faithful repair of the `∀ raw q` no-go. -/
structure ResolvedFilteredQuotientOwnershipSupply (D : ResolvedCoproductProperForestData) where
  /-- The quotient forest index, over a FILTERED forest-block-domain point only. -/
  quotientForestRaw : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G),
    (D.supply (((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf q.1).contractWithStars
      (D.starOf G ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf q.1)))).ForestIdx

end GaugeGeometry.QFT.Combinatorial
