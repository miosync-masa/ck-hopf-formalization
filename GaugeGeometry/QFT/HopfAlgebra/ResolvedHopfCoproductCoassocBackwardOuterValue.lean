import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocOuterUnionRegionTagValue

/-!
# R-6c-body-284 — backward outer round-trip (value) + the corrected leaf audit (PROVED)

Two-hundred-and-eighty-fourth genuine-body step — the one COMPLETE pure reduction of the value-root round-trips:
`backward_outer`, `unionOuterValue (fwdMapFilteredValue F V q) = q.1.1`, from body-280's
`recovered_region_membership_value` alone (no leaf).  Plus the corrected leaf-count audit.

## Backward outer (pure reduction — no leaf)

`unionOuterValue z`'s elements are `leftResidual z ∪ rightRecovered z ∪ forestRecovered z` (`mem_unionOuterValue_iff`,
handling the `Classical.decEq` union instance at membership level), and body-280 says a component is in that disjunction
iff it is a component of the domain outer `q.1.1.1`.  So at the forward image `z = fwdMapFilteredValue F V q` the
elements coincide, and `ext_elements` + `Subtype.ext` give the outer round-trip.

## Corrected leaf audit — it is THREE, not two

Re-auditing the forest-component `backward_choice` HEq: `forest_tag` gives `recoverChoiceValue z γ = inr (forestTag z γ)`
but the original choice is `q.2 γ = inr B`, and `forestChoiceSelected` FORGETS `B`.  So the HEq needs the EXACT value
`forestTag z γ = B` — a **third genuine leaf** (the value analog of `forest_choiceAt_eq`,
`ForestChoiceOccurrenceRecovery.lean:109`, which in the total root bottoms out on `parent_recovered`, body-200, a
forward-round-trip geometry fact reading `fwdMap S q`; it is S-keyed and needs value re-key).

```text
LEAVES (3):
  1. forward_outer_value    : selectedOuterRawOf ⟨unionOuterValue z, recoverChoiceValue z⟩ = z.1
  2. forward_quotient_value : HEq (V.quotientForestRaw ⟨unionOuterValue z, recoverChoiceValue z⟩) z.2
  3. forest_exactB_value    : q.2 γ = inr (forestTag (fwdMapFilteredValue F V q) γ …)   [forest occurrence recovery]

REDUCTIONS (no leaf):
  backward_outer  : unionOuterValue (fwd q) = q.1.1                — THIS body, from body-280.
  backward_choice : HEq (recoverChoiceValue (fwd q)) q.2           — body-285, = heq_of_index_eq (index = backward_outer,
                    from body-280) + tags (body-282, inl cases) + leaf 3 (inr case).

COLLAPSE: mixedPreimage = forestPreimage = recoveredPreimageValue, so the four body-253 branch specs collapse to TWO
classifier-free whole round-trips (one forward `Sigma.ext`, one backward `Sigma.ext`).
```

Per the HALT: only `backward_outer` (the complete pure reduction) is proved; the three leaves and the `backward_choice`
HEq assembly are body-285; no forward reconstruction, no `heq_of_index_eq` wiring is entered.  No `S` / `Forward` /
legacy in any declaration type.  No facade, no flat term, no `forgetHopf`.
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

namespace ResolvedRegionValueClosureSupply

variable {F : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}

/-- **R-6c-body-284 — the outer union's membership disjunction** (the deferred `∪` shape at membership level).  The
`Classical.decEq` union instance is handled with explicit `Finset.mem_union`. -/
theorem mem_unionOuterValue_iff (C : ResolvedRegionValueClosureSupply F V)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) (γ : ResolvedFeynmanSubgraph G) :
    γ ∈ (C.unionOuterValue z).1.elements ↔
      (γ ∈ (C.Assembly.Left.leftResidual z).elements
        ∨ γ ∈ (C.Assembly.Region.rightRecovered z).elements
        ∨ γ ∈ (C.Assembly.Region.forestRecovered z).elements) := by
  simp only [unionOuterValue, recoveredRawUnion, ResolvedAdmissibleSubgraph.union_elements]
  constructor
  · intro h
    rcases (@Finset.mem_union _ (Classical.decEq _) _ _ _).mp h with h1 | h2
    · rcases (@Finset.mem_union _ (Classical.decEq _) _ _ _).mp h1 with hl | hr
      · exact Or.inl hl
      · exact Or.inr (Or.inl hr)
    · exact Or.inr (Or.inr h2)
  · intro h
    rcases h with hl | hr | hf
    · exact (@Finset.mem_union _ (Classical.decEq _) _ _ _).mpr
        (Or.inl ((@Finset.mem_union _ (Classical.decEq _) _ _ _).mpr (Or.inl hl)))
    · exact (@Finset.mem_union _ (Classical.decEq _) _ _ _).mpr
        (Or.inl ((@Finset.mem_union _ (Classical.decEq _) _ _ _).mpr (Or.inr hr)))
    · exact (@Finset.mem_union _ (Classical.decEq _) _ _ _).mpr (Or.inr hf)

/-- **R-6c-body-284 — the backward outer round-trip** (pure reduction, no leaf).  The reconstruction's outer of a value
forward image is the original domain outer, from body-280. -/
theorem backward_outer_value (C : ResolvedRegionValueClosureSupply F V)
    {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G) :
    C.unionOuterValue (fwdMapFilteredValue F V q) = q.1.1 := by
  apply Subtype.ext
  apply ResolvedAdmissibleSubgraph.ext_elements
  apply Finset.ext
  intro γ
  rw [C.mem_unionOuterValue_iff]
  exact C.Assembly.recovered_region_membership_value q γ

end ResolvedRegionValueClosureSupply

end GaugeGeometry.QFT.Combinatorial
