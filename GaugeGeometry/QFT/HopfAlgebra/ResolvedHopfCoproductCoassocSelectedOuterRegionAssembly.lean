import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSelectedOuterRegionPartition

/-!
# R-6c-body-174 — selected-outer region assembly: `leftOf = leftResidual` PROVED from the region tags

Hundred-and-seventy-fourth genuine-body step, the forward-outer twin of body-173.  Where body-173 assembled the
*backward*-outer partition from the three sector bridges + the choice-tag trichotomy, this body PROVES the first of
body-167's three forward-outer region facts — `leftOf_recovered_eq` — from body-146's three region tags plus
body-145's `union_eq`.  So body-167's `leftOf_recovered_eq` is no longer fielded, and the forward-outer partition
is compressed from three region facts to **two** (`promotedOf_recovered_eq` + `target_outer_partition`).

## The provable region fact: `leftOf = leftResidual` (PROVED)

`leftOf` of a split choice is the `filter` of its input outer by the concrete left-selection predicate:
`(leftSelection.leftOf s).elements = s.inputOuter.elements.filter (leftSelectedConcrete s)`
(`leftOf_elements`, and `imageSupply.leftSelection = resolvedConcreteLeftSelectionSupply` definitionally, so
`leftSelected = leftSelectedConcrete`).  For the recovered choice `q = ⟨unionOuter z, recoverChoice z⟩` this is
`{γ ∈ unionOuter z : recoverChoice z γ = inl true}`.  The region tags then close it:

* **forward** (`leftResidual → leftOf`): a `leftResidual` component is in `unionOuter` (via `union_eq`) and tags
  `inl true` (`left_tag`);
* **backward** (`leftOf → leftResidual`): a component of `unionOuter` tagged `inl true` lies, by `union_eq`, in
  `leftResidual ∪ rightRecovered ∪ forestRecovered`; a `rightRecovered` one would tag `inl false` (`right_tag`,
  contradiction) and a `forestRecovered` one `inr B` (`forest_tag`, contradiction) — so it is `leftResidual`.

This is exactly the `all_inl` / `exists_inr` pattern of body-146 (case-split `unionOuter` membership by `union_eq`,
apply the region tags), and needs **no new fielding**: `leftOf_recovered_eq` is PROVED on the abstract `Region` from
its own three tags + `union_eq`.

## Why the other two stay fielded (the forward/backward asymmetry)

`leftOf` is a *filter* on the original components, so it matches `leftResidual` by a pure tag argument.  But
`promotedOf.elements = s.promotedElements` is the **de-contracted** promoted forest (`biUnion` of `promote γ Bᵧ`),
while `forestRecovered z .elements` is the forest-choice **parents** (`componentToForest` image) — equating them is
the promotion/de-contraction round-trip (sector geometry), not a tag fact.  And `target_outer_partition`
(`leftResidual ∪ forestRecovered = A`) is the sector image characterisation.  Both are outside a pure-logic
assembly, so per the HALT they remain fielded here.

## The assembly (PROVED where it can be)

`ResolvedSelectedOuterRegionAssemblySupply D S Region` fields the two residual facts
(`promotedOf_recovered_eq` + `target_outer_partition`); `leftOf_recovered_eq` is the top-level theorem below.
`.toSelectedOuterRegionPartitionSupply` produces body-167's `ResolvedSelectedOuterRegionPartitionSupply` with
`leftOf_recovered_eq` PROVED — and hence, through body-167 → 162 → …, the forward-outer round-trip.

Per the HALT: only the `leftOf`/tag region decomposition is fixed; `target_outer_partition`'s body is not entered;
the sector bridges / `HEq` / `representedInQuotient` / promotion round-trip are untouched.

Landed:

* `recoverChoice_leftOf_eq` — body-167's `leftOf_recovered_eq` (PROVED from the region tags + `union_eq`);
* `ResolvedSelectedOuterRegionAssemblySupply D S Region` — the two residual forward facts;
* `.toSelectedOuterRegionPartitionSupply` — body-167's supply, `leftOf` PROVED.

Toolkit body (like body-173, the backward twin).  No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- **R-6c-body-174 — body-167's `leftOf_recovered_eq` from the region tags.**  On the recovered choice
`⟨unionOuter z, recoverChoice z⟩`, the left factor `leftOf` (the `inl true` filter) is exactly the `leftResidual`
region — proved by case-splitting `unionOuter` membership with `union_eq` and applying the three region tags. -/
theorem recoverChoice_leftOf_eq {S : ResolvedConcreteSummandBundleSupply D}
    (Region : ResolvedRegionChoiceRoundTripSupply D S) {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType D G) :
    ((S.Forward.imageSupply G).leftSelection.leftOf
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).elements
      = (Region.Union.leftResidual z).elements := by
  set q : ResolvedCoassocSplitChoice D G :=
    ⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ with hq
  ext γ
  rw [ResolvedSplitChoiceLeftSelectionSupply.leftOf_elements, Finset.mem_filter]
  have bridge : ∀ (h : γ ∈ (Region.Union.unionOuter z).1.elements),
      ResolvedCoassocSplitChoice.choiceAt q ⟨γ, h⟩
        = Region.recoverChoice z ⟨γ, h⟩ (Finset.mem_attach _ _) := fun h => rfl
  constructor
  · rintro ⟨hmemU, hγmem, htag⟩
    have hmemU' : γ ∈ (Region.Union.unionOuter z).1.elements := hmemU
    have htag' : Region.recoverChoice z ⟨γ, hγmem⟩ (Finset.mem_attach _ _) = Sum.inl true :=
      (bridge hγmem).symm.trans htag
    rcases Finset.mem_union.mp ((Finset.ext_iff.mp (Region.Union.union_eq z) γ).mp hmemU') with hlr | hf
    · rcases Finset.mem_union.mp hlr with hl | hr
      · exact hl
      · exact absurd (Sum.inl.inj (htag'.symm.trans (Region.right_tag z ⟨γ, hγmem⟩ hr))) (by decide)
    · obtain ⟨B, hB⟩ := Region.forest_tag z ⟨γ, hγmem⟩ hf
      exact absurd (htag'.symm.trans hB) (by simp)
  · intro hl
    have hmemU' : γ ∈ (Region.Union.unionOuter z).1.elements :=
      (Finset.ext_iff.mp (Region.Union.union_eq z) γ).mpr
        (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hl))))
    exact ⟨hmemU', hmemU', (bridge hmemU').trans (Region.left_tag z ⟨γ, hmemU'⟩ hl)⟩

/-- **R-6c-body-174 — the selected-outer region assembly supply.**  The two residual forward-outer facts that are
*not* pure tag facts: the promotion round-trip (`promotedOf = forestRecovered`) and the target coverage
(`leftResidual ∪ forestRecovered = A`). -/
structure ResolvedSelectedOuterRegionAssemblySupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) (Region : ResolvedRegionChoiceRoundTripSupply D S) where
  /-- The promoted forests are the forest-recovered region (the promotion / de-contraction round-trip). -/
  promotedOf_recovered_eq : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    ((S.Forward.imageSupply G).promotedOf
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).elements
      = (Region.Union.forestRecovered z).elements
  /-- The left residual and forest parents partition the target outer `A`. -/
  target_outer_partition : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (γ : ResolvedFeynmanSubgraph G),
    (γ ∈ (Region.Union.leftResidual z).elements ∨ γ ∈ (Region.Union.forestRecovered z).elements)
      ↔ γ ∈ z.1.1.elements

namespace ResolvedSelectedOuterRegionAssemblySupply

variable {S : ResolvedConcreteSummandBundleSupply D} {Region : ResolvedRegionChoiceRoundTripSupply D S}

/-- **R-6c-body-174 — body-167's region-partition supply with `leftOf_recovered_eq` PROVED.** -/
def toSelectedOuterRegionPartitionSupply (P : ResolvedSelectedOuterRegionAssemblySupply D S Region) :
    ResolvedSelectedOuterRegionPartitionSupply D S Region where
  leftOf_recovered_eq := fun {G} z => recoverChoice_leftOf_eq Region z
  promotedOf_recovered_eq := fun {G} z => P.promotedOf_recovered_eq z
  target_outer_partition := fun {G} z γ => P.target_outer_partition z γ

end ResolvedSelectedOuterRegionAssemblySupply

end GaugeGeometry.QFT.Combinatorial
