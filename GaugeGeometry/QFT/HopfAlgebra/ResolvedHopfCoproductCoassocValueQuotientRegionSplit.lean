import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRegionConstructionFromSector
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocConcreteSummandValue

/-!
# R-6c-body-274 — the value-root quotient/region split: `rightDomain` ↔ survivor, `forestDomain` ↔ remnant (PROVED)

Two-hundred-and-seventy-fourth genuine-body step — the shared MEDIUM crux of the value-root cover migration (body-273),
proved once.  For `z = fwdMapFilteredValue F V q`, the star-classified quotient halves `rightDomain z` (star-avoiding)
and `forestDomain z` (star-touching) are exactly the value bundle's survivor / remnant forests, at the membership level.

## Why this is the crux

The region domains read the QUOTIENT (`RegionConstructionFromSector.lean:88,94`):

```lean
rightDomain  z := z.2.1.elements.filter (fun δ => Disjoint δ.vertices (starOfZ z))
forestDomain z := z.2.1.elements.filter (fun δ => ¬ Disjoint δ.vertices (starOfZ z))
```

At the value root `z.2 = V.quotientForestRaw q.1` (rfl), and `V.union_eq` splits that quotient as
`survivor ∪ remnant`.  With the survivor/remnant vs outer-star facts (`survivor_avoids` / `remnant_touches` — the value
image of body-150's `ResolvedRegionStarFactSupply.survivor_avoids`, re-keyed to the value outer, which agrees with the
total outer by `rfl` since `starOfZ` reads only `z.1.1 = selectedOuterRawOf q.1`), the star filter picks out exactly the
survivor half (and its complement the remnant half).  This resolves the value-root crux WITHOUT the total forward map:
the quotient source is `V`, not `S`.

## The threaded star facts (not new leaves)

`survivor_avoids` / `remnant_touches` are supplied as fields — the value-root images of the existing region star facts
(body-150).  They are the *definitional* meaning of the survivor/remnant split (survivors avoid the outer star, remnants
touch it); no coassociativity leaf is duplicated, and no `Forward` / total root appears.

Per the HALT: only the two-way quotient split is closed (`rightDomain` ↔ survivor, `forestDomain` ↔ remnant); the
`componentToRight` / `componentToForest` maps and the 170/171 source correspondences are NOT entered.  No facade, no
flat term, no `forgetHopf`.
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

/-- **R-6c-body-274 — the value-root quotient/region star facts.**  The survivor components avoid the value outer star,
the remnant components touch it — the value image of body-150's region star facts, keyed on `fwdMapFilteredValue`. -/
structure ResolvedValueQuotientRegionSplitSupply (F : ResolvedSelectedOuterFilteredMemSupply D)
    (V : ResolvedConcreteSummandValueSupply D) where
  /-- Every survivor component avoids the value outer star. -/
  survivor_avoids : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G),
    ∀ δ ∈ (V.Survivor.survivor.rightSurvivorForest q.1).elements,
      Disjoint δ.vertices (starOfZ (fwdMapFilteredValue F V q))
  /-- Every remnant component touches the value outer star. -/
  remnant_touches : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G),
    ∀ δ ∈ (V.Remnant.remnant.remnantForest q.1).elements,
      ¬ Disjoint δ.vertices (starOfZ (fwdMapFilteredValue F V q))

namespace ResolvedValueQuotientRegionSplitSupply

variable {F : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}

/-- **R-6c-body-274 — the value-root quotient membership splits as survivor ∨ remnant** (from `V.union_eq`). -/
theorem mem_quotient_iff {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (δ : ResolvedFeynmanSubgraph (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)) :
    δ ∈ (fwdMapFilteredValue F V q).2.1.elements
      ↔ δ ∈ (V.Survivor.survivor.rightSurvivorForest q.1).elements
        ∨ δ ∈ (V.Remnant.remnant.remnantForest q.1).elements := by
  change δ ∈ (V.quotientForestRaw q.1).1.elements ↔ _
  rw [V.union_eq q.1, ResolvedAdmissibleSubgraph.union_elements]
  exact @Finset.mem_union _ (Classical.decEq _) _ _ _

/-- **R-6c-body-274 — `rightDomain` ↔ survivor** at the value root (membership level). -/
theorem rightDomain_value_mem (P : ResolvedValueQuotientRegionSplitSupply F V)
    {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (δ : ResolvedFeynmanSubgraph (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)) :
    δ ∈ rightDomain (fwdMapFilteredValue F V q) ↔
      δ ∈ (V.Survivor.survivor.rightSurvivorForest q.1).elements := by
  unfold rightDomain
  constructor
  · intro h
    obtain ⟨hmem, hdisj⟩ := Finset.mem_filter.mp h
    rcases (mem_quotient_iff q δ).mp hmem with hs | hr
    · exact hs
    · exact absurd hdisj (P.remnant_touches q δ hr)
  · intro hs
    exact Finset.mem_filter.mpr ⟨(mem_quotient_iff q δ).mpr (Or.inl hs), P.survivor_avoids q δ hs⟩

/-- **R-6c-body-274 — `forestDomain` ↔ remnant** at the value root (membership level). -/
theorem forestDomain_value_mem (P : ResolvedValueQuotientRegionSplitSupply F V)
    {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (δ : ResolvedFeynmanSubgraph (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)) :
    δ ∈ forestDomain (fwdMapFilteredValue F V q) ↔
      δ ∈ (V.Remnant.remnant.remnantForest q.1).elements := by
  unfold forestDomain
  constructor
  · intro h
    obtain ⟨hmem, hdisj⟩ := Finset.mem_filter.mp h
    rcases (mem_quotient_iff q δ).mp hmem with hs | hr
    · exact absurd (P.survivor_avoids q δ hs) hdisj
    · exact hr
  · intro hr
    exact Finset.mem_filter.mpr ⟨(mem_quotient_iff q δ).mpr (Or.inr hr), P.remnant_touches q δ hr⟩

end ResolvedValueQuotientRegionSplitSupply

end GaugeGeometry.QFT.Combinatorial
