import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocLocalizedParentCD

/-!
# R-6c-body-323 — the touched-based represented predicate + D5 coverage (PROVED)

Three-hundred-and-twenty-third genuine-body step — Front-1: the multi-star-correct replacement for body-303's
forest-parent image predicate `representedInQuotient A := ∃ δ, componentToForest δ = A`, which is WRONG in the faithful
model (a multi-star parent is not a single `z.1.1` component, so a touched component would be represented yet unequal to
the parent, wrongly falling into `leftResidual`).  The correct predicate is membership in a touched collection:

```lean
representedByTouched z A := ∃ δ ∈ forestDomain z, A ∈ touchedOuterComponents z δ
```

With this, **D5 coverage** (`leftResidual ∪ represented = z.1.1.elements`) is a definitional set partition — the
untouched components (`leftResidual`) and the touched components (`represented`) exhaust `z.1.1.elements`.

## Banked here

* `representedByTouched` — the touched-image predicate (δ a star-touching quotient component, `A` one of the outer
  components it absorbs).
* `leftResidualTouched` / `representedForestTouched` — the two filter halves of `z.1.1.elements`.
* `touched_coverage` (D5) — `leftResidualTouched z ∪ representedForestTouched z = z.1.1.elements` (filter
  partition, `Finset.filter_union_filter_not_eq`).
* `representedForestTouched_eq_biUnion` — the represented set IS `⋃ δ ∈ forestDomain z, touchedOuterComponents z δ`
  (the original D5 union form; the biUnion collapses to the filter by `touchedOuterComponents ⊆ z.1.1.elements`).

## The `innerRaw` API (named for M3, NOT built here)

`innerRaw` is value-only: retype each component of `touchedOuterForest z δ` INTO `localizedParent z δ hE hL` as a
`ResolvedAdmissibleSubgraph (localizedParent z δ hE hL).1`.  The M3 intermediate laws (body-324+):
```text
toInner A ∈ innerRaw.elements                                  (each touched A retypes into the parent)
promote (localizedParent …) (toInner A) = A                    (single-component promote round-trip)
every B ∈ innerRaw.elements comes from a touched A             (surjectivity of the retype)
⟹  (promote (localizedParent …) innerRaw).elements = touchedOuterComponents z δ   (M3, by Finset image ext)
```
`promote_elements` (ResolvedSubgraphPromote.lean:129: `(promote γ B).elements = B.elements.image (γ.promote ·)`) is the
engine; `innerRaw.elements` ↔ `touchedOuterComponents z δ` via the retype makes the image the touched collection —
replacing the retired singleton `promote_collapse`.

## Overlap / disjointness note

Distinct quotient components with disjoint vertices have disjoint touched collections (body-316
`touchedOuterComponents_disjoint`) — so the represented set is a disjoint union over the forest's components (needed for
the `Δᵣ`-side sum to be multiplicity-correct); no double-counting.

Per the HALT: only the predicate + the two filter halves + D5 coverage + the biUnion bridge are proved; `innerRaw` /
`toInner` / the promote-to-touched law (M3) are named, NOT built; body-303's parent-image predicate is NOT reused in the
faithful route; the parent is NOT returned to a `z.1.1` component; `innerRaw` is NOT a `ForestIdx`; the M2b parent CD is
NOT mixed into the set equalities; no singleton collapse; no facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-323 — the touched-based represented predicate.**  An outer component `A` is represented when some
star-touching quotient component `δ` absorbs it. -/
def representedByTouched {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (A : ResolvedFeynmanSubgraph G) : Prop :=
  ∃ δ ∈ forestDomain z, A ∈ touchedOuterComponents z δ

/-- **R-6c-body-323 — the untouched (left-residual) outer components.** -/
noncomputable def leftResidualTouched {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) :
    Finset (ResolvedFeynmanSubgraph G) :=
  z.1.1.elements.filter (fun A => ¬ representedByTouched z A)

/-- **R-6c-body-323 — the touched (represented) outer components.** -/
noncomputable def representedForestTouched {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) :
    Finset (ResolvedFeynmanSubgraph G) :=
  z.1.1.elements.filter (representedByTouched z)

/-- **R-6c-body-323 — D5 coverage.**  Untouched ∪ touched exhausts the outer components (filter partition). -/
theorem touched_coverage {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) :
    leftResidualTouched z ∪ representedForestTouched z = z.1.1.elements := by
  ext A
  rw [leftResidualTouched, representedForestTouched, Finset.mem_union, Finset.mem_filter,
    Finset.mem_filter]
  constructor
  · rintro (⟨hA, -⟩ | ⟨hA, -⟩) <;> exact hA
  · intro hA
    by_cases h : representedByTouched z A
    · exact Or.inr ⟨hA, h⟩
    · exact Or.inl ⟨hA, h⟩

/-- **R-6c-body-323 — the represented set is the touched-collection union** (the original D5 `⋃` form). -/
theorem representedForestTouched_eq_biUnion {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) :
    representedForestTouched z = (forestDomain z).biUnion (touchedOuterComponents z) := by
  ext A
  rw [representedForestTouched, Finset.mem_filter, Finset.mem_biUnion]
  constructor
  · rintro ⟨-, δ, hδ, hAδ⟩; exact ⟨δ, hδ, hAδ⟩
  · rintro ⟨δ, hδ, hAδ⟩
    exact ⟨(mem_touchedOuterComponents.mp hAδ).1, δ, hδ, hAδ⟩

end GaugeGeometry.QFT.Combinatorial
