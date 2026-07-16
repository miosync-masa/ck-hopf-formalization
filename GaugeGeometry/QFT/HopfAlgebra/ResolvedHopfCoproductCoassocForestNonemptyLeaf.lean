import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocMixedNePLExclusion
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRegionConstructionValue
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestImageClassifier

/-!
# R-6c-body-312 — the `forest_nonempty` leaf: a forest image has a nonempty forest region (PROVED)

Three-hundred-and-twelfth genuine-body step — the LAST membership leaf of the round-trip leaf supply (body-283/285),
proved directly (no scout).  A `resolvedIsForestImage` witness `δ` is, by definition, a star-touching component of `z.2`
— i.e. an element of `forestDomain z` — and `forestRecovered z` is the `componentToForest`-image of `forestDomain z`;
a nonempty index gives a nonempty image, regardless of what `componentToForest` returns.

## The shallow chain

```text
resolvedIsForestImage z.1 z.2  =  ∃ δ ∈ z.2.1.elements, ¬ Disjoint δ.vertices (starOfZ z)
→ δ ∈ forestDomain z            (= z.2.1.elements.filter (¬ Disjoint · (starOfZ z)); the predicate is identical)
→ componentToForest z ⟨δ, _⟩ ∈ forestRecovered z   (mem_image over forestDomain.attach; forestRecovered_elements_eq)
→ forestRecovered z nonempty
```

`starOfZ z = z.1.1.starVertices (D.starOf G z.1.1)` (RegionConstructionFromSector.lean:79) is EXACTLY the star set in
`resolvedIsForestImage` (ForestImageClassifier.lean:66-69), so the witness's touch condition IS the `forestDomain`
filter predicate — no re-derivation.

## What is NOT needed (the orphan is harmless here)

* `componentToForest z δ ∈ z.1.1.elements` is NOT used — floor-297/298 are untouched.  Even for an orphan `δ` (a
  star-spanning component with no single parent), the total `componentToForest` returns SOME bare `ResolvedFeynmanSubgraph G`,
  and the image of a nonempty index set is nonempty.  The false claim was only that the output lands in `z.1.1.elements`.
* No exact `B`, `forestTag`, occurrence, or `remnantInj`; no `carrier` properness; no forward identities.  Generic `z`.
* The `Finset.image_nonempty` dependent-function pitfall is avoided by supplying the explicit witness
  `componentToForest z ⟨δ, hdom⟩` and `Finset.mem_image.mpr`.

Per the HALT: only `forest_nonempty` is proved (for a generic `Region`); the round-trip re-plumbing (deriving the body-283
`Data` mixed/forest leaves from the L2 roots 310/311 + this leaf) and the carrier closure are later bodies; no facade, no
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

/-- **R-6c-body-312 — the `forest_nonempty` leaf.**  On a forest image (`resolvedIsForestImage z.1 z.2`), the recovered
forest region is nonempty: the star-touching witness `δ` lies in `forestDomain z`, so its `componentToForest` image lies
in `forestRecovered z`.  Independent of `componentToForest`'s content — the orphan defect (floor-297/298) is not touched. -/
theorem forestRecovered_nonempty_of_resolvedIsForestImage
    (Region : ResolvedRegionConstructionFromSectorValueSupply D)
    {G : ResolvedFeynmanGraph} {z : ForestBlockCodType D G}
    (hz : resolvedIsForestImage z.1 z.2) :
    (Region.forestRecovered z).elements.Nonempty := by
  obtain ⟨δ, hδ, hTouch⟩ := hz
  have hdom : δ ∈ forestDomain z := Finset.mem_filter.mpr ⟨hδ, hTouch⟩
  refine ⟨Region.componentToForest z ⟨δ, hdom⟩, ?_⟩
  rw [Region.forestRecovered_elements_eq]
  exact Finset.mem_image.mpr ⟨⟨δ, hdom⟩, Finset.mem_attach _ _, rfl⟩

end GaugeGeometry.QFT.Combinatorial
