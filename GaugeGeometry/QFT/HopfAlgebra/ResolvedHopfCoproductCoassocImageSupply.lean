import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocImageOf

/-!
# R-6c-4f part 3b — the concrete splitPhi image supply

The concrete `imageOf` (the resolved `forestComponentSplitPhi`) is assembled from two per-split-choice
data: the **selected outer forest** `selectedOuterOf s` (a carrier forest, determined by the
left-selected / promoted components of the choice) and the **quotient forest** `quotientForestOf s` (a
subforest of the selected outer's star-contraction).  These are the genuine de-contraction obligations
(the selected-outer construction + its carrier membership), kept as **supply fields** — so this file
fixes the assembly without descending into the component-closure proof.

`imageOf s := ⟨selectedOuterOf s, quotientForestOf s⟩` then lands directly in
`ResolvedCoassocQuotientImage`, and `toImageOfData` produces the part-3a map data (still no term
agreement).

Landed:

* `ResolvedCoassocSplitPhiImageSupply D G` — `selectedOuterOf`, `quotientForestOf`, `imageWeightOf`,
  `discriminatorOf` (the de-contraction map as supply fields);
* `ResolvedCoassocSplitPhiImageSupply.toImageOfData` — assemble `imageOf` and recover
  `ResolvedCoassocSplitPhiImageOfData`.

No facade, no flat splitPhi theorem, no `forgetHopf`; the concrete `selectedOuterOf` (the
component-closure de-contraction) and `term_eq` are the remaining work.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-4f part 3b — the concrete splitPhi image supply.**  The resolved `forestComponentSplitPhi`
factored into its two de-contraction obligations: the selected outer forest (a carrier forest) and the
quotient forest (a subforest of its star-contraction), plus the image weight and the star
discriminator.  Supplying this is the concrete de-contraction (the `selectedOuterOf` component-closure
and its carrier membership are isolated as the field types). -/
structure ResolvedCoassocSplitPhiImageSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph) where
  /-- The selected outer forest of a split choice (a carrier forest). -/
  selectedOuterOf : ResolvedCoassocSplitChoice D G → {A : ResolvedAdmissibleSubgraph G // A ∈ D.carrier G}
  /-- The quotient forest of a split choice (a subforest of the selected outer's star-contraction). -/
  quotientForestOf : (s : ResolvedCoassocSplitChoice D G) →
    ResolvedAdmissibleSubgraph
      ((selectedOuterOf s).1.contractWithStars (D.starOf G (selectedOuterOf s).1))
  /-- The image (quotient) weight in `ResolvedHopfH3`. -/
  imageWeightOf : ResolvedCoassocQuotientImage D G → ResolvedHopfH3
  /-- The star discriminator. -/
  discriminatorOf : ResolvedCoassocQuotientImage D G → Prop

/-- **R-6c-4f part 3b — assemble the splitPhi map data.**  `imageOf s := ⟨selectedOuterOf s,
quotientForestOf s⟩`, recovering the part-3a `ResolvedCoassocSplitPhiImageOfData` (still no term
agreement). -/
def ResolvedCoassocSplitPhiImageSupply.toImageOfData (S : ResolvedCoassocSplitPhiImageSupply D G) :
    ResolvedCoassocSplitPhiImageOfData D G where
  imageOf := fun s =>
    { selectedOuter := S.selectedOuterOf s, quotientForest := S.quotientForestOf s }
  imageWeight := S.imageWeightOf
  discriminator := S.discriminatorOf

end GaugeGeometry.QFT.Combinatorial
