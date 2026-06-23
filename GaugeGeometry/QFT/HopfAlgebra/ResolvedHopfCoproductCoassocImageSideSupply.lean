import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocQuotientForest

/-!
# R-6c-support-7 — image-side supply → `ResolvedCoassocSplitPhiImageOfData`

The last vessel hop before the heart.  With the three image-side fields isolated as supply
(`selectedOuterOf` wired in support-5, `quotientForestOf` in support-6, `imageWeightOf` /
`discriminatorOf` as inputs), the resolved `forestComponentSplitPhi` map data
(`ResolvedCoassocSplitPhiImageOfData D G`) is reached by `toImageSupply` followed by the part-3b
`ResolvedCoassocSplitPhiImageSupply.toImageOfData` — **with no term agreement** (`term_eq` is the very
next step, R-6c part 3c).

This file gives the direct `Q.toImageOfData` adapter and a bundled
`ResolvedCoassocImageSideSupply` collecting the whole image side (selected-outer supply + quotient-forest
supply + image weight + discriminator) into one record, with `.toImageOfData` producing the map data.
So the full chain up to (but not including) `term_eq` now reads as one supply record.

Landed:

* `ResolvedCoassocQuotientForestSupply.toImageOfData` — `(Q.toImageSupply …).toImageOfData`;
* `ResolvedCoassocImageSideSupply D G` — the bundled image side (`selected`, `quotient`,
  `imageWeightOf`, `discriminatorOf`);
* `ResolvedCoassocImageSideSupply.toImageSupply` / `.toImageOfData` — the assembled image supply and
  splitPhi map data.

No facade, no flat splitPhi theorem, no `forgetHopf`, no `term_eq`; the term agreement and finite
carriers/cover are the remaining work.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-support-7 — the splitPhi map data from the quotient-forest supply.**  Compose
`toImageSupply` with the part-3b `toImageOfData`: `imageOf s := ⟨selectedOuterOf s, quotientForestOf s⟩`
with the supplied weight and discriminator, still NO term agreement. -/
noncomputable def ResolvedCoassocQuotientForestSupply.toImageOfData
    {S : ResolvedCoassocSelectedOuterImageSupply D G}
    (Q : ResolvedCoassocQuotientForestSupply D G S)
    (imageWeightOf : ResolvedCoassocQuotientImage D G → ResolvedHopfH3)
    (discriminatorOf : ResolvedCoassocQuotientImage D G → Prop) :
    ResolvedCoassocSplitPhiImageOfData D G :=
  (Q.toImageSupply imageWeightOf discriminatorOf).toImageOfData

/-- **R-6c-support-7 — the bundled image side.**  Collects the whole image-side de-contraction as one
supply record: the selected-outer supply, the quotient-forest supply over it, the image weight, and the
star discriminator.  Everything needed for the resolved `forestComponentSplitPhi` *map* (not yet the
term agreement). -/
structure ResolvedCoassocImageSideSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph) where
  /-- The selected-outer supply (left selection + promote + carrier membership). -/
  selected : ResolvedCoassocSelectedOuterImageSupply D G
  /-- The quotient-forest supply over `selected`. -/
  quotient : ResolvedCoassocQuotientForestSupply D G selected
  /-- The image (quotient) weight in `ResolvedHopfH3`. -/
  imageWeightOf : ResolvedCoassocQuotientImage D G → ResolvedHopfH3
  /-- The star discriminator. -/
  discriminatorOf : ResolvedCoassocQuotientImage D G → Prop

/-- The assembled splitPhi image supply from the bundled image side. -/
noncomputable def ResolvedCoassocImageSideSupply.toImageSupply
    (I : ResolvedCoassocImageSideSupply D G) : ResolvedCoassocSplitPhiImageSupply D G :=
  I.quotient.toImageSupply I.imageWeightOf I.discriminatorOf

/-- **R-6c-support-7 — the splitPhi map data from the bundled image side.**  The resolved
`forestComponentSplitPhi` map data, one supply record away from the term agreement. -/
noncomputable def ResolvedCoassocImageSideSupply.toImageOfData
    (I : ResolvedCoassocImageSideSupply D G) : ResolvedCoassocSplitPhiImageOfData D G :=
  I.quotient.toImageOfData I.imageWeightOf I.discriminatorOf

end GaugeGeometry.QFT.Combinatorial
