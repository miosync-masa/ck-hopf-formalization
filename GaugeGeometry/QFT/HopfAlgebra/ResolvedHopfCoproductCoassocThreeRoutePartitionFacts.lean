import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocThreeRouteRecoverConcrete
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightStarIndexScout

/-!
# R-6c-heart-6a-9c — three-route partition facts (two discharged, one fielded)

The three case-analysis facts that the three-route correspondence dispatches on:

* **`leftStar_unique`** — distinct left stars are distinct vertices.  PROVED from `starOf` injectivity on the
  input outer components (the 6a-9a `oneRecover`); the `isLeft` hypotheses are unused (it holds for any two
  one-stage indices with equal star vertex).
* **`originalSurvivor_not_leftStar`** — an original survivor (`∈ G`) is never a left `δ`-star (a fresh
  star `∉ G`).  PROVED from the canonical freshness `freshA`; the `isLeft` hypothesis is unused.
* **`twoStageSurvivor_cases`** — a two-stage survivor is an original survivor or a left `δ`-star.  Genuine
  partition geometry — kept as a supply field.

Per the HALT, `quotientStarEquiv` / `survivingOriginal_to` / `leftStar_toSurvivor` / heavy
`selectedOuter`/`quotientForest` geometry are NOT touched.

Landed:

* `threeRoute_leftStar_unique` — from `ResolvedThreeRouteRecoverSupply` (`starOf` injectivity);
* `threeRoute_originalSurvivor_not_leftStar` — from `freshA`;
* `ResolvedThreeRoutePartitionFactSupply D G imageOf` — the genuine `twoStageSurvivor_cases` field.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}
  {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}

/-- **R-6c-heart-6a-9c — `leftStar_unique` from `starOf` injectivity.**  Distinct one-stage indices with
the same star vertex are equal (the `isLeft` hypotheses are unused). -/
theorem threeRoute_leftStar_unique (R : ResolvedThreeRouteRecoverSupply D G imageOf)
    (s : ResolvedCoassocSplitChoice D G) (i j : OneStageStarIndex D G s)
    (_hi : i.isLeft) (_hj : j.isLeft) (hv : i.vertex = j.vertex) : i = j := by
  have hη : i.η = j.η := (R.oneRecover s).star_injective_on_elements i.hη j.hη hv
  obtain ⟨ηi, hηi⟩ := i
  obtain ⟨ηj, hηj⟩ := j
  cases hη
  rfl

/-- **R-6c-heart-6a-9c — `originalSurvivor_not_leftStar` from canonical freshness.**  An original survivor
(in `G`) is never a left `δ`-star (a fresh star outside `G`); the `isLeft` hypothesis is unused. -/
theorem threeRoute_originalSurvivor_not_leftStar
    (freshA : ∀ (s : ResolvedCoassocSplitChoice D G), ∀ η ∈ s.1.1.elements,
      D.starOf G s.1.1 η ∉ G.vertices)
    (s : ResolvedCoassocSplitChoice D G) {v : VertexId} (hO : isContractSurvivingVertex s.1.1 v)
    (i : OneStageStarIndex D G s) (_hi : i.isLeft) : v ≠ i.vertex := by
  intro hveq
  have hmem : i.vertex ∈ G.vertices := hveq ▸ hO.1
  exact freshA s i.η i.hη hmem

/-- **R-6c-heart-6a-9c — the genuine partition fact (fielded).**  A two-stage survivor splits into an
original survivor or a left-primitive `δ`-star. -/
structure ResolvedThreeRoutePartitionFactSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G) where
  /-- A two-stage surviving vertex is an original survivor or a left-primitive `δ`-star. -/
  twoStageSurvivor_cases : ∀ (s : ResolvedCoassocSplitChoice D G) {v : VertexId},
    isContractSurvivingVertex (imageOf s).quotientForest v →
      isContractSurvivingVertex s.1.1 v ∨
        ∃ i : OneStageStarIndex D G s, i.isLeft ∧ i.vertex = v

end GaugeGeometry.QFT.Combinatorial
