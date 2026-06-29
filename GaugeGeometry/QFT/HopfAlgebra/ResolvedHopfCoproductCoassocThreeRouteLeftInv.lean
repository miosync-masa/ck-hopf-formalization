import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocThreeRouteRoundTripQuotient
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocThreeRouteRoundTripLeft
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocThreeRouteRoundTripOriginal

/-!
# R-6c-heart-6a-8c-fix-3c-2 — `corrLeftInv` from the three round-trip cases

Assembles the left-inverse law `invFun ∘ toFun = id` for the three-route correspondence by dispatching a
one-stage vertex through `contractWithStars_vertex_cases` and the recovered index's
`isLeft_or_hasQuotientStar`:

```
survivor (G \ A)            → threeRoute_leftInv_originalSurvivor (fix-3c-1c)
star, recovered index isLeft → threeRoute_leftInv_leftStar       (fix-3c-1b)
star, recovered ¬isLeft      → threeRoute_leftInv_quotientStar   (fix-3c-1a)
```

The three round-trip lemmas need a few facts not in the base supply — collected into
`ResolvedThreeRouteLeftInvSupply`: `htwoInv` (`twoStarRecover` inverts `toStarVertex`) and the two star
freshnesses `freshA` / `freshB` (both free from the canonical fresh-star property 6a-7a and the concrete
recoveries 6a-8b-2).  `isLeft_or_hasQuotientStar` is already a theorem (6a-8c-0), so no left/quotient
classification field is needed.

Per the HALT, only `corrLeftInv`; no `corrRightInv`, no concrete recoveries / `quotientStarEquiv`.

Landed:

* `ResolvedThreeRouteLeftInvSupply D G imageOf` — base supply + `htwoInv` / `freshA` / `freshB`;
* `threeRoute_corrLeftInv` — the assembled left-inverse law (per split choice).

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **fix-3c-2 — the left-inverse supply.**  The base correspondence data plus the recovery-inverse fact and
the two star freshnesses the round-trip cases need. -/
structure ResolvedThreeRouteLeftInvSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G)
    extends ResolvedThreeRouteFullSupply D G imageOf where
  /-- `twoStarRecover` inverts the canonical index → star-vertex map. -/
  htwoInv : ∀ (s : ResolvedCoassocSplitChoice D G) (j : TwoStageStarIndex D G imageOf s),
    twoStarRecover s j.toStarVertex = j
  /-- The input outer forest's stars are fresh. -/
  freshA : ∀ (s : ResolvedCoassocSplitChoice D G), ∀ η ∈ s.1.1.elements,
    D.starOf G s.1.1 η ∉ G.vertices
  /-- The quotient forest's stars are fresh. -/
  freshB : ∀ (s : ResolvedCoassocSplitChoice D G), ∀ η ∈ (imageOf s).quotientForest.elements,
    D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest η
      ∉ (resolvedCoassocQuotientGraph (imageOf s)).vertices

/-- **fix-3c-2 — the assembled left-inverse law.**  Dispatch over `contractWithStars_vertex_cases` and the
recovered index's `isLeft`. -/
theorem threeRoute_corrLeftInv {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}
    (S : ResolvedThreeRouteLeftInvSupply D G imageOf) (s : ResolvedCoassocSplitChoice D G) :
    Function.LeftInverse
      (threeRouteCorrInvFun S.toResolvedThreeRouteFullSupply.toResolvedThreeRouteInvFunSupply s)
      (threeRouteCorrToFun S.toResolvedThreeRouteFullSupply.toResolvedThreeRouteToFunSupply s) := by
  intro w
  rcases contractWithStars_vertex_cases s.1.1 (D.starOf G s.1.1) w.2 with hSurv | hstar
  · exact threeRoute_leftInv_originalSurvivor S.toResolvedThreeRouteFullSupply s w hSurv
      (S.freshA s) (S.freshB s)
  · by_cases hL : (S.oneStarRecover s ⟨w.1, hstar⟩).isLeft
    · exact threeRoute_leftInv_leftStar S.toResolvedThreeRouteFullSupply s w hstar hL (S.freshB s)
    · exact threeRoute_leftInv_quotientStar S.toResolvedThreeRouteFullSupply s w hstar hL
        (S.htwoInv s)

end GaugeGeometry.QFT.Combinatorial
