import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocThreeRouteRightInvQuotient
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocThreeRouteRightInvLeft
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocThreeRouteRightInvOriginal

/-!
# R-6c-heart-6a-8c-fix-3c-4 — `corrRightInv` from the three right-inverse cases

Assembles the right-inverse law `toFun ∘ invFun = id` for the three-route correspondence by dispatching a
two-stage vertex through `contractWithStars_vertex_cases` and (for survivors) `twoStageSurvivor_cases`:

```
two-stage star                 → threeRoute_rightInv_quotientStar     (fix-3c-3a)
two-stage survivor, original    → threeRoute_rightInv_originalSurvivor (fix-3c-3c)
two-stage survivor, left δ-star → threeRoute_rightInv_leftStarSurvivor (fix-3c-3b)
```

The star case identifies `w` with `(twoStarRecover w).toStarVertex` via the `twoStarVertex` agreement
(`(twoStarRecover w).vertex = w.1`); the survivor case `rcases` the existential disjunction directly (the
goal is an equation, a `Prop`).  Extra facts beyond the base supply (`honeInv` / `htwoInv` / `twoStarVertex`
/ `freshA` / `freshB`) are collected into `ResolvedThreeRouteRightInvSupply`; all are free from the concrete
recoveries (6a-8b-2) and the canonical fresh-star property (6a-7a).

Per the HALT, only `corrRightInv`; no `corrLeftInv`, no `ResolvedThreeRouteInverseLawSupply` final fill, no
concrete route fields.

Landed:

* `ResolvedThreeRouteRightInvSupply D G imageOf` — base supply + `honeInv` / `htwoInv` / `twoStarVertex` /
  `freshA` / `freshB`;
* `threeRoute_corrRightInv` — the assembled right-inverse law (per split choice).

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **fix-3c-4 — the right-inverse supply.**  The base correspondence data plus the recovery-inverse facts,
the two-stage star vertex agreement, and the two star freshnesses. -/
structure ResolvedThreeRouteRightInvSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G)
    extends ResolvedThreeRouteFullSupply D G imageOf where
  /-- `oneStarRecover` inverts the canonical index → star-vertex map. -/
  honeInv : ∀ (s : ResolvedCoassocSplitChoice D G) (i : OneStageStarIndex D G s),
    oneStarRecover s i.toStarVertex = i
  /-- `twoStarRecover` inverts the canonical index → star-vertex map. -/
  htwoInv : ∀ (s : ResolvedCoassocSplitChoice D G) (j : TwoStageStarIndex D G imageOf s),
    twoStarRecover s j.toStarVertex = j
  /-- The recovered two-stage index's star vertex is the original. -/
  twoStarVertex : ∀ (s : ResolvedCoassocSplitChoice D G)
    (w : {v : VertexId // isContractStarVertex (imageOf s).quotientForest
      (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest) v}),
    (twoStarRecover s w).vertex = w.1
  /-- The input outer forest's stars are fresh. -/
  freshA : ∀ (s : ResolvedCoassocSplitChoice D G), ∀ η ∈ s.1.1.elements,
    D.starOf G s.1.1 η ∉ G.vertices
  /-- The quotient forest's stars are fresh. -/
  freshB : ∀ (s : ResolvedCoassocSplitChoice D G), ∀ η ∈ (imageOf s).quotientForest.elements,
    D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest η
      ∉ (resolvedCoassocQuotientGraph (imageOf s)).vertices

/-- **fix-3c-4 — the assembled right-inverse law.**  Dispatch over `contractWithStars_vertex_cases` and
`twoStageSurvivor_cases`. -/
theorem threeRoute_corrRightInv {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}
    (S : ResolvedThreeRouteRightInvSupply D G imageOf) (s : ResolvedCoassocSplitChoice D G) :
    Function.RightInverse
      (threeRouteCorrInvFun S.toResolvedThreeRouteFullSupply.toResolvedThreeRouteInvFunSupply s)
      (threeRouteCorrToFun S.toResolvedThreeRouteFullSupply.toResolvedThreeRouteToFunSupply s) := by
  intro w
  rcases contractWithStars_vertex_cases (imageOf s).quotientForest
    (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest) w.2 with hSurv | hstar
  · rcases S.twoStageSurvivor_cases s hSurv with hOrig | ⟨i, hL, hvw⟩
    · exact threeRoute_rightInv_originalSurvivor S.toResolvedThreeRouteFullSupply s w hSurv hOrig
        (S.freshA s) (S.freshB s)
    · exact threeRoute_rightInv_leftStarSurvivor S.toResolvedThreeRouteFullSupply s w i hL hvw
        (S.honeInv s) (S.freshB s) hSurv
  · set j := S.twoStarRecover s ⟨w.1, hstar⟩ with hj
    have hweq : w = ⟨j.vertex, star_mem_contractWithStars (imageOf s).quotientForest
        (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
        j.toStarVertex.2⟩ := Subtype.ext (S.twoStarVertex s ⟨w.1, hstar⟩).symm
    rw [hweq]
    exact threeRoute_rightInv_quotientStar S.toResolvedThreeRouteFullSupply s j
      (S.htwoInv s j) (S.honeInv s)

end GaugeGeometry.QFT.Combinatorial
