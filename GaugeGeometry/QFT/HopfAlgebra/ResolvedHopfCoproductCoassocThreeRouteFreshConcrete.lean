import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocThreeRouteRecoverConcrete
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightFresh

/-!
# R-6c-heart-6a-9b — three-route freshness from the canonical fresh-star property + mechanical bundle

The three-route correspondence's `freshA` / `freshB` are instances of the single canonical fresh-star
property `ResolvedCanonicalStarFreshSupply.starOf_fresh` (6a-7a), exactly as in the old right freshness
supply.  This file supplies them in the `ResolvedThreeRouteProvedSupply` shape, and bundles them with the
6a-9a recoveries into one **mechanical** supply, so the entire "mechanical" half of the proved
correspondence (recoveries + their specs + freshness) reduces to `Recover` (two `starOf`-injectivities) +
`canonicalFresh` (one universal fresh-star property).

Per the HALT, `star_injective_on_elements` and `starOf_fresh` are NOT proved (the supply fields);
`quotientStarEquiv` / partition facts / `Perm` / `Edge` / `retargetVertex_eq` are NOT touched.

Landed:

* `ResolvedCanonicalStarFreshSupply.toThreeRouteFreshA` / `…FreshB` — the two freshness facts;
* `ResolvedThreeRouteMechanicalSupply D G imageOf` — `Recover` + `canonicalFresh`, with all mechanical
  fields (`oneStarRecover` / `twoStarRecover` / `oneStarRecover_vertex` / `honeInv` / `htwoInv` /
  `twoStarVertex` / `freshA` / `freshB`) derived.

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

/-- **R-6c-heart-6a-9b — `freshA` from the canonical fresh-star property. -/
theorem ResolvedCanonicalStarFreshSupply.toThreeRouteFreshA (F : ResolvedCanonicalStarFreshSupply D)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G)
    (s : ResolvedCoassocSplitChoice D G) : ∀ η ∈ s.1.1.elements, D.starOf G s.1.1 η ∉ G.vertices :=
  fun η hη => F.starOf_fresh G s.1.1 η hη

/-- **R-6c-heart-6a-9b — `freshB` from the canonical fresh-star property. -/
theorem ResolvedCanonicalStarFreshSupply.toThreeRouteFreshB (F : ResolvedCanonicalStarFreshSupply D)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G)
    (s : ResolvedCoassocSplitChoice D G) :
    ∀ η ∈ (imageOf s).quotientForest.elements,
      D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest η
        ∉ (resolvedCoassocQuotientGraph (imageOf s)).vertices :=
  fun η hη => F.starOf_fresh (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest η hη

/-- **R-6c-heart-6a-9b — the mechanical supply.**  Recoveries (`starOf` injectivity) + canonical freshness;
the whole mechanical half of the proved correspondence. -/
structure ResolvedThreeRouteMechanicalSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G) where
  /-- The star recoveries (6a-9a). -/
  Recover : ResolvedThreeRouteRecoverSupply D G imageOf
  /-- The canonical fresh-star property (6a-7a). -/
  canonicalFresh : ResolvedCanonicalStarFreshSupply D

namespace ResolvedThreeRouteMechanicalSupply

variable (M : ResolvedThreeRouteMechanicalSupply D G imageOf)

/-- The one-stage star recovery. -/
noncomputable def oneStarRecover (s : ResolvedCoassocSplitChoice D G) :=
  M.Recover.oneStarRecover s

/-- The two-stage star recovery. -/
noncomputable def twoStarRecover (s : ResolvedCoassocSplitChoice D G) :=
  M.Recover.twoStarRecover s

/-- `oneStarRecover` preserves the star vertex. -/
theorem oneStarRecover_vertex (s : ResolvedCoassocSplitChoice D G)
    (w : {v : VertexId // isContractStarVertex s.1.1 (D.starOf G s.1.1) v}) :
    (M.Recover.oneStarRecover s w).vertex = w.1 := M.Recover.oneStarRecover_vertex s w

/-- `oneStarRecover` inverts `toStarVertex`. -/
theorem honeInv (s : ResolvedCoassocSplitChoice D G) (i : OneStageStarIndex D G s) :
    M.Recover.oneStarRecover s i.toStarVertex = i := M.Recover.honeInv s i

/-- `twoStarRecover` inverts `toStarVertex`. -/
theorem htwoInv (s : ResolvedCoassocSplitChoice D G) (j : TwoStageStarIndex D G imageOf s) :
    M.Recover.twoStarRecover s j.toStarVertex = j := M.Recover.htwoInv s j

/-- `twoStarRecover` preserves the star vertex. -/
theorem twoStarVertex (s : ResolvedCoassocSplitChoice D G)
    (w : {v : VertexId // isContractStarVertex (imageOf s).quotientForest
      (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest) v}) :
    (M.Recover.twoStarRecover s w).vertex = w.1 := M.Recover.twoStarVertex s w

include M in
/-- The input outer forest's stars are fresh. -/
theorem freshA (s : ResolvedCoassocSplitChoice D G) :
    ∀ η ∈ s.1.1.elements, D.starOf G s.1.1 η ∉ G.vertices :=
  ResolvedCanonicalStarFreshSupply.toThreeRouteFreshA M.canonicalFresh imageOf s

include M in
/-- The quotient forest's stars are fresh. -/
theorem freshB (s : ResolvedCoassocSplitChoice D G) :
    ∀ η ∈ (imageOf s).quotientForest.elements,
      D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest η
        ∉ (resolvedCoassocQuotientGraph (imageOf s)).vertices :=
  ResolvedCanonicalStarFreshSupply.toThreeRouteFreshB M.canonicalFresh imageOf s

end ResolvedThreeRouteMechanicalSupply

end GaugeGeometry.QFT.Combinatorial
