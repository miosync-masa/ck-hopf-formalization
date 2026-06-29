import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocThreeRouteInverseLaws
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightThreeRouteFinalGeometry

/-!
# R-6c-heart-6a-8c-fix-3d — constructed three-route correspondence → `right_eq`

This plugs the CONSTRUCTED three-route correspondence (`ResolvedThreeRouteInverseLawSupply`, whose
`toVertexCorrespondence` is built from the real `threeRouteCorrToFun` / `threeRouteCorrInvFun` maps, fix-3b)
into the right-factor geometry, confirming it flows all the way to `right_eq` — with NO
`ResolvedContractStarMapSupply` anywhere.

Same shape as fix-3a's `ResolvedRightThreeRouteFinalGeometrySupply`, but `Three` is the
inverse-law supply (constructed maps) rather than the fix-2 skeleton (raw fielded maps).  The
`FieldEqSupply.ofEdgeLegData → ClassData` chain is generic in the correspondence, so the perm extension over
`Three.toVertexCorrespondence` feeds it directly.

Per the HALT, the inverse laws (inside `Three`) remain fields; no concrete `quotientStarEquiv` / recoveries;
old star-map chain not deleted.

Landed:

* `ResolvedRightThreeRouteConcreteGeometrySupply D G imageOf` — constructed `Three` + `Perm` + `Edge` +
  `retargetVertex_eq`;
* `.toClassData` / `.toContractTwiceOnceSupply` / `.right_eq` — through to the right-factor class equality.

So the entire RIGHT factor is now wired through the CORRECTED (three-route) correspondence; the genuine
remaining obligations are the inverse laws + the route fields (`quotientStarEquiv`, recoveries, partition
facts) + `Perm` / `Edge` / `retargetVertex_eq`.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-6a-8c-fix-3d — the concrete (constructed-correspondence) right geometry supply.** -/
structure ResolvedRightThreeRouteConcreteGeometrySupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G) where
  /-- The constructed three-route correspondence (real `toFun` / `invFun`). -/
  Three : ResolvedThreeRouteInverseLawSupply D G imageOf
  /-- The perm extension over the constructed correspondence. -/
  Perm : ∀ s : ResolvedCoassocSplitChoice D G,
    VertexPermExtension (Three.toVertexCorrespondence s)
  /-- The edge-domain connector (6a-6c). -/
  Edge : ResolvedRightEdgeDomainSupply D G imageOf
  /-- The contract-twice vertex composition, σ = `(Perm s).starPerm`. -/
  retargetVertex_eq : ∀ (s : ResolvedCoassocSplitChoice D G) (v : VertexId),
    s.1.1.retargetVertex (D.starOf G s.1.1) v
      = (Perm s).starPerm ((imageOf s).quotientForest.retargetVertex
          (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
          (rightVertexDomain (imageOf s) v))

/-- **R-6c-heart-6a-8c-fix-3d — the right-factor class datum from the constructed correspondence.** -/
noncomputable def ResolvedRightThreeRouteConcreteGeometrySupply.toClassData
    {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}
    (R : ResolvedRightThreeRouteConcreteGeometrySupply D G imageOf)
    (s : ResolvedCoassocSplitChoice D G) :
    ResolvedContractTwiceClassData (oneStageContractGraph s) (twoStageContractGraph imageOf s) :=
  (ResolvedContractTwiceFieldEqSupply.ofEdgeLegData (R.Perm s)
    (R.Edge.toEdgeLegVertexData s (R.Perm s).starPerm (R.retargetVertex_eq s)).toEdgeLegData).toClassData

/-- **R-6c-heart-6a-8c-fix-3d — the contract-twice = contract-once supply. -/
noncomputable def ResolvedRightThreeRouteConcreteGeometrySupply.toContractTwiceOnceSupply
    {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}
    (R : ResolvedRightThreeRouteConcreteGeometrySupply D G imageOf) :
    ResolvedContractTwiceOnceSupply D G imageOf where
  contract_class_eq := fun s => contract_class_eq_of_classData (R.toClassData s)

/-- **R-6c-heart-6a-8c-fix-3d — `right_eq`, fully wired from the CONSTRUCTED three-route correspondence. -/
theorem ResolvedRightThreeRouteConcreteGeometrySupply.right_eq
    {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}
    (R : ResolvedRightThreeRouteConcreteGeometrySupply D G imageOf)
    (Inner : ResolvedCoassocInnerRightSupply D G) (s : ResolvedCoassocSplitChoice D G) :
    (D.supply G).rightTerm s.1 = Inner.innerRightTerm (imageOf s) :=
  ResolvedContractTwiceOnceSupply.right_eq Inner R.toContractTwiceOnceSupply s

end GaugeGeometry.QFT.Combinatorial
