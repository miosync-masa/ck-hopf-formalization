import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocThreeRouteProvedCorrespondence
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightThreeRouteConcrete

/-!
# R-6c-heart-6a-8c-fix-3d-final — proved three-route correspondence → `right_eq` (new main line locked)

The corrected three-route vertex correspondence is now a PROVED bijection (`ResolvedThreeRouteProvedSupply.
toVertexCorrespondence`, fix-3c-5).  This wires it into the right-factor geometry and through to `right_eq`,
locking the new main line: the right factor's class equality flows from the PROVED correspondence, with the
inverse laws no longer fielded (they are the proved `corrLeftInv` / `corrRightInv`).

Since `ResolvedThreeRouteProvedSupply.toVertexCorrespondence s = (S.toInverseLawSupply).toVertexCorrespondence
s` definitionally, this adapts to fix-3d's `ResolvedRightThreeRouteConcreteGeometrySupply` (with
`Three := S.Three.toInverseLawSupply`) and reuses its `right_eq` — the `Perm` / `Edge` / `retargetVertex_eq`
carry over unchanged (defeq correspondences).

Per the HALT, no route-field / `Perm` / `Edge` / `retargetVertex_eq` concrete proofs; old star-map chain not
deleted.

Landed:

* `ResolvedRightThreeRouteProvedGeometrySupply D G imageOf` — proved `Three` + `Perm` + `Edge` +
  `retargetVertex_eq`;
* `.toConcreteGeometrySupply` — adapt to fix-3d's supply (`Three := Three.toInverseLawSupply`);
* `.right_eq` — the right-factor class equality from the PROVED correspondence.

So `ResolvedContractStarMapSupply` is fully retired from `right_eq`; the genuine remaining right-factor
obligations are the route fields + recovery/freshness facts + `Perm` / `Edge` / `retargetVertex_eq`.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **fix-3d-final — the proved-correspondence right geometry supply.** -/
structure ResolvedRightThreeRouteProvedGeometrySupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G) where
  /-- The PROVED three-route correspondence (inverse laws proved, fix-3c-5). -/
  Three : ResolvedThreeRouteProvedSupply D G imageOf
  /-- The perm extension over the proved correspondence. -/
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

/-- **fix-3d-final — adapt to fix-3d's concrete geometry supply.**  `Three := Three.toInverseLawSupply`;
the correspondences are definitionally equal, so `Perm` / `Edge` / `retargetVertex_eq` carry over. -/
def ResolvedRightThreeRouteProvedGeometrySupply.toConcreteGeometrySupply
    {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}
    (R : ResolvedRightThreeRouteProvedGeometrySupply D G imageOf) :
    ResolvedRightThreeRouteConcreteGeometrySupply D G imageOf where
  Three := R.Three.toInverseLawSupply
  Perm := R.Perm
  Edge := R.Edge
  retargetVertex_eq := R.retargetVertex_eq

/-- **fix-3d-final — `right_eq` from the PROVED three-route correspondence (new main line). -/
theorem ResolvedRightThreeRouteProvedGeometrySupply.right_eq
    {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}
    (R : ResolvedRightThreeRouteProvedGeometrySupply D G imageOf)
    (Inner : ResolvedCoassocInnerRightSupply D G) (s : ResolvedCoassocSplitChoice D G) :
    (D.supply G).rightTerm s.1 = Inner.innerRightTerm (imageOf s) :=
  R.toConcreteGeometrySupply.right_eq Inner s

end GaugeGeometry.QFT.Combinatorial
