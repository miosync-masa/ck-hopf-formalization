import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSectorEquivAssembler
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocThreeRouteAssembler
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightThreeRouteProvedGeometry

/-!
# R-6c-heart-6a-11a — RIGHT factor grand assembler (one record → `right_eq`)

The whole RIGHT factor's `right_eq` is assembled here from a single top-level record.  The quotient-star
data (`Codomain` + `Sector`) feeds the BIGGEST (`Sector.toQuotientStarSupply`); together with `Transport` /
`Mechanical` / `Partition` it makes the proved three-route correspondence (`toProvedSupply`); adding `Perm`
/ `Edge` / `Retarget` yields the right-factor geometry, hence `right_eq`.

Split into two records to keep the `Perm` field type nameable:

* `ResolvedRightQuotientStarDataSupply` — `Codomain` + `Sector` + `Transport` + `Mechanical` + `Partition`,
  with `.toProvedSupply` the proved correspondence;
* `ResolvedRightGrandSupply` — `Data` + `Perm` (over `Data.toProvedSupply.toVertexCorrespondence`) + `Edge`
  + `Retarget`, with `.right_eq`.

Per the HALT, none of the leaf fields are proved; the remnant side and `product_eq` are untouched.

Landed:

* `ResolvedRightQuotientStarDataSupply D G imageOf` + `.toProvedSupply`;
* `ResolvedRightGrandSupply D G imageOf` + `.toRightThreeRouteProvedGeometrySupply` + `.right_eq`.

So the RIGHT factor's `right_eq` depends on exactly this one record's fields.

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

/-- **R-6c-heart-6a-11a — the quotient-star + route data (produces the proved correspondence).** -/
structure ResolvedRightQuotientStarDataSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G) where
  /-- The codomain `Right ⊔ Remnant` data (6a-10d). -/
  Codomain : ResolvedCodomainConcreteSupply D G imageOf
  /-- The sector equivalences (6a-10g-1) — the BIGGEST `quotientStarEquiv`. -/
  Sector : ResolvedSectorEquivAssemblerSupply Codomain
  /-- The vertex transport (6a-9d). -/
  Transport : ResolvedThreeRouteVertexTransportSupply D G imageOf
  /-- The recoveries + freshness (6a-9b). -/
  Mechanical : ResolvedThreeRouteMechanicalSupply D G imageOf
  /-- The partition fact (6a-9c). -/
  Partition : ResolvedThreeRoutePartitionFactSupply D G imageOf

/-- **R-6c-heart-6a-11a — the proved three-route correspondence supply from the quotient-star + route data. -/
noncomputable def ResolvedRightQuotientStarDataSupply.toProvedSupply
    (Q : ResolvedRightQuotientStarDataSupply D G imageOf) :
    ResolvedThreeRouteProvedSupply D G imageOf :=
  ResolvedThreeRouteAssembledSupply.toProvedSupply
    { Transport := Q.Transport, QuotientStar := Q.Sector.toQuotientStarSupply,
      Mechanical := Q.Mechanical, Partition := Q.Partition }

/-- **R-6c-heart-6a-11a — the RIGHT factor grand supply.** -/
structure ResolvedRightGrandSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G) where
  /-- The quotient-star + route data. -/
  Data : ResolvedRightQuotientStarDataSupply D G imageOf
  /-- The perm extension over the proved correspondence. -/
  Perm : ∀ s : ResolvedCoassocSplitChoice D G,
    VertexPermExtension (Data.toProvedSupply.toVertexCorrespondence s)
  /-- The edge-domain connector (6a-6c). -/
  Edge : ResolvedRightEdgeDomainSupply D G imageOf
  /-- The contract-twice vertex composition, σ = `(Perm s).starPerm`. -/
  Retarget : ∀ (s : ResolvedCoassocSplitChoice D G) (v : VertexId),
    s.1.1.retargetVertex (D.starOf G s.1.1) v
      = (Perm s).starPerm ((imageOf s).quotientForest.retargetVertex
          (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
          (rightVertexDomain (imageOf s) v))

/-- **R-6c-heart-6a-11a — into the right-factor proved geometry supply. -/
noncomputable def ResolvedRightGrandSupply.toRightThreeRouteProvedGeometrySupply
    (R : ResolvedRightGrandSupply D G imageOf) :
    ResolvedRightThreeRouteProvedGeometrySupply D G imageOf where
  Three := R.Data.toProvedSupply
  Perm := R.Perm
  Edge := R.Edge
  retargetVertex_eq := R.Retarget

/-- **R-6c-heart-6a-11a — `right_eq` for the RIGHT factor from the one grand record. -/
theorem ResolvedRightGrandSupply.right_eq
    (R : ResolvedRightGrandSupply D G imageOf)
    (Inner : ResolvedCoassocInnerRightSupply D G) (s : ResolvedCoassocSplitChoice D G) :
    (D.supply G).rightTerm s.1 = Inner.innerRightTerm (imageOf s) :=
  R.toRightThreeRouteProvedGeometrySupply.right_eq Inner s

end GaugeGeometry.QFT.Combinatorial
