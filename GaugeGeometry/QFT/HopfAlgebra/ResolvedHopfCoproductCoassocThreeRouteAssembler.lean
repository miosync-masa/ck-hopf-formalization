import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocThreeRouteVertexTransport
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocThreeRouteFreshConcrete
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocThreeRoutePartitionFacts
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocThreeRouteProvedCorrespondence

/-!
# R-6c-heart-6a-9e — three-route proved-supply assembler (route dependency compressed to 4 groups)

Assembles the whole `ResolvedThreeRouteProvedSupply` (whose `toVertexCorrespondence` is the PROVED
bijection, fix-3c-5) from four clean groups:

* `Transport` (6a-9d) — `survivingOriginal_to` / `leftStar_toSurvivor` / `twoStageSurvivor_cases`;
* `QuotientStar` (6a-9d) — the BIGGEST `quotientStarEquiv`;
* `Mechanical` (6a-9b) — recoveries (`starOf` injectivity) + canonical freshness, giving the 6 recovery
  fields + `freshA` / `freshB`;
* `Partition` (6a-9c) — the genuine `twoStageSurvivor_cases` (the two other partition facts,
  `leftStar_unique` / `originalSurvivor_not_leftStar`, are PROVED from `Mechanical`).

So `right_eq`'s route dependency is now exactly `{Transport, QuotientStar, star_injective×2, starOf_fresh}`
(plus `Perm` / `Edge` / `retargetVertex_eq`).  The next single target is the BIGGEST `quotientStarEquiv`.

Per the HALT, no Transport / QuotientStar / injectivity / freshness proofs, no `Edge` / `retargetVertex_eq`.

Landed:

* `ResolvedThreeRouteAssembledSupply D G imageOf` — the four groups;
* `.toFullSupply` / `.toProvedSupply` — the assembled proved supply.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-6a-9e — the assembled supply.**  The four groups feeding the proved three-route
correspondence. -/
structure ResolvedThreeRouteAssembledSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G) where
  /-- Vertex transport (6a-9d). -/
  Transport : ResolvedThreeRouteVertexTransportSupply D G imageOf
  /-- The BIGGEST quotient-star equivalence (6a-9d). -/
  QuotientStar : ResolvedThreeRouteQuotientStarSupply D G imageOf
  /-- Recoveries + freshness (6a-9b). -/
  Mechanical : ResolvedThreeRouteMechanicalSupply D G imageOf
  /-- The genuine partition fact (6a-9c). -/
  Partition : ResolvedThreeRoutePartitionFactSupply D G imageOf

variable {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}

/-- **R-6c-heart-6a-9e — the assembled full supply.** -/
noncomputable def ResolvedThreeRouteAssembledSupply.toFullSupply
    (A : ResolvedThreeRouteAssembledSupply D G imageOf) : ResolvedThreeRouteFullSupply D G imageOf where
  survivingOriginal_to := A.Transport.survivingOriginal_to
  leftStar_toSurvivor := A.Transport.leftStar_toSurvivor
  quotientStarEquiv := A.QuotientStar.quotientStarEquiv
  oneStarRecover := A.Mechanical.Recover.oneStarRecover
  oneStarRecover_vertex := A.Mechanical.Recover.oneStarRecover_vertex
  twoStageSurvivor_cases := A.Partition.twoStageSurvivor_cases
  twoStarRecover := A.Mechanical.Recover.twoStarRecover
  leftStar_unique := threeRoute_leftStar_unique A.Mechanical.Recover
  originalSurvivor_not_leftStar :=
    threeRoute_originalSurvivor_not_leftStar A.Mechanical.freshA

/-- **R-6c-heart-6a-9e — the assembled proved supply.** -/
noncomputable def ResolvedThreeRouteAssembledSupply.toProvedSupply
    (A : ResolvedThreeRouteAssembledSupply D G imageOf) : ResolvedThreeRouteProvedSupply D G imageOf where
  toResolvedThreeRouteFullSupply := A.toFullSupply
  honeInv := A.Mechanical.honeInv
  htwoInv := A.Mechanical.htwoInv
  twoStarVertex := A.Mechanical.twoStarVertex
  freshA := A.Mechanical.freshA
  freshB := A.Mechanical.freshB

end GaugeGeometry.QFT.Combinatorial
