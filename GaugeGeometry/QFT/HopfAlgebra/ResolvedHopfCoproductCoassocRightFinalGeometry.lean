import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightPermExtension
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightEdgeConnector

/-!
# R-6c-heart-6a-6f — RIGHT `FinalGeometryData` combiner (the wiring closed to `right_eq`)

The last RIGHT obligation not yet isolated is `retargetVertex_eq` (the contract-twice vertex composition,
which `σ = permExt.starPerm` pins to `starToStar`).  This file isolates it as a supply and then **wires the
entire right factor end to end**: from the six named supplies (star bijection / surviving / freshness / perm
extension / edge domain / retarget) to `ResolvedContractTwiceFinalGeometryData`, hence to `right_eq`.

So after this, the RIGHT side is purely "named supply fields" — every remaining obligation is a concrete
construction (the BIGGEST being `starToStar`), with all the assembly done.

Per the HALT, `retargetVertex_eq` is NOT proved, no concrete `starToStar`, no `edge_domain_eq` proof.

Landed:

* `ResolvedRightRetargetVertexSupply … Perm` — the `retargetVertex_eq` hole (σ = `Perm.starPerm s`), in
  the shape `EdgeDomainSupply.toEdgeLegVertexData` asks for;
* `ResolvedRightFinalGeometrySupply D G imageOf` — the six named halves bundled;
* `.toFinalGeometryData s` — the full per-`s` `ResolvedContractTwiceFinalGeometryData`;
* `.toContractTwiceOnceSupply` / `.right_eq` — through to the right-factor class equality (the `right_eq`
  half of the `term_eq` heart).

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

/-- **R-6c-heart-6a-6f — the right `retargetVertex_eq` supply.**  The contract-twice vertex composition:
contracting the input outer `s.1.1` once equals `permExt.starPerm` applied to contracting the quotient
forest after the stage-1 `rightVertexDomain`.  σ is fixed to `Perm.starPerm s` (the perm extension's
permutation). -/
structure ResolvedRightRetargetVertexSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G)
    (Star : ResolvedRightStarBijectionSupply D G imageOf)
    (Surv : ResolvedRightSurvivingSupply D G imageOf)
    (Fresh : ResolvedRightStarFreshSupply D G imageOf)
    (Perm : ResolvedRightPermExtensionSupply D G imageOf Star Surv Fresh) where
  /-- The contract-twice vertex composition, with σ = `Perm.starPerm s`. -/
  retargetVertex_eq : ∀ (s : ResolvedCoassocSplitChoice D G) (v : VertexId),
    s.1.1.retargetVertex (D.starOf G s.1.1) v
      = (Perm.starPerm s) ((imageOf s).quotientForest.retargetVertex
          (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
          (rightVertexDomain (imageOf s) v))

/-- **R-6c-heart-6a-6f — the full right final-geometry supply.**  The six named halves of the right
factor's contract-twice geometry. -/
structure ResolvedRightFinalGeometrySupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G) where
  /-- The star bijection (6a-6d-2). -/
  Star : ResolvedRightStarBijectionSupply D G imageOf
  /-- The surviving transport (6a-6d-1). -/
  Surv : ResolvedRightSurvivingSupply D G imageOf
  /-- The star freshness (6a-6b). -/
  Fresh : ResolvedRightStarFreshSupply D G imageOf
  /-- The perm extension (6a-6e). -/
  Perm : ResolvedRightPermExtensionSupply D G imageOf Star Surv Fresh
  /-- The edge-domain connector (6a-6c). -/
  Edge : ResolvedRightEdgeDomainSupply D G imageOf
  /-- The contract-twice vertex composition (6a-6f). -/
  Retarget : ResolvedRightRetargetVertexSupply D G imageOf Star Surv Fresh Perm

/-- **R-6c-heart-6a-6f — the full right `FinalGeometryData` per split choice.**  Wires the six halves. -/
noncomputable def ResolvedRightFinalGeometrySupply.toFinalGeometryData
    (R : ResolvedRightFinalGeometrySupply D G imageOf) (s : ResolvedCoassocSplitChoice D G) :
    ResolvedContractTwiceFinalGeometryData s.1.1 (D.starOf G s.1.1) (imageOf s).quotientForest
      (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest) where
  starMap := R.Star.toStarMapSupply R.Surv R.Fresh s
  permExt := R.Perm.toPermExtension s
  edgeLegVertex := R.Edge.toEdgeLegVertexData s (R.Perm.starPerm s) (R.Retarget.retargetVertex_eq s)

/-- **R-6c-heart-6a-6f — the contract-twice = contract-once supply, fully wired.** -/
noncomputable def ResolvedRightFinalGeometrySupply.toContractTwiceOnceSupply
    (R : ResolvedRightFinalGeometrySupply D G imageOf) :
    ResolvedContractTwiceOnceSupply D G imageOf where
  contract_class_eq := fun s => contract_class_eq_of_classData ((R.toFinalGeometryData s).toRightClassData)

/-- **R-6c-heart-6a-6f — `right_eq` for every split choice, fully wired from the six supplies.** -/
theorem ResolvedRightFinalGeometrySupply.right_eq
    (R : ResolvedRightFinalGeometrySupply D G imageOf)
    (Inner : ResolvedCoassocInnerRightSupply D G) (s : ResolvedCoassocSplitChoice D G) :
    (D.supply G).rightTerm s.1 = Inner.innerRightTerm (imageOf s) :=
  ResolvedContractTwiceOnceSupply.right_eq Inner R.toContractTwiceOnceSupply s

end GaugeGeometry.QFT.Combinatorial
