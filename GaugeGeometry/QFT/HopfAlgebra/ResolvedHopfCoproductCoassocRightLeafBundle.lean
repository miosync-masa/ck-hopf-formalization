import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightGrandSupply

/-!
# R-6c-leaf-6 — RIGHT leaf bundle (`right_eq` from ONE flat bundle)

Mirror of the Product leaf bundle (leaf-5) for the RIGHT half of `term_eq`.  The eight RIGHT dependencies —
`Codomain` / `Sector` / `Transport` / `Mechanical` / `Partition` / `Perm` / `Edge` / `Retarget` — are
collected into ONE flat record and flow into `ResolvedRightGrandSupply` → `right_eq`.

`ResolvedRightGrandSupply` was split (6a-11a) into `Data` (the five quotient-star + route supplies) and the
grand (whose `Perm` type references `Data.toProvedSupply.toVertexCorrespondence`).  The flat bundle inlines
that `Data` in the `Perm` / `Retarget` field types (later fields depend on earlier ones), so `toRightGrandSupply`
is a pure re-packaging.

Per the HALT, no leaf fields are proved; Transport / Sector are not reduced.

Landed:

* `ResolvedRightLeafBundle D G imageOf` — the eight RIGHT dependencies, flat;
* `.toRightGrandSupply : ResolvedRightGrandSupply D G imageOf`;
* `.right_eq` — the RIGHT factor `right_eq` from the bundle.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-leaf-6 — the RIGHT leaf bundle.**  The eight RIGHT dependencies, flat.  The `Perm` / `Retarget`
field types inline the `Data` record built from the first five fields. -/
structure ResolvedRightLeafBundle (D : ResolvedCoproductProperForestData)
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
  /-- The perm extension over the proved correspondence. -/
  Perm : ∀ s : ResolvedCoassocSplitChoice D G,
    VertexPermExtension
      (({ Codomain := Codomain, Sector := Sector, Transport := Transport,
          Mechanical := Mechanical, Partition := Partition } :
          ResolvedRightQuotientStarDataSupply D G imageOf).toProvedSupply.toVertexCorrespondence s)
  /-- The edge-domain connector (6a-6c). -/
  Edge : ResolvedRightEdgeDomainSupply D G imageOf
  /-- The contract-twice vertex composition, σ = `(Perm s).starPerm`. -/
  Retarget : ∀ (s : ResolvedCoassocSplitChoice D G) (v : VertexId),
    s.1.1.retargetVertex (D.starOf G s.1.1) v
      = (Perm s).starPerm ((imageOf s).quotientForest.retargetVertex
          (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
          (rightVertexDomain (imageOf s) v))

/-- **R-6c-leaf-6 — the RIGHT grand supply from the flat bundle. -/
noncomputable def ResolvedRightLeafBundle.toRightGrandSupply
    {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}
    (B : ResolvedRightLeafBundle D G imageOf) : ResolvedRightGrandSupply D G imageOf where
  Data := { Codomain := B.Codomain, Sector := B.Sector, Transport := B.Transport,
            Mechanical := B.Mechanical, Partition := B.Partition }
  Perm := B.Perm
  Edge := B.Edge
  Retarget := B.Retarget

/-- **R-6c-leaf-6 — the RIGHT factor `right_eq` from the flat bundle. -/
theorem ResolvedRightLeafBundle.right_eq
    {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}
    (B : ResolvedRightLeafBundle D G imageOf) (Inner : ResolvedCoassocInnerRightSupply D G)
    (s : ResolvedCoassocSplitChoice D G) :
    (D.supply G).rightTerm s.1 = Inner.innerRightTerm (imageOf s) :=
  B.toRightGrandSupply.right_eq Inner s

end GaugeGeometry.QFT.Combinatorial
