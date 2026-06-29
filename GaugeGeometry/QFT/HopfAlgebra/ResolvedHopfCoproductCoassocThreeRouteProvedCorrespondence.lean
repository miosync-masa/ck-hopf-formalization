import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocThreeRouteLeftInv
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocThreeRouteRightInv

/-!
# R-6c-heart-6a-8c-fix-3c-5 — the proved three-route correspondence (inverse laws filled)

This completes the corrected three-route vertex correspondence: it fills the `corrLeftInv` / `corrRightInv`
fields of `ResolvedThreeRouteInverseLawSupply` with the PROVED laws (`threeRoute_corrLeftInv` /
`threeRoute_corrRightInv`, fix-3c-2 / fix-3c-4), so `toVertexCorrespondence` is unconditional given only the
route data + the recovery / freshness facts.

`ResolvedThreeRouteProvedSupply` bundles the route data (`ResolvedThreeRouteFullSupply`) with the extra
facts both dispatch laws need — `honeInv` / `htwoInv` / `twoStarVertex` (the recoveries invert
`toStarVertex` and preserve the star vertex) and `freshA` / `freshB`.  It projects to the left/right
dispatch supplies, fills the inverse laws, and assembles the full
`ResolvedContractTwiceVertexCorrespondence` — a PROVED bijection.

Per the HALT, the route fields and the recovery / freshness facts remain supply fields (the genuine
remaining obligations, all free from the concrete recoveries 6a-8b-2 and the canonical fresh-star property
6a-7a); no `Perm` / `Edge` / `retargetVertex_eq`; old star-map chain not deleted.

Landed:

* `ResolvedThreeRouteProvedSupply D G imageOf` — route + `honeInv` / `htwoInv` / `twoStarVertex` /
  `freshA` / `freshB`;
* `.toLeftInvSupply` / `.toRightInvSupply` — the dispatch supplies;
* `.toInverseLawSupply` — the inverse-law supply with the PROVED laws;
* `.toVertexCorrespondence s` — the proved bijection.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **fix-3c-5 — the proved-correspondence supply.**  The route data plus the recovery-inverse / vertex /
freshness facts that the two dispatch laws need. -/
structure ResolvedThreeRouteProvedSupply (D : ResolvedCoproductProperForestData)
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

variable {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}

/-- **fix-3c-5 — the left-inverse dispatch supply. -/
def ResolvedThreeRouteProvedSupply.toLeftInvSupply (S : ResolvedThreeRouteProvedSupply D G imageOf) :
    ResolvedThreeRouteLeftInvSupply D G imageOf where
  toResolvedThreeRouteFullSupply := S.toResolvedThreeRouteFullSupply
  htwoInv := S.htwoInv
  freshA := S.freshA
  freshB := S.freshB

/-- **fix-3c-5 — the right-inverse dispatch supply. -/
def ResolvedThreeRouteProvedSupply.toRightInvSupply (S : ResolvedThreeRouteProvedSupply D G imageOf) :
    ResolvedThreeRouteRightInvSupply D G imageOf where
  toResolvedThreeRouteFullSupply := S.toResolvedThreeRouteFullSupply
  honeInv := S.honeInv
  htwoInv := S.htwoInv
  twoStarVertex := S.twoStarVertex
  freshA := S.freshA
  freshB := S.freshB

/-- **fix-3c-5 — the inverse-law supply with the PROVED inverse laws.** -/
def ResolvedThreeRouteProvedSupply.toInverseLawSupply (S : ResolvedThreeRouteProvedSupply D G imageOf) :
    ResolvedThreeRouteInverseLawSupply D G imageOf where
  route := S.toResolvedThreeRouteFullSupply
  corrLeftInv := threeRoute_corrLeftInv S.toLeftInvSupply
  corrRightInv := threeRoute_corrRightInv S.toRightInvSupply

/-- **fix-3c-5 — the proved vertex correspondence (a bijection, unconditionally). -/
noncomputable def ResolvedThreeRouteProvedSupply.toVertexCorrespondence
    (S : ResolvedThreeRouteProvedSupply D G imageOf) (s : ResolvedCoassocSplitChoice D G) :
    ResolvedContractTwiceVertexCorrespondence (oneStageContractGraph s)
      (twoStageContractGraph imageOf s) :=
  S.toInverseLawSupply.toVertexCorrespondence s

end GaugeGeometry.QFT.Combinatorial
