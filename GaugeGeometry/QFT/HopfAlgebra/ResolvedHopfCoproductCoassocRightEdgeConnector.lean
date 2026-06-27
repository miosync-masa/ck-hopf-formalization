import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightCheapGeometry

/-!
# R-6c-heart-6a-6c — RIGHT edge-domain connector (`hQuotEdges`)

The 6a-6a scout found `edge_domain_eq` is NOT free from `quotientForest = Remnant ⊔ Right` (that lives in
the quotient graph, downstream of the `selectedOuter` retarget; `Multiset.map` does not distribute over
`-`).  It needs its own edge-level partition back in `G`:

  **`s.1.1.internalEdges` (input outer `A`'s contracted edges)
     `= selectedOuter.internalEdges` (stage-1) `+` (the input-outer edges that retarget into the quotient
     forest, stage-2)**

Rather than prove that here, this file gives `edge_domain_eq` its own **named hole** in exactly the shape
`ResolvedContractTwiceEdgeLegVertexData` wants, and an adapter that — together with the cheap
`rightVertexDomain` / `right_leg_domain_eq` (6a-6b) — leaves only `retargetVertex_eq` (and `σ`) as the
remaining genuine `EdgeLegVertexData` input.

So after this, building the right-factor `EdgeLegVertexData` needs only:
`ResolvedRightEdgeDomainSupply` (this hole) + `σ` + `retargetVertex_eq`.  The heavy edge split is isolated
as the single field `edge_domain_eq`.

Per the HALT, `edge_domain_eq` is NOT proved, no `Remnant ⊔ Right` derivation, no `starToStar`.

Landed:

* `ResolvedRightEdgeDomainSupply D G imageOf` — the `edge_domain_eq` hole (per split choice), in
  `EdgeLegVertexData` shape;
* `.toEdgeLegVertexData` — the adapter consuming the hole + the 6a-6b cheap pieces, parameterised by the
  remaining genuine `σ` / `retargetVertex_eq`.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-6a-6c — the right edge-domain connector (`hQuotEdges`).**  The single named hole feeding
`EdgeLegVertexData.edge_domain_eq` for the right factor: the input outer's complement edges, retargeted
through `rightVertexDomain`, equal the quotient forest's complement edges.  Morally this encodes the edge
partition `s.1.1.internalEdges = selectedOuter.internalEdges + (quotient-forest preimage)`. -/
structure ResolvedRightEdgeDomainSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G) where
  /-- `A.complementEdges` retargeted through `rightVertexDomain` = `quotientForest.complementEdges`. -/
  edge_domain_eq : ∀ s : ResolvedCoassocSplitChoice D G,
    s.1.1.complementEdges.map (fun e => e.retarget (rightVertexDomain (imageOf s)))
      = (imageOf s).quotientForest.complementEdges

/-- **R-6c-heart-6a-6c — the right `EdgeLegVertexData` from the edge connector + cheap pieces.**  Consumes
the `edge_domain_eq` hole (this supply), `rightVertexDomain` / `right_leg_domain_eq` (6a-6b), and leaves
the genuine `σ` and `retargetVertex_eq` as the only remaining input. -/
noncomputable def ResolvedRightEdgeDomainSupply.toEdgeLegVertexData
    {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}
    (E : ResolvedRightEdgeDomainSupply D G imageOf) (s : ResolvedCoassocSplitChoice D G)
    (σ : Equiv.Perm VertexId)
    (hretarget : ∀ v, s.1.1.retargetVertex (D.starOf G s.1.1) v
      = σ ((imageOf s).quotientForest.retargetVertex
          (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
          (rightVertexDomain (imageOf s) v))) :
    ResolvedContractTwiceEdgeLegVertexData s.1.1 (D.starOf G s.1.1)
      (imageOf s).quotientForest
      (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest) σ where
  vertexDomain := rightVertexDomain (imageOf s)
  retargetVertex_eq := hretarget
  edge_domain_eq := E.edge_domain_eq s
  leg_domain_eq := right_leg_domain_eq (imageOf s)

end GaugeGeometry.QFT.Combinatorial
