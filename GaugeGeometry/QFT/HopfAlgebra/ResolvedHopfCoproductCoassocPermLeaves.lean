import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightThreeRouteProvedGeometry

/-!
# R-6c-leaf-22 — the Perm leaf isolated for the three-route correspondence

Seventeenth leaf-body discharge — isolating the only remaining *nonlocal* nuisance: extending a finite vertex
correspondence to a global `VertexId` permutation.

`VertexPermExtension corr` (VertexPermExtend:44) is ALREADY the generic standalone "extend a correspondence to
a global permutation" structure — `starPerm : Equiv.Perm VertexId` + `on_vertices` (`starPerm w = corr.invFun w`
on `G₂`) + `inv_on_vertices` (`starPerm.symm v = corr.toFun v` on `G₁`).  So no new generic structure is
needed; the earlier `ResolvedRightPermExtensionSupply` / `ResolvedRightPermConnector` (6a-6e / RightPermConcrete)
build it over the OLD star-map correspondence, whereas the current geometry (leaf-21 retarget, `ResolvedRightGrandSupply.Perm`)
needs it over the THREE-ROUTE proved correspondence `Three.toVertexCorrespondence s`.

This file names that obligation as one supply and adapts it — the single global-permutation leaf, in the
correct post-mismatch frame.  Its `.toPerm` feeds both `ResolvedRightGrandSupply.Perm` and the leaf-21
`ResolvedRightRetargetConnector`'s `Perm` parameter.

Per the HALT, no `Equiv.Perm` is constructed (the finite-to-global extension stays a supply field); Retarget /
Edge untouched.

Landed:

* `ResolvedRightPermLeafSupply D G imageOf Three` — `permExt` (the per-split-choice extension);
* `.toPerm` — the `∀ s, VertexPermExtension (Three.toVertexCorrespondence s)` the grand record needs.

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

/-- **R-6c-leaf-22 — the Perm leaf for the three-route correspondence.**  The per-split-choice extension of
`Three.toVertexCorrespondence s` to a global `VertexId` permutation. -/
structure ResolvedRightPermLeafSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G)
    (Three : ResolvedThreeRouteProvedSupply D G imageOf) where
  /-- The global-permutation extension of the three-route correspondence at each split choice. -/
  permExt : ∀ s : ResolvedCoassocSplitChoice D G,
    VertexPermExtension (Three.toVertexCorrespondence s)

/-- **R-6c-leaf-22 — the `Perm` the grand record / retarget connector need. -/
def ResolvedRightPermLeafSupply.toPerm
    {Three : ResolvedThreeRouteProvedSupply D G imageOf}
    (P : ResolvedRightPermLeafSupply D G imageOf Three) :
    ∀ s : ResolvedCoassocSplitChoice D G, VertexPermExtension (Three.toVertexCorrespondence s) :=
  P.permExt

end GaugeGeometry.QFT.Combinatorial
