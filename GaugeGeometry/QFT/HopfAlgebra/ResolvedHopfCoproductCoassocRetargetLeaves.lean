import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightThreeRouteProvedGeometry

/-!
# R-6c-leaf-21 — `retargetVertex_eq` in three-route correspondence coordinates

Sixteenth leaf-body discharge — the pre-step into the deepest RIGHT leaf.  The `retargetVertex_eq` field
(`ResolvedRightThreeRouteProvedGeometrySupply` / `ResolvedRightGrandSupply.Retarget`) is stated in the global
`Equiv.Perm` coordinate:

```text
s.1.1.retargetVertex (D.starOf G s.1.1) v = (Perm s).starPerm (RHS_inner s v)
```

`VertexPermExtension.on_vertices` (`starPerm w = (corr.invFun ⟨w, hw⟩).1` for `w ∈ G₂.vertices`) lets the
opaque `(Perm s).starPerm (RHS_inner)` be replaced by the three-route correspondence's `invFun` — the correct
coordinate after the mismatch fix.  So `retargetVertex_eq` reduces to:

* `rhs_mem` — `RHS_inner s v ∈ (twoStageContractGraph imageOf s).vertices` (`= G₂`, where the correspondence
  lands);
* `retarget_corr` — the contract-twice composition *in correspondence coordinates*
  (`… = ((Three.toVertexCorrespondence s).invFun ⟨RHS_inner, rhs_mem⟩).1`).

`RHS_inner s v = (imageOf s).quotientForest.retargetVertex (D.starOf …) (rightVertexDomain (imageOf s) v)` —
the two-stage retarget of the stage-1 image.  Both `G₁ = oneStageContractGraph s = s.1.1.contractWithStars`
and `G₂ = twoStageContractGraph imageOf s = (imageOf s).quotientForest.contractWithStars` (StarGeometry /
RightEq).

Per the HALT, `rhs_mem` / `retarget_corr` are supply fields (the genuine contract-twice vertex geometry);
`Perm` is not constructed; Edge untouched.

Landed:

* `ResolvedRightRetargetConnector D G imageOf Three Perm` — `rhs_mem` + `retarget_corr`;
* `.toRetargetVertexEq` — the `Perm.starPerm`-coordinate `retargetVertex_eq` (via `on_vertices`).

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

/-- **R-6c-leaf-21 — the retarget connector in correspondence coordinates.**  The contract-twice vertex
composition stated via the three-route correspondence's `invFun` (not the global `Equiv.Perm`), plus the
landing membership. -/
structure ResolvedRightRetargetConnector (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G)
    (Three : ResolvedThreeRouteProvedSupply D G imageOf)
    (Perm : ∀ s, VertexPermExtension (Three.toVertexCorrespondence s)) where
  /-- The two-stage retarget of the stage-1 image lands in the two-stage contract graph (`G₂`). -/
  rhs_mem : ∀ (s : ResolvedCoassocSplitChoice D G) (v : VertexId),
    (imageOf s).quotientForest.retargetVertex
        (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
        (rightVertexDomain (imageOf s) v)
      ∈ (twoStageContractGraph imageOf s).vertices
  /-- The contract-twice composition, in three-route correspondence coordinates. -/
  retarget_corr : ∀ (s : ResolvedCoassocSplitChoice D G) (v : VertexId),
    s.1.1.retargetVertex (D.starOf G s.1.1) v
      = ((Three.toVertexCorrespondence s).invFun
          ⟨(imageOf s).quotientForest.retargetVertex
              (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
              (rightVertexDomain (imageOf s) v), rhs_mem s v⟩).1

/-- **R-6c-leaf-21 — the `Perm.starPerm`-coordinate `retargetVertex_eq` from the connector.**  `on_vertices`
turns the correspondence's `invFun` back into `(Perm s).starPerm` on `G₂`'s vertices. -/
theorem ResolvedRightRetargetConnector.toRetargetVertexEq
    {Three : ResolvedThreeRouteProvedSupply D G imageOf}
    {Perm : ∀ s, VertexPermExtension (Three.toVertexCorrespondence s)}
    (Conn : ResolvedRightRetargetConnector D G imageOf Three Perm)
    (s : ResolvedCoassocSplitChoice D G) (v : VertexId) :
    s.1.1.retargetVertex (D.starOf G s.1.1) v
      = (Perm s).starPerm ((imageOf s).quotientForest.retargetVertex
          (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
          (rightVertexDomain (imageOf s) v)) :=
  (Conn.retarget_corr s v).trans ((Perm s).on_vertices _ (Conn.rhs_mem s v)).symm

end GaugeGeometry.QFT.Combinatorial
