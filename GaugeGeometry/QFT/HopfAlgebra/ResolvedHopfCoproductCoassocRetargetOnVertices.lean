import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRetargetCompositionLeaf

/-!
# R-6c-leaf-37 — the canonical on-vertices retarget formulation

Thirty-second leaf-body step — a FORMULATION FIX, in the spirit of the 6a-8c-0 mismatch correction.  Leaf-36
found that leaf-21's `rhs_mem` / `retarget_corr` fields (`∀ v`) are too strong: off the vertex set they are
false (`retargetVertex` fixes `v ∉ G.vertices`, which is not a two-stage vertex).  The meaningful, provable
statement is restricted to `v ∈ G.vertices`, with the membership supplied by the proved
`resolved_retarget_rhs_mem` (leaf-36).

This file makes that the canonical form:

* `ResolvedRightRetargetOnVerticesConnector` — `retarget_corr_on_vertices` (the contract-twice composition in
  correspondence coordinates, ON `G.vertices`, using the proved membership);
* `.retargetVertexEq_on_vertices` — the `(Perm s).starPerm`-coordinate equality on `G.vertices`, via
  `VertexPermExtension.on_vertices` + the proved membership.

The full `∀ v` `retargetVertex_eq` (leaf-21 / `ResolvedRightGrandSupply.Retarget`) is then this on-vertices
form PLUS an off-vertex bridge (both sides equal `v`, needing the perm to fix non-vertices) — deferred; the
point here is to attack `retarget_corr` in the correct domain.

Per the HALT, no off-vertex bridge and no three-route `retarget_corr` cases; Perm not constructed.

Landed:

* `ResolvedRightRetargetOnVerticesConnector D G imageOf Three` — `retarget_corr_on_vertices`;
* `.retargetVertexEq_on_vertices` — the `starPerm`-coordinate `retargetVertex_eq` on `G.vertices`.

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

/-- **R-6c-leaf-37 — the canonical on-vertices retarget connector.**  The contract-twice vertex composition in
three-route correspondence coordinates, on `G.vertices` (membership by the proved `resolved_retarget_rhs_mem`). -/
structure ResolvedRightRetargetOnVerticesConnector (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G)
    (Three : ResolvedThreeRouteProvedSupply D G imageOf) where
  /-- The contract-twice composition in correspondence coordinates, restricted to `v ∈ G.vertices`. -/
  retarget_corr_on_vertices : ∀ (s : ResolvedCoassocSplitChoice D G) {v : VertexId} (hv : v ∈ G.vertices),
    s.1.1.retargetVertex (D.starOf G s.1.1) v
      = ((Three.toVertexCorrespondence s).invFun
          ⟨(imageOf s).quotientForest.retargetVertex
              (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
              (rightVertexDomain (imageOf s) v), resolved_retarget_rhs_mem s hv⟩).1

/-- **R-6c-leaf-37 — the `starPerm`-coordinate `retargetVertex_eq` on `G.vertices`.**  `on_vertices` turns the
correspondence's `invFun` into `(Perm s).starPerm` on the two-stage vertex (`resolved_retarget_rhs_mem`). -/
theorem ResolvedRightRetargetOnVerticesConnector.retargetVertexEq_on_vertices
    {Three : ResolvedThreeRouteProvedSupply D G imageOf}
    (Conn : ResolvedRightRetargetOnVerticesConnector D G imageOf Three)
    (Perm : ∀ s, VertexPermExtension (Three.toVertexCorrespondence s))
    (s : ResolvedCoassocSplitChoice D G) {v : VertexId} (hv : v ∈ G.vertices) :
    s.1.1.retargetVertex (D.starOf G s.1.1) v
      = (Perm s).starPerm ((imageOf s).quotientForest.retargetVertex
          (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
          (rightVertexDomain (imageOf s) v)) :=
  (Conn.retarget_corr_on_vertices s hv).trans
    ((Perm s).on_vertices _ (resolved_retarget_rhs_mem s hv)).symm

end GaugeGeometry.QFT.Combinatorial
