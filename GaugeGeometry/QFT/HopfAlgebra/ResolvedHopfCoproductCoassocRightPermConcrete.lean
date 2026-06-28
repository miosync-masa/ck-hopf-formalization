import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightPermExtension

/-!
# R-6c-heart-6a-7c — RIGHT perm extension as a single "extends-correspondence" connector

`ResolvedRightPermExtensionSupply` (6a-6e) carries `starPerm` plus `on_vertices` / `inv_on_vertices`.  This
file re-packages it into the more natural **"a global permutation extends the vertex correspondence"**
shape — `starPerm` together with `extends_toFun` (on the one-stage vertices, `starPerm.symm` is the forward
correspondence) and `extends_invFun` (on the two-stage vertices, `starPerm` is the inverse correspondence)
— which is the form the eventual extension proof (extending a partial bijection on a finite vertex set to
a full `Equiv.Perm VertexId`) lands in.

This is a faithful re-phrasing (vertex argument implicit, named for the extension direction); the adapter
to `ResolvedRightPermExtensionSupply` is definitional.

Per the HALT, `starPerm` is NOT constructed, the extension is NOT proved, no `starToStar`.

Landed:

* `ResolvedRightPermConnector D G imageOf Star Surv Fresh` — `starPerm` + `extends_toFun` /
  `extends_invFun`;
* `.toRightPermExtensionSupply` — back to `ResolvedRightPermExtensionSupply` (definitional).

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

/-- **R-6c-heart-6a-7c — the right perm-extension connector.**  A global `Equiv.Perm VertexId` (per split
choice) that extends the contract-twice vertex correspondence: on the one-stage vertices `starPerm.symm` is
the forward map, on the two-stage vertices `starPerm` is the inverse map. -/
structure ResolvedRightPermConnector (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G)
    (Star : ResolvedRightStarBijectionSupply D G imageOf)
    (Surv : ResolvedRightSurvivingSupply D G imageOf)
    (Fresh : ResolvedRightStarFreshSupply D G imageOf) where
  /-- The full-`VertexId` permutation extending the correspondence (per split choice). -/
  starPerm : ∀ s : ResolvedCoassocSplitChoice D G, Equiv.Perm VertexId
  /-- On the one-stage vertices, `starPerm.symm` is the forward correspondence. -/
  extends_toFun : ∀ (s : ResolvedCoassocSplitChoice D G) {v : VertexId}
    (hv : v ∈ (oneStageContractGraph s).vertices),
    (starPerm s).symm v = (((Star.toStarMapSupply Surv Fresh s).toVertexCorrespondence).toFun ⟨v, hv⟩).1
  /-- On the two-stage vertices, `starPerm` is the inverse correspondence. -/
  extends_invFun : ∀ (s : ResolvedCoassocSplitChoice D G) {v : VertexId}
    (hv : v ∈ (twoStageContractGraph imageOf s).vertices),
    (starPerm s) v = (((Star.toStarMapSupply Surv Fresh s).toVertexCorrespondence).invFun ⟨v, hv⟩).1

/-- **R-6c-heart-6a-7c — back to the perm-extension supply (definitional).** -/
def ResolvedRightPermConnector.toRightPermExtensionSupply
    {Star : ResolvedRightStarBijectionSupply D G imageOf}
    {Surv : ResolvedRightSurvivingSupply D G imageOf}
    {Fresh : ResolvedRightStarFreshSupply D G imageOf}
    (P : ResolvedRightPermConnector D G imageOf Star Surv Fresh) :
    ResolvedRightPermExtensionSupply D G imageOf Star Surv Fresh where
  starPerm := P.starPerm
  on_vertices := fun s w hw => P.extends_invFun s hw
  inv_on_vertices := fun s v hv => P.extends_toFun s hv

end GaugeGeometry.QFT.Combinatorial
