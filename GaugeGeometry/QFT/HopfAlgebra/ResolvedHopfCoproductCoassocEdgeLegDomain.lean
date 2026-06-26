import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRetargetComp

/-!
# R-6c-heart-5c-2b-2b — edge/leg field equalities from retarget + domain correspondence

With the retarget composition (5c-2b-2a) in hand, the `internalEdges_eq` / `externalLegs_eq` field
equalities (5c-2b-1) reduce to the **domain correspondence** of the edge/leg multisets before
retargeting:

* **external legs** — `(A.contractWithStars).externalLegs = G.externalLegs.map (retarget)`; both the
  one-step and two-step contractions retarget *all* of `G.externalLegs`, so the leg domain is `G.external
  Legs` on both sides — `externalLegs_eq` follows from `retargetExternalLeg_eq` **alone** (no supply);
* **internal edges** — `(A.contractWithStars).internalEdges = A.complementEdges.map (retarget)`.  Here the
  domains differ: `A.complementEdges` (`G \ A`) vs `B'.complementEdges` (`Q \ B'`).  They correspond
  under the selected-outer retarget — `A.complementEdges.map (A'.retargetEdge starA') = B'.complement
  Edges` — which (the parametric de-contraction edge combinatorics) is isolated as a supply field
  `internalEdges_domain`.

Landed:

* `ResolvedContractTwiceRetargetSupply.externalLegs_eq` — proved from `retargetExternalLeg_eq`;
* `ResolvedContractTwiceEdgeLegSupply` (extends the retarget supply with `internalEdges_domain`);
* `ResolvedContractTwiceEdgeLegSupply.internalEdges_eq` — from `retargetEdge_eq` + `internalEdges_domain`.

No facade, no flat term, no `forgetHopf`.  `vertices_eq` (the star-vertex sets) and the
`internalEdges_domain` discharge are the remaining work.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-5c-2b-2b — the external-legs field equality.**  Both contractions retarget all of
`G.externalLegs`, so `externalLegs_eq` follows from the leg retarget composition alone. -/
theorem ResolvedContractTwiceRetargetSupply.externalLegs_eq
    {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}
    (Ret : ResolvedContractTwiceRetargetSupply D G imageOf)
    (s : ResolvedCoassocSplitChoice D G) :
    (branchRightGraph s).externalLegs
      = ((imageInnerRightGraph imageOf s).mapPerm (Ret.starPerm s)).externalLegs := by
  have hmapPerm : ((imageInnerRightGraph imageOf s).mapPerm (Ret.starPerm s)).externalLegs
      = (imageInnerRightGraph imageOf s).externalLegs.map (ResolvedExternalLeg.map (Ret.starPerm s)) :=
    rfl
  rw [hmapPerm]
  simp only [branchRightGraph, imageInnerRightGraph, resolvedCoassocQuotientGraph,
    ResolvedAdmissibleSubgraph.contractWithStars_externalLegs, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro ℓ _
  exact Ret.retargetExternalLeg_eq s ℓ

/-- **R-6c-heart-5c-2b-2b — the edge/leg supply.**  Extends the retarget composition supply with the one
genuine domain datum for edges: the complement-edge correspondence under the selected-outer retarget. -/
structure ResolvedContractTwiceEdgeLegSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G)
    extends ResolvedContractTwiceRetargetSupply D G imageOf where
  /-- The complement edges of `A`, retargeted through the selected-outer contraction, are the complement
  edges of the quotient subforest `B'` in the quotient graph. -/
  internalEdges_domain : ∀ s : ResolvedCoassocSplitChoice D G,
    s.1.1.complementEdges.map ((imageOf s).selectedOuter.1.retargetEdge
        (D.starOf G (imageOf s).selectedOuter.1))
      = (imageOf s).quotientForest.complementEdges

/-- **R-6c-heart-5c-2b-2b — the internal-edges field equality.**  From the edge retarget composition and
the complement-edge domain correspondence. -/
theorem ResolvedContractTwiceEdgeLegSupply.internalEdges_eq
    {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}
    (EdgeLeg : ResolvedContractTwiceEdgeLegSupply D G imageOf)
    (s : ResolvedCoassocSplitChoice D G) :
    (branchRightGraph s).internalEdges
      = ((imageInnerRightGraph imageOf s).mapPerm (EdgeLeg.starPerm s)).internalEdges := by
  have hmapPerm : ((imageInnerRightGraph imageOf s).mapPerm (EdgeLeg.starPerm s)).internalEdges
      = (imageInnerRightGraph imageOf s).internalEdges.map
          (ResolvedFeynmanEdge.map (EdgeLeg.starPerm s)) := rfl
  rw [hmapPerm, imageInnerRightGraph, ResolvedAdmissibleSubgraph.contractWithStars_internalEdges,
    ← EdgeLeg.internalEdges_domain s, Multiset.map_map, Multiset.map_map,
    branchRightGraph, ResolvedAdmissibleSubgraph.contractWithStars_internalEdges]
  apply Multiset.map_congr rfl
  intro e _
  exact EdgeLeg.toResolvedContractTwiceRetargetSupply.retargetEdge_eq s e

end GaugeGeometry.QFT.Combinatorial
