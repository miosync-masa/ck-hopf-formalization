import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocVertexSetEq

/-!
# R-6c-heart-6a-5c-3c — edge/leg field equalities from retarget + domain (generic)

`vertices_eq` is generic (6a-5c-3b).  This file does the same for `internalEdges_eq` / `externalLegs_eq`:
they follow **generically** from the **edge/leg retarget composition** (the one-stage retarget of an
edge/leg is the two-stage retarget relabeled by `σ`) plus the **edge/leg domain correspondence** (the
one-stage complement edges / external legs map onto the two-stage ones).  This is the generic version of
the right-`eq` route (5c-2b-2b), now reusable for both `right_eq` and the remnant.

So once the perm extension is in hand, the whole `ResolvedContractTwiceFieldEqSupply` is built from the
**retarget/domain data** (which is itself dischargeable from `retargetVertex_eq`, 5c-2b-2a, and the
complement domain).

Per the HALT, the retarget equalities and the domain correspondences are **supply fields** — only the
field-equality derivation is proved.

Landed:

* `ResolvedContractTwiceEdgeLegData A starA B starB σ` — the edge/leg retarget composition + domain
  correspondences (supply fields);
* `.internalEdges_eq` / `.externalLegs_eq` — the two field equalities, derived;
* `ResolvedContractTwiceFieldEqSupply.ofEdgeLegData` — the full field-equality supply (vertices auto,
  edge/leg from the data).

No facade, no flat term, no `forgetHopf`.  The retarget/domain data, the star bijection, and the perm
extension are the remaining work.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {GA QB : ResolvedFeynmanGraph}

/-- **R-6c-heart-6a-5c-3c — the edge/leg retarget + domain data.**  The edge/leg retarget composition
(one-stage retarget = `σ ∘` two-stage retarget `∘` domain) and the complement-edge / external-leg domain
correspondences between the one-stage and two-stage contractions. -/
structure ResolvedContractTwiceEdgeLegData
    (A : ResolvedAdmissibleSubgraph GA) (starA : ResolvedFeynmanSubgraph GA → VertexId)
    (B : ResolvedAdmissibleSubgraph QB) (starB : ResolvedFeynmanSubgraph QB → VertexId)
    (σ : Equiv.Perm VertexId) where
  /-- The complement-edge domain map (one-stage complement edge ↦ two-stage complement edge). -/
  edgeDomain : ResolvedFeynmanEdge → ResolvedFeynmanEdge
  /-- The one-stage complement edges map onto the two-stage complement edges. -/
  edge_domain_eq : A.complementEdges.map edgeDomain = B.complementEdges
  /-- The edge retarget composition. -/
  retargetEdge_eq : ∀ e, A.retargetEdge starA e
    = ResolvedFeynmanEdge.map σ (B.retargetEdge starB (edgeDomain e))
  /-- The external-leg domain map (one-stage leg ↦ two-stage leg). -/
  legDomain : ResolvedExternalLeg → ResolvedExternalLeg
  /-- The one-stage external legs map onto the two-stage external legs. -/
  leg_domain_eq : GA.externalLegs.map legDomain = QB.externalLegs
  /-- The leg retarget composition. -/
  retargetLeg_eq : ∀ ℓ, A.retargetExternalLeg starA ℓ
    = ResolvedExternalLeg.map σ (B.retargetExternalLeg starB (legDomain ℓ))

variable {A : ResolvedAdmissibleSubgraph GA} {starA : ResolvedFeynmanSubgraph GA → VertexId}
  {B : ResolvedAdmissibleSubgraph QB} {starB : ResolvedFeynmanSubgraph QB → VertexId}
  {σ : Equiv.Perm VertexId}

/-- **R-6c-heart-6a-5c-3c — the internal-edges field equality.**  From the edge retarget composition and
the complement-edge domain correspondence. -/
theorem ResolvedContractTwiceEdgeLegData.internalEdges_eq
    (M : ResolvedContractTwiceEdgeLegData A starA B starB σ) :
    (A.contractWithStars starA).internalEdges
      = ((B.contractWithStars starB).mapPerm σ).internalEdges := by
  have hmapPerm : ((B.contractWithStars starB).mapPerm σ).internalEdges
      = (B.contractWithStars starB).internalEdges.map (ResolvedFeynmanEdge.map σ) := rfl
  rw [hmapPerm, ResolvedAdmissibleSubgraph.contractWithStars_internalEdges B starB,
    ← M.edge_domain_eq, Multiset.map_map, Multiset.map_map,
    ResolvedAdmissibleSubgraph.contractWithStars_internalEdges A starA]
  apply Multiset.map_congr rfl
  intro e _
  exact M.retargetEdge_eq e

/-- **R-6c-heart-6a-5c-3c — the external-legs field equality.**  From the leg retarget composition and the
external-leg domain correspondence. -/
theorem ResolvedContractTwiceEdgeLegData.externalLegs_eq
    (M : ResolvedContractTwiceEdgeLegData A starA B starB σ) :
    (A.contractWithStars starA).externalLegs
      = ((B.contractWithStars starB).mapPerm σ).externalLegs := by
  have hmapPerm : ((B.contractWithStars starB).mapPerm σ).externalLegs
      = (B.contractWithStars starB).externalLegs.map (ResolvedExternalLeg.map σ) := rfl
  rw [hmapPerm, ResolvedAdmissibleSubgraph.contractWithStars_externalLegs B starB,
    ← M.leg_domain_eq, Multiset.map_map, Multiset.map_map,
    ResolvedAdmissibleSubgraph.contractWithStars_externalLegs A starA]
  apply Multiset.map_congr rfl
  intro ℓ _
  exact M.retargetLeg_eq ℓ

/-- **R-6c-heart-6a-5c-3c — the full field-equality supply from the retarget/domain data.**  `vertices_eq`
auto-filled (6a-5c-3b), `internalEdges_eq` / `externalLegs_eq` from the edge/leg data. -/
def ResolvedContractTwiceFieldEqSupply.ofEdgeLegData
    {corr : ResolvedContractTwiceVertexCorrespondence (A.contractWithStars starA)
      (B.contractWithStars starB)} (E : VertexPermExtension corr)
    (M : ResolvedContractTwiceEdgeLegData A starA B starB E.starPerm) :
    ResolvedContractTwiceFieldEqSupply E where
  vertices_eq := vertices_eq_of_perm_extension E
  internalEdges_eq := M.internalEdges_eq
  externalLegs_eq := M.externalLegs_eq

end GaugeGeometry.QFT.Combinatorial
