import GaugeGeometry.QFT.HopfAlgebra.Coassoc
import GaugeGeometry.QFT.Combinatorial.ResolvedFeynmanGraphs

/-!
# Boundary-resolved bridge (Track R-bridge-1, Tier 1)

Thin bridge between the flat Connes–Kreimer development (`Coassoc.lean`) and the
boundary-resolved carrier (`ResolvedFeynmanGraphs.lean`).

The flat coassociativity proof leaves two semantic facades — graph-insertion
uniqueness (`ForestGraphInsertionUniquenessModel`) and promoted external-leg
liftability
(`ForestQuotientForestSigmaForestCoverPromotedExternalLegsLiftableModel`).  Both
are **false on the flat carrier** (multiset-level collapse of structurally
distinct boundary data; explicit counterexamples in `HOPF_DECOMPOSITION.md`).

This file does **not** instantiate those flat facade classes — it cannot, because
they are flat-false and the forgetful map runs resolved → flat.  Instead it
states the *distilled boundary-semantics principles* underlying each facade and
proves them as **theorems on the boundary-resolved carrier**, where the
persistent `edgeId`/`legId` survives contraction and the collapse is impossible.
The forgetful map then recovers the flat carrier (§3), exhibiting the flat
facades as artifacts of the coarser flat notation.

Tier 1 only: no resolved `SubGraph` / `forestSigma` layer (that is `R-4-full`).
-/

namespace GaugeGeometry.QFT.HopfAlgebra

open GaugeGeometry.QFT.Combinatorial

/-! ## 1. Insertion uniqueness, distilled and resolved

The flat `ForestGraphInsertionUniquenessModel` asserts that a forest-choice
parent is determined by its vertices and its post-contraction remnant.  On the
flat carrier this fails: two distinct internal edges with identical
`(source, target, sector)` collapse to the same multiset element.  Its distilled
content — *the retargeted (contracted) internal-edge multiset determines the
pre-contraction internal edges* — is a **theorem** on the resolved carrier. -/
theorem resolved_insertion_internalEdges_unique
    (G : ResolvedFeynmanGraph) (hId : G.EdgeIdsUnique) {f : VertexId → VertexId}
    {M₁ M₂ : Multiset ResolvedFeynmanEdge}
    (hM₁ : M₁ ≤ G.internalEdges) (hM₂ : M₂ ≤ G.internalEdges)
    (h : M₁.map (ResolvedFeynmanEdge.retarget f) =
      M₂.map (ResolvedFeynmanEdge.retarget f)) :
    M₁ = M₂ :=
  G.retargetInternalEdges_injective_on_submultisets hId hM₁ hM₂ h

/-! ## 2. Promoted external-leg liftability, distilled and resolved

The flat `…PromotedExternalLegsLiftableModel` asserts that promoted external legs
of a contracted subgraph lift back consistently.  On the flat carrier this fails:
two legs with identical `(attachedTo, sector)` from different half-edges are
indistinguishable.  Its distilled content — *the retargeted external-leg multiset
determines the pre-contraction legs* — is a **theorem** on the resolved carrier. -/
theorem resolved_promotedExternalLegs_unique
    (G : ResolvedFeynmanGraph) (hId : G.LegIdsUnique) {f : VertexId → VertexId}
    {L₁ L₂ : Multiset ResolvedExternalLeg}
    (hL₁ : L₁ ≤ G.externalLegs) (hL₂ : L₂ ≤ G.externalLegs)
    (h : L₁.map (ResolvedExternalLeg.retarget f) =
      L₂.map (ResolvedExternalLeg.retarget f)) :
    L₁ = L₂ :=
  G.retargetExternalLegs_injective_on_submultisets hId hL₁ hL₂ h

/-! ## 3. Forgetful map recovers the flat carrier

The flat carrier is the forgetful image of the resolved carrier: forgetting the
identity-preserving resolved contraction yields the flat graph with endpoints
rewritten by `f`.  This is the JAR commuting square — the identities `edgeId`/
`legId` that `forget` discards are exactly the data whose loss makes the two flat
facades false. -/
theorem resolved_forget_retargetGraph_commutes
    (G : ResolvedFeynmanGraph) (f : VertexId → VertexId) (V : Finset VertexId) :
    (G.retargetGraph f V).forget =
      { vertices := V
        internalEdges := G.forget.internalEdges.map
          (fun e => { source := f e.source, target := f e.target, sector := e.sector })
        externalLegs := G.forget.externalLegs.map
          (fun ℓ => { attachedTo := f ℓ.attachedTo, sector := ℓ.sector }) } :=
  G.forget_retargetGraph f V

end GaugeGeometry.QFT.HopfAlgebra
