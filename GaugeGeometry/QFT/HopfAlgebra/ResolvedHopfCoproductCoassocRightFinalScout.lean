import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocFinalGeometryData

/-!
# R-6c-heart-6a-6a — RIGHT `FinalGeometryData` scout + field-ownership map (read-only)

Before charging into `starPerm` blind, this scout fixes **which existing fact discharges each field** of
`ResolvedContractTwiceFinalGeometryData` for the RIGHT factor, and answers the key structural question:
**is `edge_domain_eq` independent, or does it follow from `quotientForest = Remnant ⊔ Right`?**

## The two routes (confirmed)

* **one-stage** `oneStageContractGraph s = branchRightGraph s = s.1.1.contractWithStars (D.starOf G s.1.1)`
  — the INPUT OUTER forest `A := s.1.1` contracted ONCE in `G`.
* **two-stage** `twoStageContractGraph imageOf s = imageInnerRightGraph imageOf s =
  (imageOf s).quotientForest.contractWithStars (D.starOf QB (imageOf s).quotientForest)`, where the ambient
  `QB := resolvedCoassocQuotientGraph (imageOf s) = (imageOf s).selectedOuter.1.contractWithStars (D.starOf
  G (imageOf s).selectedOuter.1)` — contract `selectedOuter` (stage 1, `G → QB`), then contract
  `quotientForest` (stage 2, in `QB`).  Note `QB = selectedOuterContractGraph s` when `(imageOf
  s).selectedOuter.1 = selectedOuterRawOf s`.

So `FinalGeometryData` is instantiated at `A = s.1.1`, `starA = D.starOf G s.1.1`, `B = quotientForest`,
`starB = D.starOf QB quotientForest`, ambients `GA = G`, `QB = selectedOuter.contractWithStars`.

## Field-ownership map (the deliverable)

`ResolvedContractTwiceFinalGeometryData` decomposes into `starMap` + `permExt` + `edgeLegVertex`.  Per
field, the intended source and the difficulty:

1. **`edgeLegVertex.vertexDomain`** — CONCRETE.  `= selectedOuter.retargetVertex (D.starOf G
   selectedOuter)` (the stage-1 contract map `G → QB`).  Just a definition, no proof.

2. **`edgeLegVertex.leg_domain_eq`** — CHEAP (`≈ rfl`).  Target `G.externalLegs.map (·.retarget
   vertexDomain) = QB.externalLegs`; but `QB.externalLegs = G.externalLegs.map (selectedOuter.
   retargetExternalLeg) = G.externalLegs.map (·.retarget (selectedOuter.retargetVertex))`, and
   `vertexDomain` IS `selectedOuter.retargetVertex` — so the two sides are definitionally the same map.
   Legs are never deleted (all retargeted), so no bookkeeping.

3. **`starMap.freshA`** — D-LEVEL fact.  `s.1.1`'s stars are fresh (outside `G`).  Analogue of the
   heart-3 `ResolvedCoassocSigmaDataSupply.starFreshOf` (which is about `selectedOuter`, not `s.1.1`), so a
   parallel freshness datum for the INPUT outer.

4. **`starMap.freshB`** — D-LEVEL fact.  `quotientForest`'s stars are fresh (outside `QB`) — the quotient
   graph's star assignment freshness.

5. **`starMap.surviving_to` / `surviving_from`** — MEDIUM (vertex set reasoning).  A vertex outside the
   input outer `A` survives both routes: it is outside `selectedOuter` (since `selectedOuter ⊆ A` in vertex
   support, `leftOf ⊆ s.1.1` + promoted), so it survives stage 1 into `QB`; and it is outside
   `quotientForest` (whose vertices are all `A`-derived: stars + right-survivor / remnant vertices).  Needs
   `selectedOuter.vertices ⊆ s.1.1.vertices` and `quotientForest.vertices ⊆ (A-derived)`.

6. **`starMap.starToStar` / `starFromStar` / `star_left_inv` / `star_right_inv`** — BIGGEST / the genuine
   combinatorial heart.  The bijection `A`-component-stars ↔ `quotientForest`-component-stars.  `A`'s
   components are `{left, right-primitive, forest-choice}`; under the two-stage split the left/promoted ones
   are absorbed by `selectedOuter` (stage 1) and the right/remnant ones become `quotientForest` components
   (stage 2 = `Remnant ⊔ Right`).  This is where the `componentPartition` (5b-1) +
   `Right ⊔ Remnant` (5b-4) structure is genuinely USED.

7. **`permExt.starPerm` / `on_vertices` / `inv_on_vertices`** — MECHANICAL.  Extend the finite vertex
   correspondence (`starMap.toVertexCorrespondence`) to a global `Equiv.Perm VertexId`; `on_vertices` ties
   `starPerm` to `corr.invFun` (vertices_eq engine, 6a-5c-3b, already generic).

8. **`edgeLegVertex.retargetVertex_eq`** — GENUINE (depends on `starToStar`).  The contract-twice vertex
   composition `A.retargetVertex starA v = σ (quotientForest.retargetVertex starB (vertexDomain v))`,
   by cases: outside `A` → identity = identity; inside `A` → `A`-star `= σ (quotientForest-star
   (selectedOuter-star))`.  This is what PINS `σ` on stars to `starToStar`.

9. **`edgeLegVertex.edge_domain_eq`** — GENUINE + needs a CONNECTOR (the scout's key answer, below).

## KEY ANSWER — is `edge_domain_eq` free from `quotientForest = Remnant ⊔ Right`?

**No — it is NOT independent and NOT directly given by `quotientForest = Remnant ⊔ Right`.**

`edge_domain_eq : A.complementEdges.map (·.retarget vertexDomain) = quotientForest.complementEdges`, i.e.

  `(G.internalEdges - s.1.1.internalEdges).map (·.retarget selectedOuter.retargetVertex)`
    `= QB.internalEdges - quotientForest.internalEdges`
    `= (selectedOuter.complementEdges.map selectedOuter.retargetEdge) - quotientForest.internalEdges`.

`Multiset.map` does NOT distribute over `-`, so the LHS is not formally a difference of the same shape.
The `Remnant ⊔ Right` decomposition (5b-4) describes `quotientForest`'s COMPONENTS **inside `QB`** — i.e.
it is downstream of the `selectedOuter` retarget and says nothing directly about how `A`'s contracted edges
in `G` split.  What `edge_domain_eq` needs is an EDGE-LEVEL partition back in `G`:

  **`s.1.1.internalEdges = selectedOuter.internalEdges + (the input-outer edges that retarget into
  quotientForest)`**  — i.e. `A`'s contracted edges = stage-1 (selectedOuter) edges ⊔ stage-2
  (quotientForest preimage) edges.

So `edge_domain_eq` should get its OWN connector sub-supply (call it `hQuotEdges` / an edge-partition
datum) rather than being read off `Remnant ⊔ Right`.  The `Remnant ⊔ Right` structure is what makes that
connector PROVABLE (it identifies which `A`-edges land in which quotient component), but the connector is a
distinct, named obligation.

## Difficulty ranking (for sequencing the attack)

CONCRETE/CHEAP: `vertexDomain`, `leg_domain_eq`.
D-LEVEL: `freshA`, `freshB`.
MECHANICAL: `permExt.*` (extend correspondence to perm).
MEDIUM: `surviving_to` / `surviving_from` (vertex containment).
GENUINE: `retargetVertex_eq` (pins `σ` = `starToStar`), `edge_domain_eq` (+ its `hQuotEdges` connector).
BIGGEST: `starToStar` / `starFromStar` + inverse laws (the `A`-component ↔ `quotientForest`-component
bijection — the real coassociativity de-contraction).

## Suggested next steps (NOT done here)

* 6a-6b: nail the CHEAP/CONCRETE pieces — `vertexDomain := selectedOuter.retargetVertex` and
  `leg_domain_eq` (`rfl`) — as a partial `EdgeLegVertexData` builder.
* 6a-6c: the `hQuotEdges` edge-partition connector feeding `edge_domain_eq`.
* 6a-6d: the star bijection `starToStar` from `componentPartition` + `Remnant ⊔ Right`.

This module is documentation only (no declarations) — the scout artifact.  No facade, no flat term, no
`forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

end GaugeGeometry.QFT.Combinatorial
