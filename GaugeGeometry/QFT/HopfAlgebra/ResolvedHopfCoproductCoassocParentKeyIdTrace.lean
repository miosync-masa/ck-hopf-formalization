import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocParentGraphKey

/-!
# R-6c-body-21 — contracted-source id-trace facts ("shape is lost, ids remain")

Twenty-first genuine-body step, making the id-bearing material of body-20's `parentKey` CONCRETE.  Body-20's
scout established that `contractWithStars` loses SHAPE (discards `B.vertices` / `B.internalEdges`, collapses
endpoints inside `B` to stars) but keeps IDS: `retargetEdge` / `retargetExternalLeg` are identity-preserving
(`retarget_edgeId` / `retarget_legId`, both `rfl`).  Here we lift those atomic facts through the `.map` of the
contraction, so the surviving id-multisets are pinned as theorems — the material `(a)` of `parentKey_inj`.

The R-6 philosophy, carved into Lean:

```text
shape は失われるが id は残る  (shape is lost, ids remain)
```

* External legs are ALL retargeted (none dropped), so the full parent leg-id multiset survives:
  `contractedSourceGraph.externalLegs.map legId = γG.externalLegs.map legId`.
* Internal edges keep only the COMPLEMENT (`B`-internal edges gone), so only the complement edge-id multiset
  survives: `contractedSourceGraph.internalEdges.map edgeId = B.complementEdges.map edgeId`.

Each is `body-20 unfolding` + `Multiset.map_map` + `rfl` (the retarget keeps the id field definitionally).

Per the HALT, `parentKey_inj` is NOT proved; the component/id-separation structural fact `(b)` is untouched;
`retarget` is only used through its id-preservation.

Landed:

* `contractedSourceGraph_externalLeg_ids` — the parent leg-id multiset survives intact;
* `contractedSourceGraph_externalLeg_sectors` — likewise the leg sectors (bonus id-adjacent data);
* `contractedSourceGraph_internalEdge_ids` — only the complement edge-id multiset survives.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}
  {s : ResolvedCoassocSplitChoice D G}

/-- **R-6c-body-21 — the parent's external-leg IDS survive the contraction intact** (all legs retargeted, none
dropped; `legId` kept by `retarget`). -/
theorem ResolvedCoassocSplitChoice.ForestChoiceOccurrence.contractedSourceGraph_externalLeg_ids
    (o : s.ForestChoiceOccurrence) :
    o.contractedSourceGraph.externalLegs.map (·.legId) =
      o.γ.1.toResolvedFeynmanGraph.externalLegs.map (·.legId) := by
  rw [o.contractedSourceGraph_externalLegs, Multiset.map_map]; rfl

/-- **R-6c-body-21 — the parent's external-leg SECTORS survive the contraction intact** (`sector` kept by
`retarget`). -/
theorem ResolvedCoassocSplitChoice.ForestChoiceOccurrence.contractedSourceGraph_externalLeg_sectors
    (o : s.ForestChoiceOccurrence) :
    o.contractedSourceGraph.externalLegs.map (·.sector) =
      o.γ.1.toResolvedFeynmanGraph.externalLegs.map (·.sector) := by
  rw [o.contractedSourceGraph_externalLegs, Multiset.map_map]; rfl

/-- **R-6c-body-21 — only the COMPLEMENT internal-edge ids survive** (the `B`-internal edges are discarded;
the surviving complement edges keep `edgeId` through `retarget`). -/
theorem ResolvedCoassocSplitChoice.ForestChoiceOccurrence.contractedSourceGraph_internalEdge_ids
    (o : s.ForestChoiceOccurrence) :
    o.contractedSourceGraph.internalEdges.map (·.edgeId) =
      o.B.1.complementEdges.map (·.edgeId) := by
  rw [o.contractedSourceGraph_internalEdges, Multiset.map_map]; rfl

end GaugeGeometry.QFT.Combinatorial
