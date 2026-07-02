import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightEdgeConnector
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightCheapGeometry

/-!
# R-6c-leaf-16 — RIGHT `edge_domain_eq` reduced to an edge-partition connector

Twelfth leaf-body discharge (RIGHT side).  `ResolvedRightEdgeDomainSupply.edge_domain_eq` (6a-6c) is the
stage-1 edge bookkeeping:

```text
s.1.1.complementEdges.map (·.retarget (rightVertexDomain (imageOf s))) = (imageOf s).quotientForest.complementEdges
```

The RHS `quotientForest.complementEdges` is a *cross-graph* multiset subtraction
(`(resolvedCoassocQuotientGraph (imageOf s)).internalEdges - quotientForest.internalEdges`); unfolding the
quotient graph's internal edges via `contractWithStars_internalEdges` (`= selectedOuter.complementEdges.map
(selectedOuter.retargetEdge starOf)`, and `selectedOuter.retargetEdge starOf = ·.retarget (rightVertexDomain
(imageOf s))` definitionally) turns `edge_domain_eq` into the *same-map* multiset equation

```text
s.1.1.complementEdges.map f = (selectedOuter.complementEdges.map f) - quotientForest.internalEdges
```

which is the genuine input-outer-vs-selected-outer edge partition — isolated here as the connector field.

Per the HALT, the edge partition itself is a supply field (genuine two-stage de-contraction edge geometry);
`retargetVertex_eq` / Sector maps untouched.

Landed:

* `edge_domain_eq_of_partition` — `edge_domain_eq` from the same-map partition;
* `ResolvedRightEdgePartitionSupply D G imageOf` + `.toRightEdgeDomainSupply`.

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

/-- **R-6c-leaf-16 — `edge_domain_eq` from the same-map edge partition.**  Unfolding the quotient graph's
internal edges (via `contractWithStars_internalEdges`) reduces the cross-graph `complementEdges` on the RHS to
the selected-outer complement's retarget, matching the partition's RHS. -/
theorem edge_domain_eq_of_partition (s : ResolvedCoassocSplitChoice D G)
    (edge_partition :
      s.1.1.complementEdges.map (fun e => e.retarget (rightVertexDomain (imageOf s)))
        = ((imageOf s).selectedOuter.1.complementEdges.map
            (fun e => e.retarget (rightVertexDomain (imageOf s))))
          - (imageOf s).quotientForest.internalEdges) :
    s.1.1.complementEdges.map (fun e => e.retarget (rightVertexDomain (imageOf s)))
      = (imageOf s).quotientForest.complementEdges := by
  rw [edge_partition]
  simp only [ResolvedAdmissibleSubgraph.complementEdges,
    ResolvedAdmissibleSubgraph.contractWithStars_internalEdges, rightVertexDomain,
    ResolvedAdmissibleSubgraph.retargetEdge]

/-- **R-6c-leaf-16 — the RIGHT edge-partition supply.**  The input-outer-vs-selected-outer complement edge
partition (same-map form) — the genuine stage-1 edge geometry. -/
structure ResolvedRightEdgePartitionSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G) where
  /-- The input-outer complement retargets to the selected-outer complement retarget minus the quotient
  forest's internal edges. -/
  edge_partition : ∀ s : ResolvedCoassocSplitChoice D G,
    s.1.1.complementEdges.map (fun e => e.retarget (rightVertexDomain (imageOf s)))
      = ((imageOf s).selectedOuter.1.complementEdges.map
          (fun e => e.retarget (rightVertexDomain (imageOf s))))
        - (imageOf s).quotientForest.internalEdges

/-- **R-6c-leaf-16 — the RIGHT edge-domain supply from the edge partition. -/
def ResolvedRightEdgePartitionSupply.toRightEdgeDomainSupply
    (E : ResolvedRightEdgePartitionSupply D G imageOf) : ResolvedRightEdgeDomainSupply D G imageOf where
  edge_domain_eq := fun s => edge_domain_eq_of_partition s (E.edge_partition s)

end GaugeGeometry.QFT.Combinatorial
