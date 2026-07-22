import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaParentPromotedEdge

/-!
# R-6c-body-552 — the canonical `W″` parent is `IsOnePI`; `parentCD ↔ parentDivergent` (PURE ASSEMBLY)

Five-hundred-and-fifty-second genuine-body step, a **pure assembly** — NEW GEOMETRY = ZERO.  Every ingredient is an
already-proved theorem; this file only *wires* them:

* **support-connectivity** — body-549 `canonicalLegSaturated_parent_isConnected` (the `IsOnePI` first conjunct, DEFEQ to
  `.toFeynmanGraph.IsSupportConnected`);
* **per-edge non-bridge** — body-548/549 `legSaturated_parent_edge_cases` dispatches every parent internal edge into the
  Promoted (`(touchedOuterForest …).internalEdges`) or Exact (`quotientEdgePreimage …`) half, then body-551
  `canonicalLegSaturated_parent_erase_promoted_isSupportConnected` / body-550
  `canonicalLegSaturated_parent_erase_exact_isSupportConnected` gives `parent∖e` support-connected — contradicting
  `IsBridge`'s `¬ (erase).IsSupportConnected`.

No `forget` injectivity, no preimage uniqueness: the edge is recovered as a resolved preimage `e = eR.forget`
(`Multiset.mem_map`) and dispatched directly; the erase theorems already speak of `eR.forget`.

## Steps

1–3. `legSaturated_parent_no_bridge` — the only substantive wiring: reduce membership to a resolved preimage, dispatch
     with `legSaturated_parent_edge_cases`, and in each branch refute `IsBridge` via the matching erase-connectivity
     theorem (`IsBridge.not_supportConnected_of_erase`).
4.  **★target★** `canonicalLegSaturated_parent_isOnePI` — `⟨connected (549), non-bridge (this body)⟩`; NO `Parent` input.
5.  `canonicalLegSaturated_parentCD_of_divergent` + `canonicalLegSaturated_parentCD_iff_divergent` — with `parentOnePI`
    now DERIVED, `parentCD ↔ parentDivergent`: the **topology twin of `Parent` is formally ELIMINATED**, and the `Parent`
    aggregate is REDUCED TO `parentDivergent` ONLY.

## Scoreboard

```text
canonicalLegSaturated_parent_isOnePI          PROVED   (NO Parent input)   ⟵ 549 (connected) + 550/551 (non-bridge)
canonicalLegSaturated_parentCD_iff_divergent  PROVED   parentCD ↔ parentDivergent  (topology twin of Parent GONE)
NEW GEOMETRY                                  ZERO     (pure assembly of existing theorems)
```

Next (553): scope audit of `IsDivergenceReflectedByAdmissibleForestContract`'s field type vs canonical innerRaw /
touchedInnerStarTotal / parent self-subgraph / recontract projections / the private flat remainder — an API-visibility
alignment, not new math.

Per the HALT/guards: NO `IsDivergenceReflectedByAdmissibleForestContract`; NO `parentDivergent` proof; NO `Parent`-supply
inhabitant; NO new structure/class/instance; the connected / exact-non-bridge / promoted-non-bridge theorems are APPLIED,
not re-proved; NO `forget` injectivity; no round-trip / coassoc; old private flat theorems untouched; no facade, no
`sorry`/`admit`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-! ## Steps 1–3 — every canonical `W″` parent internal edge is NOT a bridge. -/

/-- **R-6c-body-552 (Steps 1–3) — a parent internal edge is not a bridge, NO `Parent` input.**  Reduce the flat-edge
membership `e ∈ parent.forget.internalEdges` to a resolved preimage `e = eR.forget` (`Multiset.mem_map` after
`toFeynmanGraph_internalEdges` + `forget_internalEdges`), dispatch `eR` with body-549's `legSaturated_parent_edge_cases`
into the Promoted / Exact halves, and in each branch read off `(parent∖eR.forget).IsSupportConnected` (body-551 /
body-550) to REFUTE `IsBridge`'s `¬ (erase).IsSupportConnected`.  ★NO `forget` injectivity — the erase theorems already
speak of `eR.forget`.★ -/
theorem legSaturated_parent_no_bridge {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalLegSaturatedCarrierProperSupply.toData G)
    (δ : {x : ResolvedFeynmanSubgraph
        (z.1.1.contractWithStars (canonicalLegSaturatedCarrierProperSupply.toData.starOf G z.1.1)) //
          x ∈ forestDomain z})
    {e : FeynmanEdge}
    (he : e ∈ (canonicalLegSaturatedParentForget z δ).toFeynmanGraph.internalEdges) :
    ¬ (canonicalLegSaturatedParentForget z δ).toFeynmanGraph.IsBridge e := by
  classical
  -- Reduce the flat-edge membership to a resolved preimage `e = eR.forget`.
  simp only [canonicalLegSaturatedParentForget, FeynmanSubgraph.toFeynmanGraph_internalEdges,
    ResolvedFeynmanSubgraph.forget_internalEdges] at he
  obtain ⟨eR, heR, rfl⟩ := Multiset.mem_map.mp he
  -- Dispatch `eR` into the Promoted / Exact halves (body-549 edge cases).
  rcases legSaturated_parent_edge_cases z δ.1
      (touchedLegLiftDatum_of_complete z δ.1 (canonicalLegSaturated_touchedLegComplete z δ))
      (liveAmbient_edges_supported ambientSupportOfW'' z)
      (liveAmbient_legs_supported ambientSupportOfW'' z) heR with hProm | hExact
  · -- Promoted edge (body-551): `parent∖eR.forget` support-connected ⟹ not a bridge.
    have hEC := canonicalLegSaturated_parent_erase_promoted_isSupportConnected z δ hProm
    intro hBridge
    exact hBridge.not_supportConnected_of_erase hEC
  · -- Exact edge (body-550): `parent∖eR.forget` support-connected ⟹ not a bridge.
    have hEC := canonicalLegSaturated_parent_erase_exact_isSupportConnected z δ hExact
    intro hBridge
    exact hBridge.not_supportConnected_of_erase hEC

/-! ## Step 4 — ★target★ the canonical `W″` parent is `IsOnePI`. -/

/-- **R-6c-body-552 ∎ (★target★) — the canonical `W″` parent is `IsOnePI`, NO `Parent` input.**  Pure assembly:
support-connectivity DERIVED from body-549 (`canonicalLegSaturated_parent_isConnected`, DEFEQ to the first `IsOnePI`
conjunct `.toFeynmanGraph.IsSupportConnected`) and bridge-freeness DERIVED from Steps 1–3 (per-edge, dispatched by
body-549 edge cases into body-550/551).  ⟹ `parentOnePI` is now DERIVED, never a `Parent` field. -/
theorem canonicalLegSaturated_parent_isOnePI {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalLegSaturatedCarrierProperSupply.toData G)
    (δ : {x : ResolvedFeynmanSubgraph
        (z.1.1.contractWithStars (canonicalLegSaturatedCarrierProperSupply.toData.starOf G z.1.1)) //
          x ∈ forestDomain z}) :
    (canonicalLegSaturatedParentForget z δ).IsOnePI := by
  refine ⟨?_, ?_⟩
  · exact canonicalLegSaturated_parent_isConnected z δ
  · exact fun e he => legSaturated_parent_no_bridge z δ he

/-! ## Step 5 — reduce `Parent` to `parentDivergent` only. -/

/-- **R-6c-body-552 — `parentCD` from `parentDivergent` alone** (the `parentOnePI` half is now DERIVED, body-552).
Feeds `canonicalLegSaturated_parent_isOnePI` into body-548's `canonicalLegSaturated_parentCD_of_onePI_divergent`. -/
theorem canonicalLegSaturated_parentCD_of_divergent {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalLegSaturatedCarrierProperSupply.toData G)
    (δ : {x : ResolvedFeynmanSubgraph
        (z.1.1.contractWithStars (canonicalLegSaturatedCarrierProperSupply.toData.starOf G z.1.1)) //
          x ∈ forestDomain z})
    (hDiv : (canonicalLegSaturatedParentForget z δ).IsDivergent) :
    (canonicalLegSaturatedParentForget z δ).IsConnectedDivergent :=
  canonicalLegSaturated_parentCD_of_onePI_divergent z δ (canonicalLegSaturated_parent_isOnePI z δ) hDiv

/-- **R-6c-body-552 ∎ — `parentCD ↔ parentDivergent`.**  The topology twin (`parentOnePI`, hence support-connected +
bridge-free) of the `Parent` aggregate is formally ELIMINATED: `Parent`'s connected-divergence datum is now equivalent to
plain divergence of the `W″` parent.  Forward is body-548's projection; backward is Step 5's assembly. -/
theorem canonicalLegSaturated_parentCD_iff_divergent {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalLegSaturatedCarrierProperSupply.toData G)
    (δ : {x : ResolvedFeynmanSubgraph
        (z.1.1.contractWithStars (canonicalLegSaturatedCarrierProperSupply.toData.starOf G z.1.1)) //
          x ∈ forestDomain z}) :
    (canonicalLegSaturatedParentForget z δ).IsConnectedDivergent ↔
      (canonicalLegSaturatedParentForget z δ).IsDivergent :=
  ⟨canonicalLegSaturated_parentDivergent_of_cd z δ, canonicalLegSaturated_parentCD_of_divergent z δ⟩

end GaugeGeometry.QFT.Combinatorial
