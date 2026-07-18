import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocParentRemnantSectionValue

/-!
# R-6c-body-382 — bank-3b audit: the parent-section internal-edges projection is a THEOREM (verdict)

Three-hundred-and-eighty-second genuine-body step — the internal-edges projection audit of body-381's
`parent_remnantComponent_of_data`.  Per the plan, `internalEdges` is audited BEFORE `vertices` (which consumes
edge/leg coverage) and `externalLegs` (likely the last, a choice-coherence).

## Verdict (edge-id uniqueness → THEOREM, not an honest datum)

`ResolvedAdmissibleSubgraph.retargetEdge` / `retargetExternalLeg` KEEP the edge/leg ids and are **injective on the
residual edges** (`ResolvedActualSigmaCover`, near line 734), and the quotient-edge-preimage's uniqueness is banked as
`retarget_residual_edges_injective` (near line 768) — `quotientEdgePreimage`'s `_map` (`.map retargetEdge =
δ.internalEdges`) is therefore its UNIQUE solution.  So the internal-edge preimage is pinned by edge ids, and the
`internalEdges` projection of `Core.parent (remnantComponent o) = o.γ.1` is a **THEOREM**, NOT an `occurrence_edgeLift`
honest datum.

## The shared core (proof-shape, for the follow-up body)

The one theorem the internal-edge (and, later, the vertex) projection routes through, proved from the RAW forward
definitions alone — NO parent equality, NO `hparent`, NO `OccInv`, NO body-341 `houter`, NO forest bridge:

```text
touchedOuterComponents_of_occurrence :
  HEq (V.Remnant.remnant.remnantComponent o) δ.1 →
    touchedOuterComponents (fwdMapFilteredValue F V q) δ = (ResolvedAdmissibleSubgraph.promote o.γ.1 o.B.1).elements
```

`fwd q`'s outer is `selectedOuterRawOf q`; `remnantComponent o` is `o.γ.1` contracted by `o.B.1` (`contractedSourceGraph`
re-embedded); star freshness / injectivity (`ResolvedCanonicalStarFacts`) limits the components whose star lands in
`δ = remnantComponent o` to exactly `o.γ.1`'s `o.B.1`-promoted collection.  From it:

```text
(touchedOuterForest (fwd q) δ).internalEdges = o.B.1.internalEdges          (promote data + sum-image)
Core.parent.internalEdges = touchedOuterForest.internalEdges + quotientEdgePreimage
                          = o.B.1.internalEdges + quotientEdgePreimage
quotientEdgePreimage = o.γ.1.internalEdges - o.B.1.internalEdges            (edge-id uniqueness + `hδ` + `_map`)
⇒ Core.parent.internalEdges = o.γ.1.internalEdges
```

## Anticipated final shape (recorded, not pre-empted)

`touched collection alignment` — theorem; `internalEdges` — theorem (this verdict); `externalLegs` — occurrence-specific
lift datum (TBC only after it is discharged); `vertices` — theorem from the exact edge/leg data + connected coverage.

Per the HALT: only the internal-edges VERDICT + the shared-core proof-shape are recorded; NO projection is proved here
(the deep `touchedOuterComponents_of_occurrence` is the follow-up body); the cycle guards stand (`hparent` / `OccInv` /
`houter` / forest bridge / `forestSource` unused).  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO
`promote_collapse` / singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

-- Audit anchor only; the internal-edges projection is a THEOREM (edge-id uniqueness via
-- `retarget_residual_edges_injective`); the shared core `touchedOuterComponents_of_occurrence` is the follow-up.

end GaugeGeometry.QFT.Combinatorial
