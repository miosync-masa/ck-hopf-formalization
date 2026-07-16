import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocGeometryFloorAssembly

/-!
# R-6c-body-306 — forest-parent domain defect: floor-297/298 are over-typed on the codomain (judgment pin)

Three-hundred-and-sixth genuine-body step, a domain-defect judgment scout (no new geometry).  The construction audit
(body-305) settled the forward-image side; this body settles the GENERIC-`z` existence question and records the honest
finding: **there is no total de-contraction source-projection into `z.1.1.elements`, so floor-297
(`forest_parent_mem_value`) and its twin floor-298 (`represented_forest_complete_value`) are FALSE at an orphan generic
`z` — the codomain-side analogue of the retired total `selectedOuter_mem` (body-128) over-typing.**  Imports body-299 so
the pin stays honest against the source.

## Verdict B (honest model datum), bounded by C (over-typing)

* **No total source-projection into a single component.**  A total concrete de-contraction `parentOfQuotient`
  (ResolvedActualSigmaCover.lean:894-943) exists for a generic `δ : ResolvedFeynmanSubgraph (Aout.contractWithStars …)`,
  but it lands in the WRONG type: its carrier has `internalEdges = Aout.internalEdges + …` (`:905`, `:958-966`), so
  `γ ⊇ Aout` (the whole outer forest) — `γ ∉ z.1.1.elements`.  The per-component restriction is proven **over-strong**
  for multi-component / generic `B` (DeContraction-3, `:997-1052`, verdict `:1026-1032`: the projection forces
  `Aout.starVertices ⊆ δ.vertices` — "the target component must contain ALL outer stars", false for a small star-
  spanning inner component).

* **`z.2` is FREE of `z.1.1`.**  `ForestBlockCodType z = (A, B)` with `B = z.2` an ARBITRARY `ForestIdx` of
  `A.contractWithStars` (ForestBlockBijection.lean:79-81; `forestBlockCodFinset` ranges over the full `forestCarrier`,
  `:88-90`; "the outer is NOT preserved", `:78`).  Nothing forces `z.2`'s components to be de-contractions of individual
  `z.1.1.elements`; a star-touching `δ` may span several stars (several `A`-components) — an orphan.

* **So floor-297 `forest_parent_mem_value : ∀ z δ, componentToForest z δ ∈ z.1.1.elements`
  (GeometryFloorAssembly.lean:74-76) is FALSE at an orphan `(z, δ)`.**  Same shape as the retired total
  `selectedOuter_mem` (body-128), which was FALSE at the extremal splits `p_R`/`p_L` and fixed by the filtered-domain
  repair (bodies 245/249) — but now on the CODOMAIN side.

## The live domain is fine

At the reachable domain `z = fwdMapFilteredValue F V q` (`ConcreteSummandValue.lean:100-102`), `z.2 = V.quotientForestRaw
q.1 = survivor ∪ remnant`, and every remnant genuinely de-contracts from a single `choiceParent` (body-305:
`remnantComponent = reembedAsSubgraph (contractedSourceGraph)`, occurrence root).  All the DEEP round-trip specs already
quantify `q : FilteredForestBlockDom` (`RecoveredPreimageValueRoundTrip.lean:64`, `GeometryFloorAssembly.lean:63`), so
the defect is confined to the `∀ z`-typed region-core floors, not the round-trip laws.

## The repair (a phase-1b codomain-restriction sub-front)

Mirror the body-245/249 filtered-domain repair, on the codomain side: restrict the region-core `componentToForest` /
floor-297 / floor-298 from `∀ z : ForestBlockCodType` to the reachable / compatible codomain (the `fwdMapFilteredValue F
V q` images), OR carry the de-contraction parent-existence + spec as a model datum quantified only over reachable `z`.
Do NOT attempt a total `∀-z` proof (false for generic `B`); do NOT use `Classical.choose`-without-proof (the sole
region-adjacent `Classical.choose`, SectorBackwardMaps.lean:60/66, is backed by the proved sector `forest_surj`, whose
codomain is a genuine image); no default-parent hack.

## Guards / status

The forward-image occurrence bullets are ready (body-305 `forestChoiceSelected_of_occurrence`); the blocker is the
codomain over-typing, NOT the geometry.  Phase-1b must repair the region-core codomain typing before floor-297/298 can be
inhabited — a bounded, well-understood migration (the filtered-domain pattern, now codomain-side), not a new deep
obstruction.

Per the HALT: this is a domain-defect judgment pin only; the import keeps it honest against body-299.  No declarations
beyond this docstring; no facade, no flat term, no `forgetHopf`.
-/
