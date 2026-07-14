import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocWitnessSplitFilteredValue
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocParametricCarrierClosure
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRegionRoundTripReduction

/-!
# R-6c-body-273 — construction-boundary scout: how the concrete value cover would be built (SCOUT)

Two-hundred-and-seventy-third genuine-body step, a scout (no new geometry).  It audits the *last* wiring boundary
below the closed parametric theorem: how a concrete `ResolvedWitnessSplitFilteredValueCoverSupply F V` (body-253, the
`cover` hypothesis of `coassoc_gen_of_parametric_model_value`) would actually be constructed, and classifies every
dependency.  Imports the three source anchors it audits (253 target types, 269 closure, 142/RegionRoundTripReduction
total root) so the map stays honest.

## Finding 0 — no concrete value-root cover constructor exists yet

`ResolvedWitnessSplitFilteredValueConcreteData` / `...CoverSupply` (body-253) are only ever DEFINED (+ `witnessSplit*` /
`toCover`); no `def … : ResolvedWitnessSplitFilteredValueConcreteData … where` inhabits them.  The sole concrete
branch-data builder is `ResolvedRegionRoundTripReductionSupply.toBranchSupply`
(`RegionRoundTripReduction.lean:112`) — 100% over the **total root** `fwdMap S` / `S.Forward`.  A value-root concrete
constructor must be built (bodies 274+).

## Three-bucket dependency classification

**(1) z-LOCAL raw geometry — needs no change** (reads only `z : ForestBlockCodType D G`; `S` is a phantom type-index):
`starOfZ` / `rightDomain` / `forestDomain` (`RegionConstructionFromSector.lean:79,83,88`), the region maps
`rightRecovered` / `forestRecovered` / `leftResidual` (+ `_elements_eq`, 156/157), `choice_tag_trichotomy`
(`RecoveredRegionMembershipAssembly.lean:78`, generic in `q`), and the union geometry
`ResolvedOuterUnionConstructionSupply` / `ResolvedConcreteRegionUnionSupply` fields (all `∀ z`, 142/184).

**(2) FORWARD-IMAGE statements — must re-key from the total forward map** (the real migration targets, verbatim):
`RegionRoundTripReduction.lean:74-86` (`forward_outer` reads `S.Forward.imageSupply.selectedOuterOf` at **:75**;
`forward_quotient` reads `S.quotientForest`; `backward_outer`/`backward_choice` read `fwdMap S q`) — **the root**;
`WitnessSplitMixed.lean:80-86,107-117`; `WitnessSplitForest.lean:85-91,112-120`;
`WitnessSplitConcrete.lean:80-82,94-105`; `WitnessSplitFromCover.lean:83-89,110-134`; the three sector bridges
`LeftResidualSectorBridge.lean:75`, `RightRegionSectorBridge.lean:71`, `ForestRegionSectorBridge.lean:79`; and
`recovered_region_membership` (`RecoveredRegionMembershipAssembly.lean:107-115`).

**(3) carrier PACKAGING — already consolidated in body-269** (`∀ z`, no forward map): raw regions → pairwise disjoint →
raw union → `recovered_raw_mem` → carrier-tagged recovered outer.  The union construction (184/142) inhabits **directly**
from body-269's `.toRegionPartitionSupply` / `.toRecoveredOuterCarrierSupply` — no extra forward-image fact (verified by
inspection: `ForestRecoveredBridge.lean:84-99` consumes only region maps + pairwise + `∀ z` membership).

## Phantom `S` (droppable via converter / value re-index)

`RegionConstructionFromSector.lean` (156) and `LeftResidualConstruction.lean` (157) NEVER read `S` (no `S.` occurrence in
any body); `S` is only a type index.  Likewise the bucket-3 union structures (184/142).  These carry `S` purely
phantom.

## THE CRUX — corrected depth verdict (NOT a pure rfl re-key)

The region domains read the **quotient**, not just the outer:

```lean
rightDomain  z := z.2.1.elements.filter (fun δ => Disjoint δ.vertices (starOfZ z))   -- :88
forestDomain z := z.2.1.elements.filter (fun δ => ¬ Disjoint δ.vertices (starOfZ z)) -- :94
```

so a region statement at `z` depends on `z.2` (the quotient forest).  Therefore:

* at `z = fwdMap S q`                       : `z.2 = S.quotientForest q`
* at `z = fwdMapFilteredValue F V ⟨q,hq⟩`   : `z.2 = V.quotientForestRaw q.1`

These are **not** equal in general — `V` is an independent value bundle.  So the prior migration scout's rfl-bridge
(`fwdMapFiltered ⟨q,hq⟩ = fwdMap S q` by `Subtype.ext rfl`, body-248) holds for **`fwdMapFiltered`** (body-249, which
reuses `S.quotientForest`) but **NOT for `fwdMapFilteredValue`** (body-252, which uses `V.quotientForestRaw`).  Only the
**outer** agrees by `rfl` (`fwdMapFilteredValue_outer_fst`, body-252) — the quotient does not.

Two honest routes:

```text
Route A  (fwdMapFiltered, total-quotient)   rfl-shallow re-key of 170-173 + branch specs, BUT the concrete cover stays
                                            parameterized by S (S.quotientForest is the quotient source) — it does NOT
                                            reach the value root that coassoc_gen_of_parametric_model_value consumes.
Route B  (fwdMapFilteredValue, value root)  the cover the top-level theorem actually needs; the region membership must
                                            be RE-DERIVED from V's OWN survivor/remnant decomposition (body-252
                                            V.union_eq / V.Survivor / V.Remnant / V.hcross / V.hRdisj), since
                                            z.2.1.elements = (V.quotientForestRaw q).1.elements = survivor ∪ remnant,
                                            and rightDomain/forestDomain are the star-avoiding / star-touching halves.
                                            Bounded but genuine — MEDIUM depth, not rfl.
```

**Corrected verdict.**  The bucket classification, migration-target list, and phantom-`S` findings stand.  But the depth
is **MEDIUM (value-root re-derivation via V's decomposition)**, not SHALLOW-rfl: the value cover's forward round-trip
`fwdMapFilteredValue F V ⟨witnessSplit z, _⟩ = z` needs the quotient recovery `V.quotientForestRaw (witnessSplit z) = z.2`
(HEq), which the S-based bridges gave via `S.quotientForest`.  The good news: **V already carries the survivor/remnant
split of its own quotient** (`V.union_eq`), so the re-derivation is closed inside `F + V` — no new leaf, no `Forward`.

## Re-key path (bodies 274+)

```text
156/157 : reusable as-is (S phantom)                — bucket 1
184/142 : inhabit union from body-269 converters    — bucket 3, no forward fact
170-173 : re-derive region membership at            — bucket 2, MEDIUM: read V.quotientForestRaw via V.union_eq,
          fwdMapFilteredValue (via V's decomposition)   NOT S.quotientForest; outer by fwdMapFilteredValue_outer_fst (rfl)
141-144 : value branch specs over fwdMapFilteredValue — bucket 2
→ ResolvedWitnessSplitFilteredValueConcreteData → .toCover → the cover hypothesis
```

## Design guards (for 274+)

* do NOT build `cover` via `.ofLegacy`;
* do NOT keep old `ResolvedConcreteSummandBundleSupply` as a canonical-constructor argument (drop the phantom `S` by
  converter; the quotient source is `V`, not `S`);
* do NOT reintroduce a backward law over unfiltered `q`;
* body-269 closure is the sole model input for carrier membership;
* keep raw region geometry and carrier closure as separate records.

Per the HALT: scout only — the audit is recorded; no cover is constructed, no re-key is performed; the imports keep the
map honest against the source.  No declarations beyond this docstring; no facade, no flat term, no `forgetHopf`.
-/
