import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocWitnessSplitFilteredValue
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSummandAgreeValue

/-!
# R-6c-body-255 — migration interface map: bodies 248–254 (docs anchor)

Two-hundred-and-fifty-fifth genuine-body step, a documentation anchor (no new geometry).  It fixes the milestone that
the `fwdMap` filtered-domain migration is complete **at the interface / statement level**: the retired total
selected-outer root no longer appears in any canonical migration interface.  Imports body-253/254 so the map stays
type-checked.  Reader-facing narrative: `CK_HOPF_FORMALIZATION_MAP.md` §"R-6c bodies 248–254"; proof-dependency map:
`CK_HOPF_DEPENDENCY_GRAPH.md` §"R-6c bodies 248–254".

## The interface migration (248–254)

```text
248  scout: verdict (3) PROVIDER-RETYPE (shallow) — every proof ports verbatim by Subtype.ext rfl.
249  fwdMapFiltered : FilteredForestBlockDom D G → ForestBlockCodType D G   (tag from body-245, not the total root)
       + fwdMapFiltered_eq_legacy (rfl) — migration-check only.
250  ResolvedWitnessSplitFilteredCoverSupply (round-trips vs fwdMapFiltered) + .ofLegacy.
251  ResolvedWitnessSplitFilteredConcreteData + dite assembly → the cover WITHOUT the legacy bridge.
252  ResolvedConcreteSummandValueSupply — independent value root, DROPS Forward; fwdMapFilteredValue + rfl projections.
253  ResolvedWitnessSplitFilteredValue{Cover,ConcreteData} + toCover — round-trip chain on the value root, Forward-free.
254  ResolvedSummandAgreeValueSupply — term equality over fwdMapFilteredValue, Forward-free statement; .ofLegacy defeq.
```

## The headline (precise)

```text
The retired total selected-outer root no longer appears in any canonical migration interface.
It survives only in explicitly marked legacy-comparison adapters (fwdMapFiltered_eq_legacy, the several .ofLegacy).

The interface migration is complete; canonical proof inhabitants remain for
witnessSplit membership, branch geometry, and value-side summand agreement.
```

## Migration status (statement vs canonical proof)

```text
Layer                    Statement       Canonical proof
filtered forward map     complete        membership root (body-245)
witnessSplit cover       Forward-free    branch specs / witnessSplit_mem remain
value bundle             complete        geometry fields remain
summand agreement        Forward-free    factor-equality discharge remains
legacy total root        retired         comparison adapters only
```

## Note

Among the `isProper` conjuncts only `0 < complementEdges.card` (strict properness) remains (plus `recovered_eq`).  On
the migration side the statements are `Forward`-free; the proof-level inhabitants remain — `witnessSplit_mem`
(total-root-free via `OuterMixingInvMem` / `forestChoiceCarrier` membership), the branch geometry, and a canonical
`summand_agree_value` via the factor-equality path (`resolved_splitChoice_summand_agree_of_factor_eqs`,
`ForestCarryingBlock.lean:68`).  A hidden domain defect to audit: `ResolvedSummandFactorBundle.selected` is **total**
(a total-root-shaped image supply) — the last place the filtered-domain correction must reach.  The next fronts are
`witnessSplit_mem` canonical instantiation, the `summand_agree_value` factor-equality discharge (and the `selected`
audit), then the strict `complementEdges` conjunct.  No declarations beyond this docstring anchor; the import keeps the
map honest against the source.  No facade, no flat term, no `forgetHopf`.
-/
