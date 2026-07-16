import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocOuterMixingValueInverse

/-!
# R-6c-body-309 — classifier-leaf ordering audit: the suspected cycle is FALSE (verdict B, re-stratification pinned)

Three-hundred-and-ninth genuine-body step — a dependency-circularity + classifier-provability judgment scout, ahead of
proving the mixed classifier leaves.  The suspected cycle
`mixed_ne_pR/pL → recoveredPreimageValue_mem → R.Data → forward_roundtrip_value → mixed_ne_pR/pL` is audited and found
**FALSE**: the classifier leaves are provable from the RAW forward identities (which are classifier-free), and the only
defect is interface ORDERING.  This body pins verdict **B** + the correct re-stratification; no new geometry, no proofs of
the leaves themselves (that is body-310).  Imports body-308 so the pin stays honest against the inverse it feeds.

## Verdict B — no true cycle; the defect is layer bundling

* **`resolvedIsForestImage` is a pure star-touch existential** (ForestImageClassifier.lean:66-69:
  `∃ δ ∈ B.1.elements, ¬ Disjoint δ.vertices (A.1.starVertices (D.starOf G A.1))`) — it names NONE of
  `recoverChoiceValue` / `recoveredPreimageValue` / `p_R` / `p_L`.  So the extremal inequalities do NOT follow from the
  classifier definition alone (**verdict A refuted**).

* **`Tags` is a strictly lower layer than the mixed leaves.**  `ResolvedRegionTagValueSupply` (body-282,
  OuterUnionRegionTagValue.lean:71-94) = `Closure` + `forestTag` + three region exclusivities; NO `mixed_ne`, NO
  `forest_nonempty`, NO classifier.  `recoveredPreimageValue = ⟨Closure.unionOuterValue z, recoverChoiceValue z⟩`
  (:140-142) and `recoverChoiceValue` (:101-110) are definable from raw `Tags` alone.  `ResolvedRecoveredPreimageValueMem`
  (body-283, RecoveredPreimageValueMem.lean:45-59) takes `Tags` as a FIELD and adds `forest_nonempty` / `mixed_ne_pR` /
  `mixed_ne_pL` as SIBLING fields — that sibling bundling is the entire defect.

* **The raw forward identities do NOT consume the classifier.**  `forward_outer_value` (PROVED, body-289,
  ForwardOuterValue.lean:175: `selectedOuterRawOf (recoveredPreimageValue z) = z.1.1`) consumes `Data.Tags` + three
  geometry leaves (`promote_collapse` / `forestComponentMem` / `represented_cases`) and **never** `Data.mixed_ne_*` /
  `Data.forest_nonempty`.  `forward_quotient_value` (PROVED, body-290, ForwardQuotientValue.lean:100) consumes
  `forward_outer_value` + survivor/remnant membership bridges — no `mixed_ne`.  `forest_value_eq`
  (RecoveredPreimageValueRoundTrip.lean:63-70) is stated purely on `Tags`/`Closure` — classifier-free.

* **The cycle does not close.**  `recoveredPreimageValue_mem` (body-308, OuterMixingValueInverse.lean:93-98) is a
  `by_cases resolvedIsForestImage` dispatching `forestPreimage_mem` (uses `forest_nonempty`) / `mixedPreimage_mem` (uses
  `mixed_ne_pR/pL`); it does NOT call `forward_roundtrip_value`.  `forward_roundtrip_value` takes `hmem` as a HYPOTHESIS
  and is built from the two classifier-free forward facts.  In `toOuterMixingInverse`, `invFun_mem` (← `recoveredPreimageValue_mem`)
  and `forward` (← `forward_roundtrip_value`) are INDEPENDENT inputs — the last arrow `forward_roundtrip → mixed_ne`
  does not exist (**verdict C refuted**).

## The exclusion mechanism (classifier-free, contrapositive)

* **`mixed_ne_pR`** (`(recoveredPreimageValue z).2 ≠ fun _ _ => Sum.inl false`, under `¬ resolvedIsForestImage`): if the
  recovered choice were all-`inl false` (= `p_R`, all-right-primitive), then `leftOf = ∅` (no `inl true`) and
  `promotedOf = ∅` (only `inr` promotes), so `selectedOuterRawOf (recoveredPreimageValue z) = ∅`; but
  `forward_outer_value` equates it with `z.1.1`, a proper-forest outer (nonempty via `carrier_isProperForest`).
  Contradiction.  Needs: `forward_outer_value` + "`selectedOuterRawOf` of an all-`inl false` choice is empty" (the
  contrapositive of body-244 `selectedOuterRaw_isNonempty_of_mem_forestChoiceCarrier`) + outer nonempty.

* **`mixed_ne_pL`** (`≠ fun _ _ => Sum.inl true` = `p_L`, all-left-selected): if all-left, then `rightRecovered` /
  `forestRecovered` are empty, so the quotient forest is empty; but `forward_quotient_value` HEq-identifies it with `z.2`,
  the proper-forest codomain (nonempty).  Contradiction.  Needs: `forward_quotient_value` + quotient-empty-of-`p_L` +
  `z.2` nonempty.

Both mechanisms are **classifier-free** (the classifier appears only as the discharged hypothesis `¬ resolvedIsForestImage`,
never in the proof body).  Supporting forward-direction machinery exists (body-244 `exists_nonright_of_ne_pR`,
`promotedElements_nonempty_of_inr`, `selectedOuterRaw_isNonempty_of_mem_forestChoiceCarrier`); the two contrapositive
emptiness lemmas are the genuinely NEW pieces (present only inline inside ForwardOuterValue.lean:129/135, not exported).

## The correct 6-layer re-stratification (for body-310+)

```text
1  raw preimage value            Tags  (recoveredPreimageValue / recoverChoiceValue)      OuterUnionRegionTagValue
2  raw round-trip geometry       forward_outer_value (289) · forward_quotient_value (290) · forest_value_eq   [Tags + geometry]
3  classifier leaves             mixed_ne_pR/pL  (from layer-2 forward facts + outer/quotient nonempty) ·
                                 forest_nonempty (from forest-branch region geometry)                          ← NEW proofs
4  filtered-domain membership    recoveredPreimageValue_mem (308)
5  round-trip leaf supply        R
6  outer-mixing inverse          toOuterMixingInverse (308)
```
The ONLY structural change: feed the forward-fact supplies from `Tags` (or a `Closure`-level record) rather than the whole
`Data` (body-283), so `mixed_ne_*` / `forest_nonempty` sit at layer 3 ABOVE the raw forward facts, not bundled beside
`Tags`.  This is a re-layering, not a new obstruction.

## Per-fact classifier-dependence table

```text
fact                    file:line                              classifier-dep   status                 layer
mixed_ne_pR             RecoveredPreimageValueMem.lean:53-55   N                FIELD (283)            3 (above fwd facts)
mixed_ne_pL             RecoveredPreimageValueMem.lean:57-59   N                FIELD (283)            3 (above fwd facts)
forest_nonempty         RecoveredPreimageValueMem.lean:50-51   N (hyp only)     FIELD (283)            3 (forest geometry)
forest_value_eq         RecoveredPreimageValueRoundTrip:63-70  N                FIELD (285)            2 (raw Tags/fwd)
forward_outer_value     ForwardOuterValue.lean:175             N                PROVED (289)           2 (raw Tags/fwd)
forward_quotient_value  ForwardQuotientValue.lean:100          N                PROVED (290)           2 (raw Tags/fwd)
```

Per the HALT: judgment pin only — verdict B + the re-stratification + the two exclusion mechanisms are recorded; the
classifier leaves are NOT proved here (body-310 target), no supply is split here, no `R.forward_roundtrip_value` /
`invFun_mem` is back-flowed into any classifier proof; no facade, no flat term, no `forgetHopf`.  The import keeps the pin
honest against body-308.
-/
