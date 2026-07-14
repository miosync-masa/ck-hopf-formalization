import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocFilteredBijectionSide

/-!
# R-6c-body-271 — the parametric layer completes: a single conditional coassociativity theorem (docs anchor)

Two-hundred-and-seventy-first genuine-body step, a documentation anchor (no new geometry).  It fixes the R-6c
**headline**: the parametric coassociativity layer is closed to one honest conditional statement.  Imports body-270 so
the map stays type-checked against the source.  Reader-facing narrative: `CK_HOPF_FORMALIZATION_MAP.md` §"R-6c bodies
268–270"; proof-dependency map: `CK_HOPF_DEPENDENCY_GRAPH.md` §"R-6c bodies 268–270".

## The chain (body-269 supply → body-270 theorem)

```text
ResolvedParametricCarrierClosureSupply          (body-269, carrier-closure assumptions consolidated)
  + filtered value bundle                       (body-252, ResolvedConcreteSummandValueSupply — Forward-free)
  + filtered witnessSplit cover                 (body-253, ResolvedWitnessSplitFilteredValueCoverSupply)
  + forward quotient membership                 (body-270, ResolvedForwardQuotientMemValueSupply — the sole new leaf)
  + explicit base / geometry leaves             (carrier_isProperForest, rep / repCD / rep_gen)
→ ResolvedForestBlockBijectionSupply            (body-97, the raid-boss sum_bij' data — inhabited directly)
→ coassoc_gen                                    (body-270, coassoc_gen_of_parametric_model)
```

## The 12-field supply table (all Forward-free, no `.ofLegacy`)

```text
ResolvedForestBlockBijectionSupply field   supplied by
toFun                                      fwdMapFilteredValue F V ⟨q,hq⟩            (252)
invFun                                     cover.witnessSplit                       (253)
toFun_mem                                  forwardMem.quotient_mem + mem_attach     (270, NEW leaf)
invFun_mem                                 cover.witnessSplit_mem                    (253)
left_inv                                   cover.backward_witness                    (253)
right_inv                                  cover.forward_witness                     (253)
summand_agree                              summand_agree_value_of_value F V          (259, DERIVED — not a field)
carrier_isProperForest                     base model leaf                           (96)
rep / repCD / rep_gen                      representative base leaves
```

## The headline (precise)

```text
The R-6c parametric layer is complete as a single conditional
coassociativity theorem.

The theorem path is entirely filtered-domain, value-rooted,
Forward-free, and legacy-adapter-free.
```

## Residual — separated exactly

```text
theorem-level migration residual   none                — no total selectedOuter_mem, no .ofLegacy on the path
new local leaf                     ResolvedForwardQuotientMemValueSupply.quotient_mem   (the only new obligation)
construction boundary              the concrete value cover's region / backward chain (156/157/173/184), still
                                     phrased against the total forward map — a construction detail, NOT on the theorem
model instance phase               carrier enumeration / permutation closure / hCD      (phase 1b, separate)
original geometry / base leaves    explicit hypotheses of coassoc_gen_of_parametric_model
```

The distinction is the whole point: `coassoc_gen_of_parametric_model` is Forward-free / `.ofLegacy`-free **as a
theorem** — it takes the migrated value-root `cover` (body-253) as a hypothesis.  Producing a *concrete* `cover` from
the region converters (body-269's `toRegionPartitionSupply` / `toRecoveredOuterCarrierSupply`) still routes through the
total-forward region chain; that is the single named construction boundary, below the theorem, not a gap in it.

Per the HALT: this is a docstring anchor only; the import keeps the map honest against body-270.  No declarations beyond
this docstring; no facade, no flat term, no `forgetHopf`.
-/
