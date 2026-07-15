import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecoveredPreimageValueCover

/-!
# R-6c-body-287 — the value-root construction migration is complete (docs anchor)

Two-hundred-and-eighty-seventh genuine-body step, a documentation anchor (no new geometry).  It fixes the
construction-boundary closure — the counterpart of the parametric-layer completion (body-271).  Imports body-286 so the
map stays type-checked against the source.  Reader-facing narrative: `CK_HOPF_FORMALIZATION_MAP.md` §"R-6c bodies
271–286"; proof-dependency map: `CK_HOPF_DEPENDENCY_GRAPH.md` §"R-6c bodies 271–286".

## The headline

```text
The R-6c value-root construction migration is complete.

The concrete witnessSplit cover and the top-level coassociativity theorem are
constructed entirely from the filtered value root.  No total forward map,
Forward supply, legacy adapter, or phantom S remains on the canonical path.
```

## Two decisive audit corrections (do not re-litigate)

* **body-273** — the quotient component is NOT `rfl`-portable: `rightDomain` / `forestDomain` read `z.2`
  (= `V.quotientForestRaw` at the value root, `S.quotientForest` at the total root); the migration is MEDIUM,
  reconstructed from `V`'s survivor/remnant split (`V.union_eq`).
* **body-284** — the round-trip residual is THREE leaves, not two: the forest-component `backward_choice` HEq needs the
  EXACT value `forestTag = B` (`forestChoiceSelected` forgets `B`) — the value analog of body-200's `forest_choiceAt_eq`.

## The canonical chain (all value-root, S-free)

```text
S-free region cores + bridges (left/right/forest)     274–280
→ region coherence + raw closure + preimage root       281–283
→ backward outer (pure) + exact 3-leaf audit           284
→ 3 leaves produce 2 whole round-trips                 285
→ filtered concrete branch data + concrete cover       286
→ ResolvedForestBlockBijectionSupply                   97
→ coassoc_gen
```

`coassoc_gen_of_recovered_preimage_value` (body-286) is the S-free top-level statement — `F` / `V` / `R.toCover` /
`forwardQuotientMemValueOfValue F V` (free, body-272) + base leaves → `Δᵣ`-coassociativity, never mentioning
`ResolvedParametricCarrierClosureSupply D S`.

## Final status

```text
proof-shape residual        NONE
migration residual          NONE
construction boundary       CLOSED (concrete value cover, body-286)
value round-trip geometry   3 explicit leaves (forward_outer_value, forward_quotient_value, forest_value_eq)
region geometry             sound/complete + classifier leaves (mixed_ne_pR/pL, forest_nonempty)
carrier closure             honest model supply (recovered_raw_mem + pairwise disjoint, body-269)
concrete carrier instance   separate phase 1b (enumeration + permutation + hCD)
```

The total-forward machinery is **retired from the canonical path**, not "unused": it survives only in the comparison /
migration-check converters (`.ofLegacy`, `.toValueCore`, `.toParametricCarrierClosure`), never on the route to
`coassoc_gen_of_recovered_preimage_value`.  Full unconditional resolved coassociativity remains unclaimed pending a
concrete phase-1b model instance discharging the three value round-trip geometry leaves + the region / carrier model
supplies.

Per the HALT: this is a docstring anchor only; the import keeps the map honest against body-286.  No declarations beyond
this docstring; no facade, no flat term, no `forgetHopf`.
-/
