import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSummandAgreeValueCanonical
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocFilteredDomMembership

/-!
# R-6c-body-260 — migration closure map: bodies 248–259 (docs anchor)

Two-hundred-and-sixtieth genuine-body step, a documentation anchor (no new geometry).  It fixes the milestone that the
filtered-domain migration is complete at **both** the interface/statement and the proof levels — the retired total
selected-outer root is confined to explicitly marked legacy-comparison adapters.  Imports body-259/256 so the map stays
type-checked.  Reader-facing narrative: `CK_HOPF_FORMALIZATION_MAP.md` §"R-6c bodies 256–259"; proof-dependency map:
`CK_HOPF_DEPENDENCY_GRAPH.md` §"R-6c bodies 256–259".

## The headline (precise)

```text
The filtered-domain migration is complete at both the interface and proof levels.

The retired total selected-outer root is absent from the canonical forward map, witnessSplit cover, membership
proofs, value bundle, and summand agreement. It survives only in explicitly marked legacy-comparison adapters.

This was a domain correction, not a stronger proof of the false total theorem.
The case p_R remains cover-external through EmptyPivot.
```

## Final migration table (bodies 248–259)

```text
Layer                          Canonical status
selected outer membership      filtered root, proved (body-245)
forward map                    filtered / value-root (bodies 249/252)
witnessSplit statements        filtered, Forward-free (bodies 250/253)
witnessSplit membership        canonical tag proof (body-256)
value bundle                   independent Forward-free root (body-252)
summand agreement statement    Forward-free (body-254)
summand agreement proof        canonical factor-equality proof (bodies 258/259)
old total root                 retired, legacy-comparison adapters only
```

## The proof-level closers (256–259)

```text
256  mem_forestBlockDomFinset_of_choice / _of_isForestCarrying / _of_ne — canonical witnessSplit_mem from the tags
       (Finset.mem_sigma + mem_attach), total-root-free.
258  resolved_selectedOuter_left_factor_eq_of_parts_raw — the last term-path helper, re-keyed to raw (no S in type).
259  summand_agree_value_of_value (F) (V) : ResolvedSummandAgreeValueSupply F V — .ofLegacy-free, from V + F, all rfl.
```

## Residual (migration-derived vs mathematics-derived)

* **Migration residual — none** (the retired total root is confined to the `.ofLegacy` comparison lemmas).
* **`IsProperForest` — only `0 < complementEdges.card`** (strict properness).
* **Membership certificate — `recovered_eq`** (the section condition, body-232).
* **Original geometry** — branch specs, the eight sector `sound` / `complete` directions, forward compatibility, the
  region cross-disjointnesses, and the non-region base (contract geometry, measure, survivor/remnant providers, `rep`).

## Note

The next front is the strict `0 < complementEdges.card` conjunct — the last `IsProperForest` piece, purely geometric
and entirely independent of the (now complete) migration.  No declarations beyond this docstring anchor; the import
keeps the map honest against the source.  No facade, no flat term, no `forgetHopf`.
-/
