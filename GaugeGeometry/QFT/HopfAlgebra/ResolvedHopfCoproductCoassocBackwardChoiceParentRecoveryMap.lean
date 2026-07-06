import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestChoiceOccurrenceRecovery
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocBackwardChoiceFinalLeaf

/-!
# R-6c-body-201 — backward-choice parent recovery map: closed to `parent_recovered` (docs anchor)

Two-hundred-and-first genuine-body step, a documentation anchor (no new geometry).  After bodies 196–200 the
backward-choice round-trip is closed to a single homogeneous geometry leaf — the forward round-trip parent recovery.
This module records that state and the residual leaves, importing the occurrence-recovery and final-leaf modules so
the map stays type-checked.  Reader-facing narrative: `CK_HOPF_FORMALIZATION_MAP.md` §"R-6c bodies 196–200";
proof-dependency map: `CK_HOPF_DEPENDENCY_GRAPH.md` §"R-6c bodies 196–200".

## The backward-choice, closed (all axiom-clean `[propext, Classical.choice, Quot.sound]`)

```text
196  forest_value_eq split — recoverChoice tag pinning (188 pattern) + forestTag_forward_eq (fresh forward-forest).
197  dual scout — forestTag_forward_eq and forward_quotient_heq are DUAL (domain q vs codomain z); attack separately.
198  forestTag_forward_eq reduced — Sum.inr.inj ⟹ forest_choiceAt_eq (q.2 γ = inr forestTag_fwd).
199  backward-choice final leaf — the whole chain (198→196→194→193→164) supplied by forest_choiceAt_eq.
200  occurrence recovery — forest_choiceAt_eq PROVED from a recovered occurrence (occ.hchoice, free) +
       parent_recovered (occ.γ = γ), via heq_transport_choice (cases the parent Eq, then occ.hchoice).
```

## Canonical chain

```text
200 → 198 → 196 → 194 → 193 → 164 → 160 → 154 → 147 → witnessSplit → coassoc_gen
```

## The remaining backward-choice geometry

No longer an `HEq` or a choice-value abstraction — the homogeneous parent recovery

```text
parent_recovered : occ.γ = γ
```

an `Eq` of outer components (the forward round-trip parent identity), plus the occurrence construction.

## Residual (the honest floor now)

* **backward-choice** — the single homogeneous `parent_recovered` (`occ.γ = γ`) + the occurrence construction;
* **forward-quotient** — `forward_quotient_heq` (the dual, heavier `ForestIdx` reconstruction, untouched);
* **forward outer** — closed to the compatibility leaves (bodies 188/185/180);
* **backward outer** — the three sector bridges (bodies 170/171/172), proved up to `choice_tag_trichotomy` (body-173);
* **sector bridge internals** — the `componentToRight` / `componentToForest` round-trips, `representedInQuotient`;
* **pairwise disjointnesses** (body-158) and the **carrier closure** (body-159);
* **region classifiers** (bodies 150/151/152) and the non-region base (contract `vertices_eq`, measure,
  star/global-gap kernel, survivor/remnant Inj/Gen, `carrier_isProperForest` / `rep` / `selectedOuter_mem`).

## Note

The backward-choice is closed to the forest parent recovery `parent_recovered`; the next front is the
`parent_recovered` scout — the sector forest round-trip (`componentToForest (fwdMap q)` recovering the original
`γ`, i.e. occurrence parent injectivity).  No declarations beyond this docstring anchor; the imports keep the map
honest against the source.  No facade, no flat term, no `forgetHopf`.
-/
