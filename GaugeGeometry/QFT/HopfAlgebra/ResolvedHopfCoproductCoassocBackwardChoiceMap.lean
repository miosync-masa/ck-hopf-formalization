import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocChoiceComponentCases

/-!
# R-6c-body-195 — backward-choice map: the backward-choice HEq reduced to a forest value equality (docs anchor)

Hundred-and-ninety-fifth genuine-body step, a documentation anchor (no new geometry).  After bodies 192–194 the
backward-choice `HEq` mismatch is retired and its content driven down to a single forest value fact.  This module
records that state and the residual leaves, importing the cases module so the map stays type-checked.  Reader-facing
narrative: `CK_HOPF_FORMALIZATION_MAP.md` §"R-6c bodies 192–194"; proof-dependency map:
`CK_HOPF_DEPENDENCY_GRAPH.md` §"R-6c bodies 192–194".

## The backward-choice HEq, retired (all axiom-clean `[propext, Classical.choice, Quot.sound]`)

```text
192  HEq scout — backward_choice_heq is LIGHT (homogeneous componentwise Eq under the proved outer partition);
       forward_quotient_heq is HEAVY (ForestIdx over two contract-with-stars graphs).
193  heq_of_index_eq — (A = B) + pointwise Eq ⟹ HEq (subst + heq_of_eq + funext); backward_choice_heq PROVED from
       the outer partition (body-160) + the componentwise Eq.
194  choice component cases — case on q.2 γ:
       inl false → rightPrimSelected → right bridge (170) → right_tag   ✓
       inl true  → leftSelectedConcrete → left bridge (172) → left_tag  ✓
       inr B     → forestChoiceSelected → forest bridge (171) → forest_tag ∃ B'; value match B' = B = forest_value_eq
```

## Canonical chain

```text
194 → 193 → 164 → 160 → 154 → 147 → witnessSplit → coassoc_gen
```

## Residual (the honest floor now)

* **backward-choice** — the single `inr` value fact `forest_value_eq` (the choice-value de-contraction: on a forward
  image, the recovered forest tag equals `q`'s original forest index) + the reused tags / bridges + the proved index
  transport;
* **forward-quotient** — `forward_quotient_heq` (the heavier `ForestIdx` reconstruction, untouched);
* **forward outer** — closed to the compatibility leaves (bodies 188/185/180);
* **backward outer** — the three sector bridges (bodies 170/171/172), proved up to `choice_tag_trichotomy` (body-173);
* **sector bridge internals** — the `componentToRight` / `componentToForest` round-trips, `representedInQuotient`;
* **pairwise disjointnesses** (body-158) and the **carrier closure** (body-159);
* **region classifiers** (bodies 150/151/152) and the non-region base (contract `vertices_eq`, measure,
  star/global-gap kernel, survivor/remnant Inj/Gen, `carrier_isProperForest` / `rep` / `selectedOuter_mem`).

## Note

The backward-choice `HEq` is retired to `forest_value_eq`; the next front is the `forest_value_eq` scout — the
choice-value de-contraction relating `recoverChoice`'s `forestTag` on a forward image to `q`'s original forest index.
No declarations beyond this docstring anchor; the imports keep the map honest against the source.  No facade, no flat
term, no `forgetHopf`.
-/
