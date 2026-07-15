import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForwardOuterValue

/-!
# R-6c-body-296 — `promote_collapse` is an honest de-contraction floor leaf (floor pin)

Two-hundred-and-ninety-sixth genuine-body step, a floor-pin scout (no new geometry).  It audits body-289's
`promote_collapse` leaf and records the verdict: it is a genuine de-contraction leaf requiring the EXACT forest index
`B`, not reducible for a generic `z`.  Imports body-289 so the pin stays honest against the source.

## The leaf

```lean
promote_collapse : (ResolvedAdmissibleSubgraph.promote γ.1 (forestTag z γ h).1).elements = {γ.1}
```
for a recovered parent `γ ∈ forestRecovered z` and a GENERIC `z : ForestBlockCodType D G`.

## The reduction (only the outer layer is `rfl`)

`ResolvedAdmissibleSubgraph.promote_elements` (ResolvedSubgraphPromote.lean:129, `@[simp]`, `rfl`) gives
`(promote γ B).elements = B.elements.image (fun δ => γ.promote δ)` — the IMAGE, not the singleton.  So `promote_collapse`
is defeq to

```text
B.elements.image (fun δ => γ.promote δ) = {γ}    with B = forestTag z γ h
```

which forces `B.elements = {δ₀}` a singleton whose element de-contracts back to `γ` (`γ.promote δ₀ = γ`) — i.e. `B` must
be the **whole-component (trivial one-piece) forest** of `γ.toResolvedFeynmanGraph`.  There is no `promote_top` /
`promote γ ⊤ = γ` lemma in the tree; the singleton collapse is NOT proved anywhere (in every occurrence
`promote_collapse` is an assumed field, the only in-tree assignment being a field pass-through).

## Why it is a floor (and distinct from `forestTag_agrees`)

`forestTag` is honestly arbitrary (body-282; floor-pinned body-295): the generic-`z` region core retains no `B`/occurrence
and never pins `forestTag`'s value to the top forest.  So nothing forces the arbitrary `forestTag` to return the
whole-component forest, and `promote_collapse` cannot be proved from promote-geometry alone.  It needs the EXACT `B`
(the whole-component property) — hence it is **not** `B`-agnostic and is **coupled to which forest index `forestTag`
returns**.  It is a DISTINCT floor from `forestTag_agrees` (which asserts two occurrences' `B` agree at forward images):
`promote_collapse` needs no forward-image agreement, but it does need `forestTag`'s value to be the top forest.

> **`promote_collapse` is a genuine de-contraction floor leaf.**  Only the outer `promote_elements` layer is `rfl`; the
> singleton collapse requires the exact forest index `B = forestTag z γ h` to be the whole-component forest, which the
> arbitrary body-282 `forestTag` does not supply for a generic `z`.

Two of the six component-level leaves are now floor-pinned (`forestTag_agrees`, body-295; `promote_collapse`, this body);
`survivor_mem_value` / `remnant_mem_value` are reduced to their two-direction floors (bodies 293/294); the remaining
audits are `forestComponentMem` (body-297) and `represented_cases` (body-298).

Per the HALT: this is a docstring floor-pin only; the import keeps the pin honest against body-289.  No declarations
beyond this docstring; no facade, no flat term, no `forgetHopf`.
-/
