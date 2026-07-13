import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocInternalEdgesCardPos
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecoveredOuterRegionPartition

/-!
# R-6c-body-261 — complement-edges scout: the last conjunct has NO deep leaf (global monotonicity wins)

Two-hundred-and-sixty-first genuine-body step, a scout of the final `IsProperForest` conjunct
`0 < A.complementEdges.card` (strict properness) for the two constructed forests.  Verdict: **both routes reduce to
`A.internalEdges ≤ q.1.1.internalEdges` (edge subset) → complement positivity inherited from the carrier forest's
properness** — the promote-complement compatibility feared for the `inr` case is **bypassed entirely**.  No deep leaf;
only shallow mirrors of existing flat lemmas.

## `complementEdges` (verbatim)

`complementEdges A = G.internalEdges - A.internalEdges` (`ResolvedSubGraph.lean:268`, `Multiset` subtraction);
`internalEdges A = A.elements.sum (·.internalEdges)` (`:151`).  `0 < complementEdges.card` needs some edge `e` with
`A.internalEdges.count e < G.internalEdges.count e` (`Multiset.mem_sub` + `Multiset.card_pos_iff_exists_mem`).  The
only existing producer is the circular `complementEdges_card_pos_of_isProperForest` (`:658`); `internalEdges_le`
(`ResolvedCoproductIndex.lean:165`) is non-strict.

## Y — clean partition transfer (body-241 mirror)

`(unionOuter (fwdMap S q)).1.elements = q.1.1.elements` (`union_eq` `OuterUnionConstruction.lean:88` ∘
`recovered_region_partition` `RecoveredOuterRegionPartition.lean:81`) — membership-independent.  Elements-equality gives
`internalEdges`-equality (`congrArg` on the `:151` sum), hence `complementEdges`-equality (`:268`), hence
`.card`-equality; and `q.1.1 ∈ D.carrier G → IsProperForest → 0 < q.1.1.complementEdges.card` (`:658`).  No new infra
beyond the `simp only [internalEdges, h]` step.

## X — the GLOBAL monotonicity route (winner: no case split, no promote leaf)

```text
selectedOuterRawOf s .internalEdges ≤ s.1.1.internalEdges          (edge subset)
  ⇒ 0 < s.1.1.complementEdges.card  ⇒  0 < selectedOuterRawOf.complementEdges.card
```

by the count/monotonicity core (flat original `admissibleSubgraph_complementEdges_card_pos_of_internalEdges_le`,
`Coassoc.lean:3410`; the type-generic `multiset_sub_card_pos_of_left_le`, `:3427`, copies verbatim at
`Multiset ResolvedFeynmanEdge`).  The edge-subset `selectedOuterRawOf.internalEdges ≤ s.1.1.internalEdges` holds:

* **left** — `leftOf.elements = s.1.1.elements.filter (leftSelected)` (`LeftSelect.lean:70`, `inputOuter = s.1.1`
  `:48`), so each left component `∈ s.1.1.elements` and its edges `≤ s.1.1.internalEdges`;
* **promoted** — `promotedOf.elements = s.promotedElements` (`PromotedOf.lean:103`), each piece `γ.promote δ` with
  `γ ∈ s.1.1.elements` (`promotedComponentElements_inr` `:63`); `(γ.promote δ).internalEdges = δ.internalEdges`
  (`ResolvedSubgraphPromote.lean:61`) and `δ.internalEdges ≤ γ.internalEdges` (promote's `internalEdges_le`, `:52`),
  chained with `γ.internalEdges ≤ s.1.1.internalEdges`;

aggregated by a resolved mirror of `admissibleSubgraph_internalEdges_le_of_components_le` (`Coproduct.lean:3721`, using
`selectedOuterRawOf`'s `IsPairwiseDisjoint`).  **This bypasses the `inl false` per-component missing-edge argument AND
the `inr` promote-complement leaf; `exists_nonleft_of_ne_pL` is not even needed** (positivity is inherited globally,
not per-witness).

## Assessment and plan

* **Y: viable via partition transfer** (clean, membership-independent, body-241 shape).
* **X: viable via global edge-subset monotonicity** — `X.internalEdges ≤ q.1.1.internalEdges` → complement inherits
  from carrier properness.  **No deep leaf, no case split, no `p_L` witness.**
* **Single deep leaf: NONE.**  The only content is disjoint-forest count arithmetic that already exists verbatim on the
  flat side and inside the resolved `internalEdges_le` proof.

**body-262 targets (all shallow mirrors of existing flat lemmas):**
1. resolved `complementEdges_card_pos_of_internalEdges_le` (the monotonicity core; `count_lt_of_mem_complementEdges`
   inlines as `Multiset.mem_sub.mp` since `complementEdges = G.internalEdges - A.internalEdges`);
2. resolved `internalEdges_le_of_mem` (component edges ≤ ambient; count-proof already in
   `ResolvedCoproductIndex.lean:165-187`) and `internalEdges_le_of_components_le` (aggregate under pairwise-disjoint);
3. the two `≤`-facts assembling `selectedOuterRawOf.internalEdges ≤ s.1.1.internalEdges` (left filter + promote chain);
4. the two applications (X via monotonicity, Y via partition transfer).

Per the HALT: no conjunct body is proved; the two viable routes, the global-monotonicity win for X, and the exact
shallow-mirror targets are named — **the last `IsProperForest` conjunct is not a monolith and has no deep leaf**.  This
is a documentation / scout anchor (like body-235).  No declarations beyond this docstring.  No facade, no flat term, no
`forgetHopf`.
-/
