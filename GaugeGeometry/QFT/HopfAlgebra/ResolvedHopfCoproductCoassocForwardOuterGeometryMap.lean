import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForwardOuterGeometryAssembly

/-!
# R-6c-body-191 — forward outer geometry map: the forward outer closed to compatibility leaves (docs anchor)

Hundred-and-ninety-first genuine-body step, a documentation anchor (no new geometry).  After bodies 188–190 the
forward-outer partition is closed to its irreducible geometric compatibility and verified in one chain to body-162.
This module records that state and the residual leaves, importing the assembly module so the map stays
type-checked.  Reader-facing narrative: `CK_HOPF_FORMALIZATION_MAP.md` §"R-6c bodies 188–190"; proof-dependency map:
`CK_HOPF_DEPENDENCY_GRAPH.md` §"R-6c bodies 188–190".

## The forward outer, closed (all axiom-clean `[propext, Classical.choice, Quot.sound]`)

```text
188  componentToForest / promote compatibility — the SEMANTIC finding:
       (promote γ Bᵧ).elements = de-contracted SUB-PIECES of γ (⊆ γ); forestRecovered = the PARENTS;
       so promotedOf recovered = forestRecovered  IFF  (promote γ Bᵧ).elements = {γ}.
       Fielded: forestTag / recoverChoice_forest_eq / promote_collapse.  PROVED: per-component collapse = {γ}.
189  promoted_region_eq PROVED by biUnion collapse (inl regions → ∅, each forest parent → {γ}).
190  forward outer assembly — 188 + 185 + 180 + region constructions/bridges → body-179 → body-181 → body-162.
```

## Canonical chain

```text
190 → 181 → 177 → 174 → 167 → 162 → 160 → 154 → 147 → witnessSplit → coassoc_gen
```

## Forward outer final leaf list (the irreducible geometry)

```text
forestTag                 body-188   the forest index Bᵧ of a recovered parent
recoverChoice_forest_eq   body-188   tag pinning (recoverChoice = inr Bᵧ on the forest region)
promote_collapse          body-188   (promote γ Bᵧ).elements = {γ}
forestComponentMem        body-185   each componentToForest parent ∈ A
represented_cases         body-180   a quotient-represented A-component is a forest parent
region construction/wiring          body-156/157 constructions + leftResidual_eq / forestRecovered_eq bridges
```

Everything structural above these is proved: `leftOf` (174), `leftResidual_mem` (178), `coverage` (180),
`forestRecovered_mem` / `promoted_region_eq` (185/189).

## Residual (the honest floor now)

* **forward-outer** — *closed to the compatibility leaves above*;
* **backward-outer** — the three sector bridges (bodies 170/171/172), proved up to `choice_tag_trichotomy` (body-173);
* **`HEq` transports** — `backward_choice_heq` (body-164), `forward_quotient_heq` (body-165);
* **sector bridge internals** — the `componentToRight` / `componentToForest` round-trips, `representedInQuotient`;
* **pairwise disjointnesses** (body-158) and the **carrier closure** (body-159);
* **region classifiers** (bodies 150/151/152) and the non-region base (contract `vertices_eq`, measure,
  star/global-gap kernel, survivor/remnant Inj/Gen, `carrier_isProperForest` / `rep` / `selectedOuter_mem`).

## Note

The forward outer is closed to its irreducible geometric compatibility, verified in one chain to body-162.  The next
front is the `HEq` transports (`backward_choice_heq` / `forward_quotient_heq`), splitting the remaining round-trip
content into component/sector facts.  No declarations beyond this docstring anchor; the imports keep the map honest
against the source.  No facade, no flat term, no `forgetHopf`.
-/
