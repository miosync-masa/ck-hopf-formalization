import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecoveredPreimageValueGeometryAssembly

/-!
# R-6c-body-292 — the abstract round-trip / global-HEq layer is closed (docs anchor)

Two-hundred-and-ninety-second genuine-body step, a documentation anchor (no new geometry).  It fixes the elimination of
the abstract `witnessSplit` round-trip and global heterogeneous-equality obligations from the canonical R-6c path —
the counterpart of the parametric-layer completion (body-271) and the construction-migration completion (body-287).
Imports body-291 so the map stays type-checked against the source.  Reader-facing narrative:
`CK_HOPF_FORMALIZATION_MAP.md` §"R-6c bodies 288–291"; proof-dependency map: `CK_HOPF_DEPENDENCY_GRAPH.md` §"R-6c bodies
288–291".

## The headline

```text
All abstract witnessSplit round-trip and global heterogeneous-equality
obligations have been eliminated from the canonical R-6c path.

The round-trip layer now depends only on six component-level geometry facts.
```

## The reduction chain (288–291)

```text
288 exact forest choice     → forestTag_agrees                                        (occurrence compatibility)
289 forward outer           → promote_collapse + forestComponentMem + represented_cases
290 forward quotient (HEq)  → survivor_mem_value + remnant_mem_value                   (generic S-free HEq transports)
291 six local facts         → three former global leaves → two whole round-trips → concrete cover → coassoc_gen
```

Generic S-free HEq transports reused: `heq_of_index_eq` (193), `heq_forestIdx` (203), `heq_of_membership_split` (204),
`heq_finset_of_mem_iff` (206), `heq_transport_choice` (200).  Body-290 reduces the quotient `HEq` WITHOUT circularity
(RHS = complementary star-filter partition; LHS = `V.union_eq`; graph transport = body-289's outer equality; never
`fwd q = z`).

## Two-layer status (the distinction matters)

```text
round-trip layer      exactly SIX component geometry leaves
complete theorem      those six + (inside Data) region sound/complete + carrier closure + F/V + base leaves
```

It is NOT "the whole theorem has six hypotheses" — it is the **round-trip geometry residual** that is six facts; the
model / carrier / base assumptions remain explicit and separate.  The six round-trip leaves:

```text
forestTag_agrees    forestTag = the occurrence-recovered index                        (288)
promote_collapse    (promote γ (forestTag …)).elements = {γ}                           (289, de-contraction singleton)
forestComponentMem  forest-recovered parent ∈ target outer A                           (289)
represented_cases   represented A-component ∈ forestRecovered                          (289)
survivor_mem_value  survivor ⟷ rightDomain  (tag-reducible: inl false ⟷ star-avoiding) (290)
remnant_mem_value   remnant  ⟷ forestDomain (genuine de-contraction)                   (290)
```

## Headline status

```text
proof-shape residual          none
migration residual            none
global HEq residual           none
abstract round-trip residual  none
round-trip geometry           six local component facts
model / base assumptions      explicit and separate
```

`coassoc_gen_of_local_value_geometry` (body-291) is the S-free top-level theorem over the six leaves + the base leaves.
Full unconditional resolved coassociativity remains unclaimed pending a phase-1b concrete model instance discharging the
six component leaves + the region / carrier model supplies — but the entire abstract round-trip / global-identity layer
is closed.

Per the HALT: this is a docstring anchor only; the import keeps the map honest against body-291.  No declarations beyond
this docstring; no facade, no flat term, no `forgetHopf`.
-/
