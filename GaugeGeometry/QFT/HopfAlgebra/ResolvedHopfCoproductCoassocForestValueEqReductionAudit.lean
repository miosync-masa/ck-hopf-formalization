import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocMemSupplyReplumb
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestValueEqValue
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestTagAgreesFloor

/-!
# R-6c-body-314 — forest_value_eq reduction audit: no `remnantClass`; it bottoms out at `forestTag_agrees` (verdict C)

Three-hundred-and-fourteenth genuine-body step — a `forestTag`-construction judgment scout (no new geometry), centered on
whether the last round-trip identity leaf `forest_value_eq` (body-285) can be discharged by CONSTRUCTING the opaque
`forestTag` (body-282) from a generic de-contraction class `remnantClass`.  Verdict **C**: no such `remnantClass` exists,
and `forest_value_eq` is ALREADY reduced (body-288 `ForestValueEqValue.lean`) to the single honest concrete-model
coherence datum `forestTag_agrees` (body-295 floor).  Imports body-288/295 so the pin stays honest against the source.

## Why the `remnantClass` construction cannot be written (verdict C)

* **No `remnantClass : δ → ForestIdx`.**  A dir-wide grep finds NO `remnantClass` producing a `ForestIdx`; the only
  `remnantClass*` identifier is `remnantClass_eq` (RemnantDecontraction.lean:52-53), a **`ResolvedClass` equality**
  `(remnantComponent o).toResolvedFeynmanGraph.toResolvedClass = o.contractedSourceGraph.toResolvedClass` — wrong type
  (a class, not a `ForestIdx`/`B`) and keyed on an occurrence `o` (which already carries `B`), not on a bare quotient δ.
* **`remnantComponent` runs the wrong direction.**  `remnantComponent : ForestChoiceOccurrence → ResolvedFeynmanSubgraph
  s.selectedOuterContractGraph` (Remnant.lean:75-76): occurrence → quotient subgraph, NOT δ → `ForestIdx`.
* **The region core keeps no `B`.**  `componentToForest : {x // x ∈ forestDomain z} → ResolvedFeynmanSubgraph G`
  (RegionConstructionFromSector.lean:108-109) with `forestDomain z = z.2.1.elements.filter (¬ Disjoint · (starOfZ z))` —
  a bare star-touching quotient subgraph with no index/occurrence for generic `z`.  So `forestTag z γ := transport
  (remnantClass δ)` is unwritable, and `forestTag z γ := B` is not even well-defined (no `componentToForest` injectivity).
* Body-295 (`ForestTagAgreesFloor.lean:19-43`) already recorded this: enriching the core with a region-side
  `componentToForestOccurrence` + B-uniqueness **relocates but does not eliminate** `forestTag_agrees` — the generic-`z`
  region `B` is an INDEPENDENT de-contraction datum, not definitionally the `choiceAt`-sourced `forestTag_fwd_value`.

## `forest_value_eq` is ALREADY reduced (no fresh proof needed)

`forest_value_eq` (ForestValueEqValue.lean:112-126, body-288) is PROVED from `ResolvedForestValueEqValueSupply`
(`:96-105`) whose only fields are `Data : ResolvedRecoveredPreimageValueMemSupply F V` (body-283, now inhabited by
body-313) and the single coherence leaf
```text
forestTag_agrees : forestTag (fwd q) ⟨γ.1, hu⟩ hmem = forestTag_fwd_value q γ hmem   (:101-105)
```
The forward-image half is proved: `forestTag_fwd_value` (`:77`, `= occurrence.B`) and `forest_choiceAt_eq_value`
(`:85-90`, via body-200's `heq_transport_choice`), so `forest_value_eq` follows by `Sum.inr.inj` (`:126`).  The sole
residual is `forestTag_agrees` — the opaque model `forestTag` agreeing with the `choiceAt`-recovered `B` on forward images.

## `forestTag_agrees` is a concrete-model coherence datum — the SECOND (and last) model obligation

`forestTag_agrees` is NOT a false-in-general obstruction (unlike the retired floor-297/298): it holds whenever the
concrete model's `forestTag` is defined via the actual de-contraction tag — a legitimate coherence the canonical model
discharges, exactly the tier of the carrier closure `recovered_raw_mem` (body-159/`ParametricCarrierClosure.lean:111`).
`B` being `choiceAt`-sourced and forward-image-only (body-295) is precisely why it is a supplied datum, not a `rfl`.

## The consolidated reduction (what the outer-mixing inverse now rests on)

```text
ResolvedOuterMixingValueInverseSupply (body-308)
  ⟸ ResolvedRecoveredPreimageValueRoundTripLeafSupply (body-285)
      ├ forward_outer_value      — PROVED (body-289, ForwardOuterValue.lean:175)
      ├ forward_quotient_value   — PROVED (body-290, ForwardQuotientValue.lean:100)
      ├ forest_value_eq          — reduced to  forestTag_agrees   (body-288/295)      ← model datum #2
      └ Data (body-283)          — inhabited (body-313) modulo  recovered_raw_mem     ← model datum #1
```
So the entire round-trip layer — hence the raw outer-mixing bijection inverse — bottoms out at exactly **TWO** honest
concrete-model coherence data: `recovered_raw_mem` (carrier closure, Group-3) and `forestTag_agrees` (tag coherence,
body-295 floor).  Both are discharged by the concrete canonical carrier/tag model; neither is a proof-shape or geometry
residual.

Per the HALT: this is a construction-judgment pin — verdict C + the reduction consolidation are recorded; no `remnantClass`
is built (it does not exist), `forest_value_eq` is not re-proved (already reduced), and `forestTag_agrees` /
`recovered_raw_mem` are NOT claimed proved; no facade, no flat term, no `forgetHopf`.
-/
