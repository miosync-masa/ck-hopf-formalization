import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestValueEqReductionAudit
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForwardOuterValue
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForwardQuotientValue

/-!
# R-6c-body-315 — round-trip concrete-inhabitability audit: the forward identities need a NEW multi-component
# de-contraction law (the "2 model data" of body-314 was premature)

Three-hundred-and-fifteenth genuine-body step — a concrete-inhabitability audit (NOT an assembly scout) of the round-trip
leaf supply (body-285), applying the "proved theorem ≠ concretely inhabitable supply" distinction.  It corrects the
body-314 consolidation: `forward_outer_value` / `forward_quotient_value` (bodies 289/290) are theorems PROVED FROM
supplies whose fields are the retired floor-297 family, so they are NOT free — the raw outer-mixing inverse's genuine
outstanding obligation is a **multi-component de-contraction / promotion law that does not yet exist**.  Imports body-289/
290/314 so the audit stays honest against the source.

## The "free because proved" trap (correction to body-314)

Body-314 listed `forward_outer_value` (289) / `forward_quotient_value` (290) as PROVED, hence the inverse "bottoms out at
two model data."  But those proofs CONSUME supplies:

* `ResolvedForwardOuterValueGeometrySupply` (ForwardOuterValue.lean:54-71) has field
  `forestComponentMem : γ ∈ (…forestRecovered z).elements → γ ∈ z.1.1.elements` (`:63-66`) — since
  `forestRecovered z = image (componentToForest z)`, this is **verbatim the retired floor-297** (`componentToForest z δ ∈
  z.1.1.elements`, GeometryFloorAssembly.lean:74-76), **FALSE at a multi-star orphan** (body-306): a δ spanning ≥2 stars
  has no single parent in `z.1.1.elements`.
* Field `promote_collapse : (promote γ (forestTag z γ h).1).elements = {γ.1}` (`:58-62`) is a **singleton** collapse.
  `promote_elements : (promote γ B).elements = B.elements.image (γ.promote ·)` (ResolvedSubgraphPromote.lean:129-132) —
  a multi-component `B` yields `|B.elements|` components, NOT `{γ}`.  So the singleton is **false for a multi-component
  tag** (body-188 scout: it holds iff each `Bᵧ` is the whole-component one-piece forest).
* `ResolvedForwardQuotientValueGeometrySupply` (ForwardQuotientValue.lean:53-72) has field
  `Geom : ResolvedForwardOuterValueGeometrySupply` (`:56`) — **chained-uninhabitable exactly when 289 is** — plus
  `survivor_mem_value` / `remnant_mem_value` waiting on a concrete `V`.

Both forward fields in the round-trip supply are quantified over **generic z** (RecoveredPreimageValueRoundTrip.lean:
58-62), so orphans are IN SCOPE — they genuinely must be satisfied (the inverse's `forward` field is the right-inverse on
the FULL `forestBlockCodFinset`, orphans included).  Option "only needed at fwd-q" is refuted by the source.

## The identities are TRUE — but need a new proof route

`forward_outer_value : selectedOuterRawOf (recoveredPreimageValue z) = z.1.1` is a TRUE statement at orphans (body-307
verdict B: real CK coassociativity holds, the total outer-mixing bijection `forestBlockDomFinset ↔ forestBlockCodFinset`
EXISTS via outer-MIXING — the outer `A` is NOT preserved, so per-component domain choices assemble into a multi-star
`B`).  It is **false only along the singleton region-core route** (289's `forestComponentMem` + `promote_collapse`).  This
is a proof-route defect, not a false theorem.

## The TRUE geometry root (does not yet exist)

The current `componentToForest : {x // x ∈ forestDomain z} → ResolvedFeynmanSubgraph G`
(RegionConstructionValue.lean:60) is **single-valued**, and `promote_collapse` FORCES single-piece tags — the geometry
cannot express a δ spanning several parents.  The real root is a **multi-component de-contraction / promotion law**:

```text
a multi-valued de-contraction  δ ↦ Finset (parents ⊆ z.1.1.elements)   (or a forest-collection adjunction)
such that promoting the recovered forest over the collection reassembles z.1.1 —
  promote / contractWithStars as inverse operations at the COLLECTION level.
```

The forward primitive already emits collections (`promote_elements`, ResolvedSubgraphPromote.lean:129-132:
`(promote γ B).elements = B.elements.image (γ.promote ·)`).  But NO inverse/collection-level law exists — a dir-wide
search finds only the forward `promote`, the singleton scouts, and forward-only recovery.  This missing law — NOT
bodies 289/290 — is the real outstanding geometry obligation, and it is precisely the outer mixing of body-307.

## The corrected inhabitability table

```text
dependency                         theorem-level        faithful-model inhabitability
--------------------------------   ------------------   ------------------------------------------
mixed_ne_pR (310)                  reduction proved     valid  (consumes forward_outer — inherits its route defect)
mixed_ne_pL (311)                  reduction proved     valid  (consumes forward_quotient — inherits its route defect)
forest_nonempty (312)              PROVED leaf          valid  (orphan-harmless; floor-297 untouched)
forestTag_agrees (295)             field (288)          model-coherence  (forward-image; concrete tag model)
recovered_raw_mem                  field in Data        carrier-closure  (canonical ResolvedProperForestFiniteCover)
forestComponentMem (289)           field                FALSE — RETIRE  (verbatim floor-297)
promote_collapse singleton (289)   field                multi-star-audit  (false for multi-component B)
represented_cases (289)            field                valid where witness exists (floor-298 converse; benign)
survivor/remnant dirs (293/294)    theorem ⟸ fields     concrete-V-pending  (star-partition; NOT gated on floor-297)
forward_outer_value (289)          theorem from supply  NEW-PROOF-REQUIRED  (true at orphans; 289 route dead)
forward_quotient_value (290)       theorem from supply  NEW-PROOF-REQUIRED  (Geom-chained to 289 + concrete-V-pending)
multi-component de-contraction     does not exist       NEW-PROOF-REQUIRED  (the true root = outer mixing, body-307)
```

## Corrected reduction — three fronts, not "two model data"

The raw outer-mixing inverse (body-308) rests on:
1. **The multi-component de-contraction / promotion law** (new geometry) — replaces 289's `forestComponentMem` +
   singleton `promote_collapse`, and re-proves `forward_outer_value` / `forward_quotient_value` at orphans.
2. **The concrete `V`** (`ResolvedConcreteSummandValueSupply`) — discharges survivor/remnant sound/complete (293/294),
   independent of the floor-297 defect (star-partition, well-defined at orphans).
3. **The two model data** — `recovered_raw_mem` (carrier closure) + `forestTag_agrees` (tag coherence).

Front 1 is the genuinely-new geometry the campaign must now build; it is NOT a Group-3 model datum and must NOT be
revived under a new name as one.

Per the HALT: this is an inhabitability-judgment pin — the table + the true root are recorded; no `remnantClass`, no
multi-component law is constructed here (it is the next front), floor-297 is NOT revived, multi-star `B` is NOT collapsed
to a singleton, and 289/290 are NOT counted free; no facade, no flat term, no `forgetHopf`.
-/
