import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestValueEqScout
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecoveredQuotientRoundTrip

/-!
# R-6c-body-197 — forward quotient recovery scout: `forestTag_forward_eq` and `forward_quotient_heq` are DUAL

Hundred-and-ninety-seventh genuine-body step, a scout of whether the two remaining round-trip value leaves —
`forestTag_forward_eq` (body-196) and `forward_quotient_heq` (body-165) — share a common root.  The audit's verdict:
**they are dual (opposite-direction) siblings, not the same geometry**; they should be attacked separately, but they
share one deep engine — the remnant de-contraction.  This map records that so no effort is wasted forcing a common
provider.

## The two leaves are dual siblings of body-160

Body-160's `ResolvedRoundTripComponentPartitionSupply` pairs each `HEq` with its (proved) outer element-partition —
one per bijection direction:

| direction | outer `Eq` (proved) | the `HEq` | value part |
|---|---|---|---|
| **domain `q`** | `recoveredOuter_partition` | `backward_choice_heq` | `choice_component_eq` → **`forestTag_forward_eq`** (`inr` tag) |
| **codomain `z`** | `selectedOuter_partition` | **`forward_quotient_heq`** | `quotientForest = survivor ⊔ remnant` |

* `forestTag_forward_eq` is the forest/remnant **value-part of `backward_choice_heq`** (the *domain* round-trip `q ↦
  fwdMap q ↦ recoverChoice`), a homogeneous `Eq` of `ForestIdx`;
* `forward_quotient_heq` is the *codomain* round-trip `z ↦ ⟨unionOuter z, recoverChoice z⟩ ↦ quotientForest`, a
  heterogeneous `HEq` of `ForestIdx` over two `contractWithStars` graphs.

So `forestTag_forward_eq` is **not** the shadow of `forward_quotient_heq`; it is the shadow of its *dual*,
`backward_choice_heq`.  They are mirror images across the bijection — different directions, different types (`Eq`
vs `HEq`), consumed at different `Sigma.ext` positions.

## The shared deep engine (but not a shared leaf)

Both rest on the **remnant de-contraction round-trip**: `remnantComponent` / `remnantGen` (body-126), the
`componentToForest` / `promote` de-contraction and `promoted_eq_forestRecovered` (bodies 156/183/189), and the
survivor twin `rightSurvivorForest` / `survivorGen` (body-125).  `S.quotientForest q = rightSurvivorForest q ⊔
remnantForest q` (body-129 `union_eq`), and `z.2`'s components split into star-avoiding survivors (`inl false`) and
star-touching remnants (`inr`) — the same partition on both sides.  A single "remnant recovery" fact could feed the
*forest/remnant halves* of both directions, but the two consumers differ (a `Sum`-valued choice function vs a
`ForestIdx` quotient), so a common provider captures only the remnant kernel, never the whole leaf.

## Verdict and plan

* **Not unifiable into one provider.**  Attack the two leaves separately.
* **Lighter first: `forestTag_forward_eq`** (homogeneous `ForestIdx` `Eq`).  Minimal fields: `remnantGen` /
  `remnantComponent` (body-126, the `inr` de-contraction), the `forestRecovered` / `componentToForest` inverse
  (bodies 156/183) linking `forestTag_fwd` to the original `q.2 γ = inr B`, a `Subtype.ext` on `ForestIdx = {A // A
  ∈ carrier}`, and the already-reusable body-188 tag pinning.
* **Heavier second: `forward_quotient_heq`** — the full `union_eq` reconstruction (`quotientForest = survivor ⊔
  remnant`) plus a dependent `HEq` transport across the contract-graph equality; the same remnant kernel is its hard
  half.

Per the HALT: no leaf is proved; the remnant-de-contraction engine is identified but not entered; the dual relation
and the separate-attack plan are recorded.

This is a documentation / scout anchor (like bodies 187/191/195); the imports keep the map honest against the
source.  No declarations beyond this docstring.  No facade, no flat term, no `forgetHopf`.
-/
