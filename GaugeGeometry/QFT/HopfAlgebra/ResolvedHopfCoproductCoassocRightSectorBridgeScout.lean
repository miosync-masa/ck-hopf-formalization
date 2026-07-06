import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightRegionSectorBridge
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSurvivorElementsRecovery

/-!
# R-6c-body-210 — right sector bridge scout: `rightRecovered_forward_membership` and `survivor_mem` are DUAL, not shared

Two-hundred-and-tenth genuine-body step, a scout of whether the two right/survivor sector leaves — body-170's
`rightRecovered_forward_membership` and body-206's `survivor_mem` — can share one provider.  The audit's verdict:
**they are the two opposite halves of one right-sector round-trip, but genuinely different leaves at different graph
levels**; they cannot share a membership-bridge field and must be attacked separately.  This map records that, and
the reduction path for each, so no effort is wasted forcing a common provider.

## The two leaves are dual halves at different graph levels

```text
rightRecovered_forward_membership (body-170)   G-level, backward componentToRight
   γ ∈ rightRecovered (fwdMap q) ↔ rightPrimSelected q γ     (γ : ResolvedFeynmanSubgraph G)
   rightRecovered = ofElements (rightDomain.attach.image componentToRight),  componentToRight : δ ↦ G-parent

survivor_mem (body-206)                        quotient-level, forward survivorComponent
   x₁ ∈ rightSurvivorForest recovered ↔ x₂ ∈ rightDomain z   (x₁,x₂ : over contract-with-stars graphs, HEq-linked)
   rightSurvivorForest = ofElements (rightComponents.attach.image survivorComponent),  survivorComponent : γ ↦ reembed
```

`componentToRight` (backward, quotient → G) and `survivorComponent` (forward, G → quotient) are the two opposite
halves of ONE right-sector equivalence (whose inverse laws are `right_left_inv` / `right_right_inv`), but they are
**different maps applied at different endpoints, over different concrete graphs** (G-level parents vs quotient
reembeds).  So the two leaves **cannot share a single membership-bridge field**; only the *abstract* sector-index
bijection is shared, and each leaf transports it differently — that transport is the fresh content.

## The shared abstract asset (proved) and the two reductions

* **The right-sector inverse is already proved** at the sector-index level: `ResolvedSectorLeafBundle.right_left_inv`
  / `right_right_inv` (discharged in `SectorInverseConcrete` from `componentToRight_spec = Classical.choose_spec` +
  forward `right_injective`), equivalently `ResolvedRightSectorEquivSupply.rightEquiv : RightPrimitiveIndex D G s ≃
  (rightForest s).elements`.  This underlies body-170 but sits one layer above both leaves' concrete graphs.
* **`survivor_mem` reduces to a pure tag correspondence** (lighter): `survivorComponent = survivorReembed`, and
  `survivorReembed_toResolvedFeynmanGraph = rfl` (vertices/intrinsic graph preserved at `rfl`), so the `HEq x₁ x₂`
  forward direction is near-definitional; the only genuine obligation is
  `recoverChoice z γ = inl false ⟷ Disjoint γ.vertices (starOfZ z)` (right-primitive tag ⟷ star-avoiding).
* **`rightRecovered_forward_membership`** carries the G-level backward `componentToRight` round-trip in addition to
  the `rightPrimSelected ↔ isRightPrimitive` predicate bridge (both `= inl false`).

## Verdict and plan

* **Not unifiable into one provider** — different concrete graphs, opposite halves.  Attack separately.
* **Lighter first: `survivor_mem`** — reduce to the tag lemma `recoverChoice z γ = inl false ⟷ Disjoint γ.vertices
  (starOfZ z)`, using the `rfl`-level `survivorReembed` and the `rfl` element characterisations.
* **`rightRecovered_forward_membership` second** — via the proved right-sector inverse + the predicate bridge.
* The only genuinely shared asset is the abstract sector-index right inverse; reuse it as a lemma, keep the two
  membership bridges as separate providers.

Per the HALT: no leaf is proved; the sector inverse / tag correspondence bodies are not entered; the dual relation
and the separate-attack plan are recorded.

This is a documentation / scout anchor (like body-197).  The imports keep the map honest against the source.  No
declarations beyond this docstring.  No facade, no flat term, no `forgetHopf`.
-/
