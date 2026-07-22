import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaParentReflectionAudit
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocStarOnForget
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRealSupportedW
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocInnerRawAggregate
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocInnerSourceSelector
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocInnerRawProper
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocInnerStarCorrectingPerm
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForgetInjOn
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaSaturatedCarrier
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaSaturatedConstructionRoot
import GaugeGeometry.QFT.HopfAlgebra.ResolvedCoproductIndex

/-!
# R-6c-body-554 — descending `touchedInnerStarTotal` through `forget` to a flat fresh-star assignment (PROVED)

Five-hundred-and-fifty-fourth genuine-body step — **Residual 1** of the Parent-divergence reflection (body-553, Step 5):
the explicit *flat descent* of the inner touched-star `touchedInnerStarTotal` through `forget`, and its freshness.  This is
a step of a **Parent-ELIMINATION** proof, so the RED-LINE holds throughout: **no `R`, `R.Core`, `Parent`, or
Parent-dependent Core appears in any signature or body**; in particular `innerRaw_isProperForest P Core` is **never**
called — the canonical `innerRaw`'s componentwise nonemptiness is replayed directly from the Parent-FREE
`canonicalLegSaturatedCarrierProperProvider.carrier_isProperForest`.

## Steps closed

* **Step 1–3 — the generic explicit-star descent engine** (parallels body-420/425, but keyed to an *arbitrary* component
  star `star : ResolvedFeynmanSubgraph G → VertexId` instead of `resolvedComponentFreshStar`):
  * `resolvedStarOnForgetOf` — the flat star `FeynmanSubgraph G.forget → VertexId`, defined on the component-membership
    branch via the unique preimage (extended by `dite`);
  * `resolvedStarOnForgetOf_spec` — `resolvedStarOnForgetOf A star B.forget = star B`, uniqueness of the preimage from
    `forget_injOn_elements` (which needs only **`HasNonemptyComponents`** — NO global `forget` injectivity, NO
    `IsProperForest`);
  * `resolvedStarOnForgetOf_isFreshStarAssignment` — the descended star is a fresh star assignment on `A.forget`, from the
    resolved-side freshness/injectivity + the spec.
* **Step 4 — raw touched-star freshness/injectivity** (re-key of body-450 with `M` **dropped**): the datum-explicit
  `touchedInnerStarTotal_fresh_raw` / `touchedInnerStarTotal_injOn_raw`, stated over the explicit
  `(Fstar) (z) (δ) (datum) (hE) (hL)` form (NO `ResolvedMultiStarDecontractionSupply`, NO `parentCD`, NO round-trip).
* **Step 5 — canonical `innerRaw` nonemptiness, PARENT-FREE**: `canonicalLegSaturated_innerRaw_hasNonemptyComponents`,
  the direct replay of body-378's `HasNonemptyComponents` conjunct via
  `canonicalLegSaturatedCarrierProperProvider.carrier_isProperForest` — **NO `Core`, NO `innerRaw_isProperForest`**.
* **Step 6 — the single canonical flat-star owner**: `canonicalLegSaturatedFlatTouchedInnerStar` (issued ONCE) + its
  `_spec` (Step 2 applied) + `_isFreshStarAssignment` (Step 3 applied, fed Step 4 + Step 5).  Body-555 reads this owner
  unchanged.

Route taken: the spec/fresh are **weakened to `HasNonemptyComponents`** (`forget_injOn_elements` accepts it), so the whole
descent is Parent-free with only Step 5's nonemptiness supply — full `IsProperForest` (which would drag in `Core`) is
never needed.

## Scoreboard

```text
resolvedStarOnForgetOf generic descent engine          PROVED (spec + fresh via HasNonemptyComponents)
canonical innerRaw HasNonemptyComponents               PARENT-FREE DERIVED (body-378 replay via carrier_isProperForest)
canonicalLegSaturatedFlatTouchedInnerStar owner        ISSUED ONCE (+ spec + fresh)
Residual 2 (flat quotient remainder = δ, body-555)     UNTOUCHED
new geometry                                           ZERO
circularity guard (no Parent-derived Core)             HELD
```

Per the HALT/guards: NO `R` / `R.Core` / `Parent` / Parent-dependent Core in any signature or body; NO
`innerRaw_isProperForest P Core`; Residual 2 UNTOUCHED; reflection NOT applied; no `parentDivergent` / `Parent` supply; NO
substitution of `resolvedComponentFreshStar` for `touchedInnerStarTotal`; NO whole-function strict star equality; NO global
`forget` injectivity; NO new class/structure/instance; body-420's private flat theorems untouched.  No facade, no
`sorry`/`admit`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000

/-! ## Step 1 — the generic explicit-star descent engine. -/

/-- **R-6c-body-554 (Step 1) — the generic descended star.**  For an arbitrary component star `star`, on a flat component
`η ∈ A.forget.elements` it returns `star` of `η`'s unique resolved preimage; off the forest it is irrelevant (`dite`).
This is the `resolvedComponentFreshStar`-agnostic generalisation of body-420's `resolvedStarOnForget`. -/
noncomputable def resolvedStarOnForgetOf {G : ResolvedFeynmanGraph} (A : ResolvedAdmissibleSubgraph G)
    (star : ResolvedFeynmanSubgraph G → VertexId) (η : FeynmanSubgraph G.forget) : VertexId :=
  if h : η ∈ A.forget.elements then star (Finset.mem_image.mp h).choose else 0

/-! ## Step 2 — the unique-preimage spec. -/

/-- **R-6c-body-554 (Step 2) — the core spec.**  On a forgotten component `B.forget` the descended star is exactly
`star B` — the preimage is pinned by `forget_injOn_elements` (which needs only `HasNonemptyComponents`, NOT a global
`forget` injectivity). -/
theorem resolvedStarOnForgetOf_spec {G : ResolvedFeynmanGraph} (A : ResolvedAdmissibleSubgraph G)
    (star : ResolvedFeynmanSubgraph G → VertexId) (hne : A.HasNonemptyComponents)
    {B : ResolvedFeynmanSubgraph G} (hB : B ∈ A.elements) :
    resolvedStarOnForgetOf A star B.forget = star B := by
  have hmem : B.forget ∈ A.forget.elements := by
    rw [ResolvedAdmissibleSubgraph.forget_elements]; exact Finset.mem_image_of_mem _ hB
  rw [resolvedStarOnForgetOf, dif_pos hmem]
  congr 1
  obtain ⟨hchoose_mem, hchoose_eq⟩ := (Finset.mem_image.mp hmem).choose_spec
  exact A.forget_injOn_elements hne hchoose_mem hB hchoose_eq

/-! ## Step 3 — the generic freshness descent. -/

/-- **R-6c-body-554 (Step 3) — the descended star is a fresh star assignment on `A.forget`.**  From the resolved-side
freshness `hFresh` + injectivity `hInj` and the Step-2 spec.  `HasNonemptyComponents` is the only structural input. -/
theorem resolvedStarOnForgetOf_isFreshStarAssignment {G : ResolvedFeynmanGraph}
    (A : ResolvedAdmissibleSubgraph G) (star : ResolvedFeynmanSubgraph G → VertexId)
    (hne : A.HasNonemptyComponents)
    (hFresh : ∀ B ∈ A.elements, star B ∉ G.vertices)
    (hInj : ∀ B₁ ∈ A.elements, ∀ B₂ ∈ A.elements, star B₁ = star B₂ → B₁ = B₂) :
    A.forget.IsFreshStarAssignment (resolvedStarOnForgetOf A star) := by
  refine ⟨fun η hη => ?_, fun η₁ hη₁ η₂ hη₂ hstar => ?_⟩
  · obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hη
    rw [resolvedStarOnForgetOf_spec A star hne hB]
    exact hFresh B hB
  · obtain ⟨B₁, hB₁, rfl⟩ := Finset.mem_image.mp hη₁
    obtain ⟨B₂, hB₂, rfl⟩ := Finset.mem_image.mp hη₂
    rw [resolvedStarOnForgetOf_spec A star hne hB₁,
      resolvedStarOnForgetOf_spec A star hne hB₂] at hstar
    exact congrArg _ (hInj B₁ hB₁ B₂ hB₂ hstar)

/-! ## Step 4 — the raw touched-star freshness/injectivity (re-key of body-450, `M` dropped). -/

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-body-554 (Step 4a) — the touched inner star avoids the parent's vertices (raw, NO `M`).**  Re-key of body-450's
`touchedInnerStar_fresh` with `M.parent z δ` replaced by the explicit `localizedParentWithTouchedLegs z δ datum hE hL` and
`M.legLift`/`M.hE`/`M.hL` by the explicit `datum`/`hE`/`hL`.  Route: `touchedInnerStarTotal_of_mem` → `touchedInnerStar` →
outer `starOf_fresh` + parent-vertices-subset. -/
theorem touchedInnerStarTotal_fresh_raw (Fstar : ResolvedCanonicalStarFacts D)
    (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
    (datum : ResolvedTouchedLegLiftDatum z δ)
    (hE : ∀ e ∈ G.internalEdges, e.source ∈ G.vertices ∧ e.target ∈ G.vertices)
    (hL : ∀ ℓ ∈ G.externalLegs, ℓ.attachedTo ∈ G.vertices) :
    ∀ B ∈ (innerRaw z δ datum hE hL).elements,
      touchedInnerStarTotal z δ datum hE hL B
        ∉ (localizedParentWithTouchedLegs z δ datum hE hL).toResolvedFeynmanGraph.vertices := by
  intro B hB
  rw [touchedInnerStarTotal_of_mem z δ datum hE hL B hB, touchedInnerStar]
  intro hmem
  have hmemG : D.starOf G z.1.1 (innerSource z δ datum hE hL ⟨B, hB⟩).1 ∈ G.vertices :=
    (localizedParentWithTouchedLegs z δ datum hE hL).vertices_subset hmem
  exact Fstar.starOf_fresh G z.1.1 (innerSource z δ datum hE hL ⟨B, hB⟩).1
    (mem_touchedOuterComponents.mp (innerSource z δ datum hE hL ⟨B, hB⟩).2).1 hmemG

/-- **R-6c-body-554 (Step 4b) — the touched inner star is injective on the inner forest (raw, NO `M`).**  Re-key of
body-450's `touchedInnerStar_injOn`.  Route: outer `starOf_injective` → `innerSource_spec`. -/
theorem touchedInnerStarTotal_injOn_raw (Fstar : ResolvedCanonicalStarFacts D)
    (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
    (datum : ResolvedTouchedLegLiftDatum z δ)
    (hE : ∀ e ∈ G.internalEdges, e.source ∈ G.vertices ∧ e.target ∈ G.vertices)
    (hL : ∀ ℓ ∈ G.externalLegs, ℓ.attachedTo ∈ G.vertices) :
    ∀ B₁ ∈ (innerRaw z δ datum hE hL).elements,
    ∀ B₂ ∈ (innerRaw z δ datum hE hL).elements,
      touchedInnerStarTotal z δ datum hE hL B₁ = touchedInnerStarTotal z δ datum hE hL B₂ → B₁ = B₂ := by
  intro B₁ hB₁ B₂ hB₂ heq
  rw [touchedInnerStarTotal_of_mem z δ datum hE hL B₁ hB₁, touchedInnerStar,
    touchedInnerStarTotal_of_mem z δ datum hE hL B₂ hB₂, touchedInnerStar] at heq
  set src₁ := innerSource z δ datum hE hL ⟨B₁, hB₁⟩ with hs₁
  set src₂ := innerSource z δ datum hE hL ⟨B₂, hB₂⟩ with hs₂
  have hsrc : src₁ = src₂ :=
    Subtype.ext (Fstar.starOf_injective G z.1.1 (η := src₁.1) (δ := src₂.1)
      (mem_touchedOuterComponents.mp src₁.2).1 (mem_touchedOuterComponents.mp src₂.2).1 heq)
  have h1 := innerSource_spec z δ datum hE hL ⟨B₁, hB₁⟩
  have h2 := innerSource_spec z δ datum hE hL ⟨B₂, hB₂⟩
  rw [← hs₁] at h1
  rw [← hs₂] at h2
  rw [hsrc] at h1
  exact h1.symm.trans h2

/-! ## Step 5 — canonical `innerRaw` nonemptiness, PARENT-FREE. -/

/-- **R-6c-body-554 (Step 5) — the canonical `innerRaw` has nonempty components, PARENT-FREE.**  ★Circularity RED-LINE:
this is the direct replay of body-378's `HasNonemptyComponents` conjunct on the canonical `innerRaw` datum, using ONLY the
Parent-FREE `canonicalLegSaturatedCarrierProperProvider.carrier_isProperForest` — `innerRaw_isProperForest`, `Core`, `R`,
`Parent` appear NOWHERE.★  Each inner component is `toInner A` for `A ∈ touchedOuterComponents`, whose vertices `= A.1`'s
(defeq), and `A.1 ∈ z.1.1.elements` inherits nonemptiness from the source carrier's proper-forest property. -/
theorem canonicalLegSaturated_innerRaw_hasNonemptyComponents {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalLegSaturatedCarrierProperSupply.toData G)
    (δ : {x : ResolvedFeynmanSubgraph
        (z.1.1.contractWithStars (canonicalLegSaturatedCarrierProperSupply.toData.starOf G z.1.1)) //
          x ∈ forestDomain z}) :
    (innerRaw z δ.1
      (touchedLegLiftDatum_of_complete z δ.1 (canonicalLegSaturated_touchedLegComplete z δ))
      (liveAmbient_edges_supported ambientSupportOfW'' z)
      (liveAmbient_legs_supported ambientSupportOfW'' z)).HasNonemptyComponents := by
  intro γ hγ
  rw [innerRaw_elements] at hγ
  obtain ⟨A, -, rfl⟩ := Finset.mem_image.mp hγ
  show 0 < A.1.vertexCount
  exact (canonicalLegSaturatedCarrierProperProvider.carrier_isProperForest G z.1.1 z.1.2).2.1
    A.1 (mem_touchedOuterComponents.mp A.2).1

/-! ## Step 6 — the single canonical flat-star owner. -/

/-- **R-6c-body-554 (Step 6) ∎ — the canonical flat touched-inner star.**  The Residual-1 flat descent of
`touchedInnerStarTotal` on the canonical `W″` parent's `.forget`, issued ONCE via the Step-1 engine.  Body-555 reads this
owner unchanged. -/
noncomputable def canonicalLegSaturatedFlatTouchedInnerStar {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalLegSaturatedCarrierProperSupply.toData G)
    (δ : {x : ResolvedFeynmanSubgraph
        (z.1.1.contractWithStars (canonicalLegSaturatedCarrierProperSupply.toData.starOf G z.1.1)) //
          x ∈ forestDomain z}) :=
  resolvedStarOnForgetOf
    (innerRaw z δ.1
      (touchedLegLiftDatum_of_complete z δ.1 (canonicalLegSaturated_touchedLegComplete z δ))
      (liveAmbient_edges_supported ambientSupportOfW'' z)
      (liveAmbient_legs_supported ambientSupportOfW'' z))
    (touchedInnerStarTotal z δ.1
      (touchedLegLiftDatum_of_complete z δ.1 (canonicalLegSaturated_touchedLegComplete z δ))
      (liveAmbient_edges_supported ambientSupportOfW'' z)
      (liveAmbient_legs_supported ambientSupportOfW'' z))

/-- **R-6c-body-554 (Step 6) — the canonical owner's spec** (Step 2 applied, fed Step 5's Parent-free nonemptiness). -/
theorem canonicalLegSaturatedFlatTouchedInnerStar_spec {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalLegSaturatedCarrierProperSupply.toData G)
    (δ : {x : ResolvedFeynmanSubgraph
        (z.1.1.contractWithStars (canonicalLegSaturatedCarrierProperSupply.toData.starOf G z.1.1)) //
          x ∈ forestDomain z})
    {B : ResolvedFeynmanSubgraph (localizedParentWithTouchedLegs z δ.1
        (touchedLegLiftDatum_of_complete z δ.1 (canonicalLegSaturated_touchedLegComplete z δ))
        (liveAmbient_edges_supported ambientSupportOfW'' z)
        (liveAmbient_legs_supported ambientSupportOfW'' z)).toResolvedFeynmanGraph}
    (hB : B ∈ (innerRaw z δ.1
        (touchedLegLiftDatum_of_complete z δ.1 (canonicalLegSaturated_touchedLegComplete z δ))
        (liveAmbient_edges_supported ambientSupportOfW'' z)
        (liveAmbient_legs_supported ambientSupportOfW'' z)).elements) :
    canonicalLegSaturatedFlatTouchedInnerStar z δ B.forget
      = touchedInnerStarTotal z δ.1
          (touchedLegLiftDatum_of_complete z δ.1 (canonicalLegSaturated_touchedLegComplete z δ))
          (liveAmbient_edges_supported ambientSupportOfW'' z)
          (liveAmbient_legs_supported ambientSupportOfW'' z) B :=
  resolvedStarOnForgetOf_spec _ _ (canonicalLegSaturated_innerRaw_hasNonemptyComponents z δ) hB

/-- **R-6c-body-554 (Step 6) ∎ — the canonical owner is a fresh star assignment on the parent's `.forget`** (Step 3
applied, fed Step 4's raw freshness/injectivity + Step 5's Parent-free nonemptiness).  ★No `Parent`, no `Core`.★ -/
theorem canonicalLegSaturatedFlatTouchedInnerStar_isFreshStarAssignment {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalLegSaturatedCarrierProperSupply.toData G)
    (δ : {x : ResolvedFeynmanSubgraph
        (z.1.1.contractWithStars (canonicalLegSaturatedCarrierProperSupply.toData.starOf G z.1.1)) //
          x ∈ forestDomain z}) :
    (innerRaw z δ.1
        (touchedLegLiftDatum_of_complete z δ.1 (canonicalLegSaturated_touchedLegComplete z δ))
        (liveAmbient_edges_supported ambientSupportOfW'' z)
        (liveAmbient_legs_supported ambientSupportOfW'' z)).forget.IsFreshStarAssignment
      (canonicalLegSaturatedFlatTouchedInnerStar z δ) :=
  resolvedStarOnForgetOf_isFreshStarAssignment _ _
    (canonicalLegSaturated_innerRaw_hasNonemptyComponents z δ)
    (touchedInnerStarTotal_fresh_raw canonicalLegSaturatedStarFacts z δ.1
      (touchedLegLiftDatum_of_complete z δ.1 (canonicalLegSaturated_touchedLegComplete z δ))
      (liveAmbient_edges_supported ambientSupportOfW'' z)
      (liveAmbient_legs_supported ambientSupportOfW'' z))
    (touchedInnerStarTotal_injOn_raw canonicalLegSaturatedStarFacts z δ.1
      (touchedLegLiftDatum_of_complete z δ.1 (canonicalLegSaturated_touchedLegComplete z δ))
      (liveAmbient_edges_supported ambientSupportOfW'' z)
      (liveAmbient_legs_supported ambientSupportOfW'' z))

end GaugeGeometry.QFT.Combinatorial
