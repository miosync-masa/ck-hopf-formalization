import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocInnerStarCoherence

/-!
# R-6c-body-350 — the inner-source selector: `innerRaw` component ↦ its touched outer source (PROVED)

Three-hundred-and-fiftieth genuine-body step — the selector foundation for the explicit-star re-contract
section (body-349's layer 1).  Since `(innerRaw z δ …).elements = image (toInner z δ …)` over the touched
outer components (body-328) and `toInner` is injective (body-327), each inner-forest component `B` has a UNIQUE
touched outer source `innerSource B` with `toInner (innerSource B) = B`.  This is the exact mirror of body-333's
`forestSource`, one level in.

Landed axiom-clean:

* `innerSource` — the touched outer component whose `toInner` is `B`;
* `innerSource_spec` — `toInner (innerSource B) = B.1`;
* `innerSource_toInner` — `innerSource ⟨toInner A, _⟩ = A` (uniqueness via `toInner_injective`).

## Audit of the explicit-star data section (body-351 layer 1)

With `innerSource` the explicit star map is `touchedInnerStar B := D.starOf G z.1.1 (innerSource B).1` — the
ORIGINAL star of `B`'s touched outer source, evaluated through the selector (NO `innerStar_agrees`).  The
mechanical section is then the THREE graph-data equalities

```text
(innerRaw.contractWithStars touchedInnerStar).vertices      = δ.1.vertices        -- parent vertex section + touched stars
                                       … .internalEdges      = δ.1.internalEdges   -- innerRaw complement + quotientEdgePreimage_map
                                       … .externalLegs       = δ.1.externalLegs    -- legLift.map_eq
```

whose right sides are `δ.1`'s data (`= touchedLocalComponent z δ.1`'s data, which is `δ`'s by
`touchedLocalComponent_vertices`/`…` rfl, body-321).  These are the M1-localization inverse at the data level;
each needs the corresponding `contractWithStars` unfolding and the M1 primitive, and NONE uses
`innerStar_agrees` (that is consumed only in body-351 to swap the hardcoded `D.starOf parent innerRaw` for
`touchedInnerStar`).  Verdict: the selector is the last reusable piece before the three data equalities; those
are mechanical M1-inverse proofs (next body), the star coherence stays the sole datum.

Per the HALT: only the selector + its round-trip are proved; the three explicit-star data equalities and the
remnant round-trip are next; `innerStar_agrees` is NOT used here; no forward quotient / global forward
round-trip; the six bridge gates are not touched.  No facade, no flat term, no `forgetHopf`, no rep/perm, and
NO `promote_collapse` / singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}
  (z : ForestBlockCodType D G)
  (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
  (datum : ResolvedTouchedLegLiftDatum z δ)
  (hE : ∀ e ∈ G.internalEdges, e.source ∈ G.vertices ∧ e.target ∈ G.vertices)
  (hL : ∀ ℓ ∈ G.externalLegs, ℓ.attachedTo ∈ G.vertices)

set_option linter.unusedSectionVars false

/-- **R-6c-body-350 — the touched outer source of an inner-forest component.**  Mirrors body-333's
`forestSource`, one level in: `innerRaw.elements = image toInner`, so `B`'s preimage is chosen. -/
noncomputable def innerSource
    (B : {x : ResolvedFeynmanSubgraph (localizedParentWithTouchedLegs z δ datum hE hL).toResolvedFeynmanGraph //
      x ∈ (innerRaw z δ datum hE hL).elements}) :
    {x : ResolvedFeynmanSubgraph G // x ∈ touchedOuterComponents z δ} :=
  (Finset.mem_image.mp (by rw [← innerRaw_elements z δ datum hE hL]; exact B.2)).choose

/-- **R-6c-body-350 — the source's `toInner` is `B`.** -/
theorem innerSource_spec
    (B : {x : ResolvedFeynmanSubgraph (localizedParentWithTouchedLegs z δ datum hE hL).toResolvedFeynmanGraph //
      x ∈ (innerRaw z δ datum hE hL).elements}) :
    toInner z δ datum hE hL (innerSource z δ datum hE hL B) = B.1 :=
  (Finset.mem_image.mp (by rw [← innerRaw_elements z δ datum hE hL]; exact B.2)).choose_spec.2

/-- **R-6c-body-350 — the source of `toInner A` is `A`** (uniqueness via `toInner_injective`). -/
theorem innerSource_toInner (A : {x : ResolvedFeynmanSubgraph G // x ∈ touchedOuterComponents z δ})
    (hmem : toInner z δ datum hE hL A ∈ (innerRaw z δ datum hE hL).elements) :
    innerSource z δ datum hE hL ⟨toInner z δ datum hE hL A, hmem⟩ = A :=
  toInner_injective z δ datum hE hL (innerSource_spec z δ datum hE hL ⟨toInner z δ datum hE hL A, hmem⟩)

/-- **R-6c-body-350 — the explicit re-contract star map.**  The ORIGINAL star of `B`'s touched outer source,
via the selector — the star map the mechanical section (body-351) proves the re-contract against (NO
`innerStar_agrees`). -/
noncomputable def touchedInnerStar
    (B : {x : ResolvedFeynmanSubgraph (localizedParentWithTouchedLegs z δ datum hE hL).toResolvedFeynmanGraph //
      x ∈ (innerRaw z δ datum hE hL).elements}) : VertexId :=
  D.starOf G z.1.1 (innerSource z δ datum hE hL B).1

end GaugeGeometry.QFT.Combinatorial
