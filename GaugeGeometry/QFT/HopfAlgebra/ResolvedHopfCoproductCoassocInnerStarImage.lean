import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecontractSection

/-!
# R-6c-body-354 — the inner-forest star image = touched-outer-forest star image (PROVED)

Three-hundred-and-fifty-fourth genuine-body step — the star-image half of the re-contract vertex section
(body-353's residual, layer 1).  The image of `innerRaw`'s components under the explicit star
`touchedInnerStarTotal` equals the image of the touched outer components under the ORIGINAL star
`D.starOf G z.1.1` — the `starVertices` half of the `contractWithStars` vertex formula, banked before the
vertex membership identity.

Both inclusions are the `innerSource`/`toInner` round-trip (bodies 350) + `touchedInnerStarTotal_of_mem`
(body-351): an inner star is `D.starOf` of its `innerSource`; a touched star is the `touchedInnerStarTotal`
of its `toInner` (via `innerSource_toInner`).

Landed axiom-clean: `innerRaw_starVertices_eq_touched`.

## The residual vertex identity (body-355)

With this and body-351 (`innerRaw.vertices = touchedOuterForest.vertices`), the `contractWithStars` vertex
formula gives

```text
(innerRaw.contractWithStars touchedInnerStarTotal).vertices
  = (parentGraph.vertices \ touchedOuterForest.vertices) ∪ touchedOuterForest.starVertices (D.starOf G z.1.1)
```

so `recontract_innerRaw_vertices` reduces to the M1-localization vertex identity `… = δ.vertices` — the custom
parent's surviving (edge/leg preimage) vertices are `δ`'s non-star vertices and the touched stars are `δ`'s
stars.  That is the last, membership-level pipe (next body); this body banks the star image.

Per the HALT: only the star image equality is proved; the vertex membership identity + the remnant round-trip
are next; `innerStar_agrees` and the hardcoded `D.starOf parent innerRaw` are NOT used; no forward quotient /
global forward round-trip.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` /
singleton / floor-297.
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

/-- **R-6c-body-354 — the inner star image equals the touched star image.** -/
theorem innerRaw_starVertices_eq_touched :
    (innerRaw z δ datum hE hL).starVertices (touchedInnerStarTotal z δ datum hE hL)
      = (touchedOuterForest z δ).starVertices (D.starOf G z.1.1) := by
  ext s
  rw [ResolvedAdmissibleSubgraph.mem_starVertices, ResolvedAdmissibleSubgraph.mem_starVertices]
  constructor
  · rintro ⟨B, hB, rfl⟩
    refine ⟨(innerSource z δ datum hE hL ⟨B, hB⟩).1, ?_, ?_⟩
    · rw [touchedOuterForest_elements]; exact (innerSource z δ datum hE hL ⟨B, hB⟩).2
    · rw [touchedInnerStarTotal_of_mem z δ datum hE hL B hB, touchedInnerStar]
  · rintro ⟨A, hA, rfl⟩
    rw [touchedOuterForest_elements] at hA
    have hmem : toInner z δ datum hE hL ⟨A, hA⟩ ∈ (innerRaw z δ datum hE hL).elements := by
      rw [innerRaw_elements]; exact Finset.mem_image.mpr ⟨⟨A, hA⟩, Finset.mem_attach _ _, rfl⟩
    refine ⟨toInner z δ datum hE hL ⟨A, hA⟩, hmem, ?_⟩
    rw [touchedInnerStarTotal_of_mem z δ datum hE hL _ hmem]
    show D.starOf G z.1.1 (innerSource z δ datum hE hL ⟨toInner z δ datum hE hL ⟨A, hA⟩, hmem⟩).1
      = D.starOf G z.1.1 A
    rw [innerSource_toInner z δ datum hE hL ⟨A, hA⟩]

end GaugeGeometry.QFT.Combinatorial
