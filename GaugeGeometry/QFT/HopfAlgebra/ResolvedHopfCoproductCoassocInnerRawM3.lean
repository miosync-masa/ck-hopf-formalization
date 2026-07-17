import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocToInner

/-!
# R-6c-body-328 — `innerRaw` + M3: promote-to-touched-collection (PROVED, value-only)

Three-hundred-and-twenty-eighth genuine-body step — Front-1 M3, the collection-level law that REPLACES the retired
singleton `promote_collapse`.  `innerRaw` is the admissible forest of the custom localized parent whose components are the
`toInner`-retyped touched components; promoting it back recovers EXACTLY the touched collection (not a singleton).

## Banked here

* `innerRaw` — `ResolvedAdmissibleSubgraph.ofElements ((touchedOuterComponents z δ).attach.image (toInner …))` with CD from
  `toInner_isConnectedDivergent` (body-327) and pairwise from `toInner_disjoint` (body-327, via witnesses).
* `innerRaw_elements` — `(innerRaw …).elements = (touchedOuterComponents z δ).attach.image (toInner …)` (`rfl`).
* `promote_innerRaw_elements` (M3) — `(ResolvedAdmissibleSubgraph.promote (localizedParentWithTouchedLegs …)
  (innerRaw …)).elements = touchedOuterComponents z δ`, proved by two-inclusion `Finset.ext` + term-mode `mem_image` +
  `promote_toInner`.  This is the genuine multi-star de-contraction: `promote parent innerRaw` returns the touched
  COLLECTION `B.elements.image (parent.promote ·)`, and each `parent.promote (toInner A) = A` (body-327), so the image is
  exactly `touchedOuterComponents z δ`.

M3 is now a value-level theorem PROVED under the `legLift` datum (body-326).  The remaining Front-1 residuals are the two
concrete-model CK data (M2b parent CD, δ-leg-completeness = the `legLift` datum) and D4 (parent injectivity/disjointness,
still open).

Per the HALT: only `innerRaw` + `innerRaw_elements` + M3 are proved; `innerRaw` is NOT lifted to `ForestIdx`; no carrier
membership; no parent CD used; the equality is on `.elements` only (NOT full-forest equality); D4 is NOT entered; no
facade, no flat term, no `forgetHopf`.  STATUS: D4 remains proof residual; the model data (parent CD, legLift) are supplied
interfaces, discharged from the concrete carrier in Front 3.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct

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

/-- **R-6c-body-328 — the inner forest of the custom parent** (the retyped touched components). -/
noncomputable def innerRaw :
    ResolvedAdmissibleSubgraph (localizedParentWithTouchedLegs z δ datum hE hL).toResolvedFeynmanGraph :=
  ResolvedAdmissibleSubgraph.ofElements
    ((touchedOuterComponents z δ).attach.image (toInner z δ datum hE hL))
    (by
      intro B hB
      obtain ⟨A, -, rfl⟩ := Finset.mem_image.mp hB
      exact toInner_isConnectedDivergent z δ datum hE hL A)
    (by
      intro B₁ hB₁ B₂ hB₂ hne
      obtain ⟨A₁, -, rfl⟩ := Finset.mem_image.mp hB₁
      obtain ⟨A₂, -, rfl⟩ := Finset.mem_image.mp hB₂
      exact toInner_disjoint z δ datum hE hL
        (fun h => hne (congrArg (toInner z δ datum hE hL) h)))

/-- **R-6c-body-328 — the inner forest's components are the retyped touched collection** (`rfl`). -/
theorem innerRaw_elements :
    (innerRaw z δ datum hE hL).elements
      = (touchedOuterComponents z δ).attach.image (toInner z δ datum hE hL) :=
  rfl

/-- **R-6c-body-328 — M3: promote-to-touched-collection.**  Promoting the inner forest back recovers exactly the touched
collection — the multi-star replacement for the retired singleton `promote_collapse`. -/
theorem promote_innerRaw_elements :
    (ResolvedAdmissibleSubgraph.promote (localizedParentWithTouchedLegs z δ datum hE hL)
        (innerRaw z δ datum hE hL)).elements
      = touchedOuterComponents z δ := by
  ext x
  simp only [ResolvedAdmissibleSubgraph.promote_elements, innerRaw_elements, Finset.mem_image,
    Finset.mem_attach, true_and]
  constructor
  · rintro ⟨B, ⟨A, rfl⟩, rfl⟩
    rw [promote_toInner z δ datum hE hL A]
    exact A.2
  · intro hx
    exact ⟨toInner z δ datum hE hL ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩,
      promote_toInner z δ datum hE hL ⟨x, hx⟩⟩

end GaugeGeometry.QFT.Combinatorial
