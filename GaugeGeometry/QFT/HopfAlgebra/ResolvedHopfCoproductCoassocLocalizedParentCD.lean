import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocTouchedLocalComponent

/-!
# R-6c-body-322 — M2 split: local-component CD (M2a, PROVED) + localized parent + parent-CD verdict (M2b = honest leaf)

Three-hundred-and-twenty-second genuine-body step — Front-1 M2, split into two genuinely different obligations:

* **M2a** (PROVED here): the localized component `touchedLocalComponent z δ` is connected-divergent whenever `δ` is —
  a thin transport (same data, different ambient), closed by defeq on the intrinsic conjuncts + `IsAmbientInvariantDivergence`
  on the divergence conjunct.
* **M2b** (verdict C, recorded): the de-contracted PARENT's CD is an HONEST SUPPLIED DATUM — there is no inverse theorem
  (every divergence-preservation runs parent → quotient), so `localizedParent.forget.IsConnectedDivergent` must be a
  supply field, exactly like the CK subdivergence-nesting / `contract_preserves_CD` measure leaves.

The "same data ⇒ same CD" intuition holds for the local component (M2a) but must NOT be extended to the parent (M2b):
de-contraction CHANGES the parent's data (`internalEdges = Aout.internalEdges + quotientEdgePreimage`).

## M2a — the local-component CD transport (PROVED)

`(touchedLocalComponent z δ).forget` and `δ.forget` have IDENTICAL underlying data (vertices/internalEdges/externalLegs,
by the body-321 rfl projections), so their `toFeynmanGraph` agree (defeq).  `IsConnected` / `IsOnePI` (both functions of
`toFeynmanGraph`, SubGraph.lean:670,680) transfer by defeq; `IsDivergent` (reads the ambient `DivergenceMeasure.degree`,
which differs by ambient) transfers via `IsAmbientInvariantDivergence.degree_self_eq` (ContractionPreservation.lean:451) —
the degree depends only on `toFeynmanGraph`, which is shared.

## M2b — the parent CD is an honest supplied datum (verdict C)

Audited: NO inverse (quotient CD → parent CD) theorem exists.  Every divergence-preservation class runs FORWARD:
`IsDivergencePreservedByContract` (parent divergent → quotient divergent, ContractionPreservation.lean:320),
`IsDivergencePreservedByAdmissibleForestContract` (:340), `ResolvedInnerCDPreservationSupply.contract_preserves_CD`
(InnerCDBody.lean:47) — all input = parent, output = quotient.  `parentOfQuotient` has ONLY backbone identities
(`parentOfQuotient_remnant_eq` ActualSigmaCover.lean:1237, `_internalEdges` :971, `_externalLegs` :986,
`_containsAoutEdges` :958), NO CD lemma.  Every call site ASSUMES `parent.forget.IsConnectedDivergent`
(ActualSigmaCover.lean:1066/1079/1091; `ResolvedBranchMapInstantiation.lean:139` `remnantCD` is an assumed field).  So
`localizedParent.forget.IsConnectedDivergent` is a genuine model datum (a supply field), NOT derivable — the same tier as
`recovered_raw_mem` / `forestTag_agrees` / the measure CD leaves.  This is expected: it is the CK statement that a
divergent quotient subdivergence has a divergent de-contracted preimage — a power-counting fact the measure supplies.

## `localizedParent` — value-only (hE/hL threaded, NO CD in the def)

`parentOfQuotient` (ActualSigmaCover.lean:894) requires endpoint-support `hE`/`hL` (a raw `ResolvedFeynmanGraph` carries
no well-formedness field, ResolvedFeynmanGraphs.lean:60), but NOT a CD hypothesis — so `localizedParent` is DEFINABLE now
(value-only) with `hE`/`hL` threaded from the caller (the payload graph discharges them).  The CD is separate (M2b).

Per the HALT: only M2a is proved and `localizedParent` defined (value-only); the M2b parent CD is NOT proved (honest
supplied datum, verdict C); NO carrier / `ForestIdx`; the M3 promote law is NOT entered; no facade, no flat term, no
`forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

variable {D : ResolvedCoproductProperForestData}

set_option linter.unusedSectionVars false

/-- **R-6c-body-322 — M2a: the localized component is connected-divergent** whenever `δ` is.  Same underlying data as
`δ`, so `IsConnected` / `IsOnePI` transfer by defeq and `IsDivergent` by ambient-invariance. -/
theorem touchedLocalComponent_isConnectedDivergent {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
    (hδ : δ.forget.IsConnectedDivergent) :
    (touchedLocalComponent z δ).forget.IsConnectedDivergent := by
  obtain ⟨hC, hPI, hDiv⟩ := hδ
  refine ⟨hC, hPI, ?_⟩
  have hdeg : DivergenceMeasure.degree (touchedLocalComponent z δ).forget
      = DivergenceMeasure.degree δ.forget := by
    rw [← IsAmbientInvariantDivergence.degree_self_eq (touchedLocalComponent z δ).forget,
      ← IsAmbientInvariantDivergence.degree_self_eq δ.forget]
    rfl
  show (0 : ℤ) ≤ DivergenceMeasure.degree (touchedLocalComponent z δ).forget
  rw [hdeg]; exact hDiv

/-- **R-6c-body-322 — the localized de-contracted parent** (value-only; `hE`/`hL` threaded, no CD in the def).  The
B-path (body-317): re-key `parentOfQuotient` with `Aout := touchedOuterForest z δ`, `δ := touchedLocalComponent z δ`. -/
noncomputable def localizedParent {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
    (hE : ∀ e ∈ G.internalEdges, e.source ∈ G.vertices ∧ e.target ∈ G.vertices)
    (hL : ∀ ℓ ∈ G.externalLegs, ℓ.attachedTo ∈ G.vertices) :
    ResolvedFeynmanSubgraph G :=
  parentOfQuotient (touchedOuterForest z δ) (D.starOf G z.1.1) (touchedLocalComponent z δ) hE hL

end GaugeGeometry.QFT.Combinatorial
