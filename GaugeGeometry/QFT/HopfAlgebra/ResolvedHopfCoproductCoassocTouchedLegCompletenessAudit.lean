import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocToInnerContainment

/-!
# R-6c-body-325 — touched leg-preimage existence audit: Q3 FAIL, δ-leg-completeness is a model datum (verdict)

Three-hundred-and-twenty-fifth genuine-body step — the touched lower-bound external-leg-preimage existence audit demanded
before adopting route A'.  The load-bearing step FAILS: `(touchedOuterForest z δ).externalLegs.map retarget ≤
δ.externalLegs` does NOT hold for a universally-quantified `δ`.  The rescue — δ-leg-completeness — is a genuine CK
structural fact of the concrete carrier's quotient components, joining the model-datum tier (M2b parent CD /
`recovered_raw_mem` / `forestTag_agrees`).  Neither route A' (strengthen the base `Classical.choose`) nor route C
(legs-agnostic `coverage_value`) is free; both are base-layer edits.  This body banks only the one clean provable fact
(`touchedOuterForest_starTouch`) and pins the verdict.

## Q3 = FAIL-asymmetry (the leg step is underivable at the stated generality)

* **Legs never become internal edges.**  `contractWithStars` keeps `externalLegs`/`internalEdges` as INDEPENDENT fields
  (RSG:286-290): legs go through `G.externalLegs.map (A.retargetExternalLeg starOf)`, edges through
  `A.complementEdges.map (A.retargetEdge starOf)`; `ResolvedExternalLeg.retarget` (ResolvedFeynmanGraphs.lean:153-157)
  rewrites ONLY `attachedTo`, always yielding one single-attachment leg.  So case (b) is impossible.
* **Retargeted touched legs only ATTACH to `δ.vertices` — one-way.**  A leg of `(touchedOuterForest z δ).externalLegs`
  is `ℓ ∈ A.externalLegs` for a touched `A`; `legs_supported` (RSG:35) gives `ℓ.attachedTo ∈ A.vertices`, and
  `retargetExternalLeg` sends it to `starOf A ∈ δ.vertices` (touched).  But `legs_supported` is a ONE-WAY implication
  (`leg ∈ externalLegs ⟹ attaches to vertices`); its CONVERSE (a contract-leg attaching to `δ.vertices` is IN
  `δ.externalLegs`) does not hold — `δ.externalLegs` is an arbitrary submultiset of `contract.externalLegs`
  (`externalLegs_le` + `legs_supported` only).
* **Counterexample (case a).**  `G` with two legs `ℓ₁, ℓ₂` on one vertex `v` of a touched `A` (both `∈ A.externalLegs`);
  a valid `δ` may take `δ.externalLegs = {retarget ℓ₁}` (≤ contract legs, attaches to `starOf A ∈ δ.vertices`), omitting
  `retarget ℓ₂`.  Then `retarget ℓ₂ ∈ touchedOuterForest.externalLegs.map retarget` but `∉ δ.externalLegs`.  The `≤`
  fails.  Only the REVERSE `δ.externalLegs ≤ contract.externalLegs` is proved (body-320 `touchedContractedExternalLegs_le`).
* **The witness is not extractable.**  `quotientLegPreimage_exists` (ActualSigmaCover.lean:837-843) delegates to generic
  `exists_le_map` (ResolvedUniquePayloadModel.lean:24-41), an occurrence-by-occurrence ARBITRARY preimage, touched-forest-
  agnostic.  A touched-lower-bound `L ⊇ touchedOuterForest.externalLegs` is not recoverable, and re-choosing it needs the
  Q3 `≤` first — which fails.

## M3 genuinely needs exact leg equality (route C is not free either)

`ResolvedFeynmanSubgraph.ext` (RSG:113-118) demands `externalLegs` equality; `coverage_value` / `forward_outer_value`
(ForwardOuterValue.lean:160-194) compare `.elements` by FULL structural Finset membership (legs included).  A route-C
`toInner A` carrying parent-relative legs breaks `promote (toInner A) = A` on the leg field, so
`(promote localizedParent innerRaw).elements ≠ touchedOuterComponents z δ`.  A legs-agnostic reformulation would require
replacing the full-structural `.elements` comparison in `coverage_value` with a legs-quotiented one — a base-layer change
of comparable weight to strengthening the base `Classical.choose`.

## Verdict — δ-leg-completeness is a concrete-model CK datum (the orphan problem, leg side)

The one property that rescues route A' is **δ-leg-completeness**: `δ.externalLegs = { all contract-legs attaching to
δ.vertices }`.  It is NOT in `resolvedIsForestImage` (a purely vertex-based star-touch existential,
ForestImageClassifier.lean:66-69), NOT in the abstract carrier, and NOT any existing lemma.  This is the SAME structure as
the orphan defect: on a FORWARD IMAGE `z = fwd q` the quotient components are genuine de-contractions (remnant =
de-contraction of choiceParents, body-305), hence leg-complete; for a GENERIC orphan `z` an arbitrary carrier member `B`'s
components need NOT be leg-complete.  So the bijection's surjectivity onto the full codomain (orphans included) rests on
the concrete carrier's quotient components being leg-complete CK subdivergences — a power-counting/structural fact the
CONCRETE model supplies, NOT derivable abstractly.  It joins the Front-1 model-datum tier: **M2b parent CD +
δ-leg-completeness** (both CK structural facts of the concrete carrier), alongside `recovered_raw_mem` / `forestTag_agrees`.

## Consequence for the campaign

Front-1 (the touched-geometry re-proof of `forward_outer_value` at orphans) reduces `forward_outer_value` to: D5 coverage
(PROVED, body-323) on VERTICES/edges + the leg-side δ-leg-completeness datum + M2b parent CD.  The vertex/edge geometry is
honest and mechanical (bodies 316-324); the two residual data (parent CD, δ-leg-completeness) are concrete-model CK facts,
the same tier as the carrier closure.  This is the honest floor: the multi-star de-contraction geometry is real and mostly
mechanical, but bottoms out at two power-counting structural data the abstract carrier cannot supply.

Per the HALT: only `touchedOuterForest_starTouch` (the Q2 fact) is proved; the leg `≤` is NOT proved (FAIL-asymmetry), no
base file is edited, route A'/C are NOT pursued, δ-leg-completeness is NOT claimed proved (it is a named model datum); no
facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData}

set_option linter.unusedSectionVars false

/-- **R-6c-body-325 — Q2: every touched-forest component's star lies in `δ`.**  The one clean provable fact of the leg
audit (the touched membership); the leg `≤` (Q3) is FAIL-asymmetry and NOT proved. -/
theorem touchedOuterForest_starTouch {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    {δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))}
    {A : ResolvedFeynmanSubgraph G} (hA : A ∈ (touchedOuterForest z δ).elements) :
    D.starOf G z.1.1 A ∈ δ.vertices := by
  rw [touchedOuterForest_elements] at hA
  exact (mem_touchedOuterComponents.mp hA).2

end GaugeGeometry.QFT.Combinatorial
