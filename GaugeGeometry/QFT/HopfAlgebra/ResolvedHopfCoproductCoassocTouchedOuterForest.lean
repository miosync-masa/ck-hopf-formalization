import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocTouchedOuterComponents

/-!
# R-6c-body-317 — D1 value-only scout: the touched outer forest + the localized-parent verdict (PROVED lift)

Three-hundred-and-seventeenth genuine-body step — the D1 value-only scout (Front 1).  It banks the raw-forest lift of
`touchedOuterComponents` (body-316) as `touchedOuterForest` (with CD / pairwise-disjointness inherited automatically), and
records the localized-de-contraction-parent verdict: **C with a B-shaped path** — no existing constructor returns exactly
δ's star fiber, but the GLOBAL `parentOfQuotient` (which has a FREE `Aout` argument) RE-KEYED to `touchedOuterForest z δ`
does, modulo a multi-component whole↔local transport.  Value-only: NO `ForestIdx`, NO `D.carrier` (those defer to Front 3).

## Banked here — the touched outer forest (item 1)

`touchedOuterForest z δ := z.1.1.filterElements (D.starOf G z.1.1 · ∈ δ.vertices)` — the sub-forest of the outer `z.1.1`
cut to the touched components.  `filterElements` (ResolvedAdmissibleSubgraphOfElements.lean:75-84) inherits
`isConnectedDivergent` + `pairwiseDisjoint` from `z.1.1` AUTOMATICALLY (no proof obligations), and its `_elements` is
`rfl`.  So `(touchedOuterForest z δ).elements = touchedOuterComponents z δ`, and the body-316 nonempty law transports.

## The localized-parent verdict — C with a B-path

* **Load-bearing fact (confirmed).**  Every existing δ-keyed de-contraction parent drags `Aout.internalEdges` as a WHOLE
  summand: `parentOfQuotient` (ResolvedActualSigmaCover.lean:894-906) has result
  `internalEdges := Aout.internalEdges + quotientEdgePreimage Aout starOf δ` (`:905`), `vertices` filtered by
  `v ∈ Aout.vertices ∨ …` (`:901-902`), certified by `parentOfQuotient_containsAoutEdges` (`:964`,
  `Aout.internalEdges ≤ result.internalEdges`).  `parentOfQuotientLocalComponent` (`:1262`) only narrows to a SINGLE
  component `η`.  So NO constructor returns exactly the touched fiber — **not verdict A**.

* **The B-path.**  `parentOfQuotient`'s `Aout` is a FREE argument.  Re-keying `Aout := touchedOuterForest z δ` yields
  `internalEdges = (touchedOuterForest z δ).internalEdges + quotientEdgePreimage` — ONLY the touched fiber, not all of
  `z.1.1`.  This is the correct localized parent.

* **The missing raw pieces** (named for body-318+):
  ```text
  M1  multi-component whole↔local transport   δ : z.1.1.contractWithStars ⤳ (touchedOuterForest z δ).contractWithStars
      (the re-keyed parentOfQuotient needs δ in the SMALLER contracted graph; the existing bridge
       `localizeRemnantComponent` / `UsesOnlyStar` / `whole_local_retargetVertex_eq`, ActualSigmaCover.lean:1313-1489,
       is single-`η` only — this is the genuinely new transport).
  M2  localized-parent CD certificate         parent.forget.IsConnectedDivergent (only ever ASSUMED, :1066/:1263; new).
  M3  D2 promote-to-touched-collection        (promote parent innerRaw).elements = touchedOuterComponents z δ
      (promote_elements already = B.elements.image (γ.promote ·), ResolvedSubgraphPromote.lean:129 — this is the pivot).
  ```
  The re-contract section laws (`parentOfQuotient_remnant_eq` / `_internalEdges` `:971-985`) already EXIST for the free
  `Aout`, so they transport to the re-keyed `Aout` for free once M1 lands δ in the smaller contracted graph.

## Membership separation confirmed (defers to Front 3)

`touchedOuterForest` / `parentOfQuotient` / `filterElements` / `reembedAsSubgraph` all build from vertices/edges/legs
only — NO `D.carrier`.  So the eventual `parent ∈ recovered outer carrier` and `innerRaw ∈ D.carrier parent` obligations
defer cleanly to Front 3; the D1 value block stays carrier-free.

Per the HALT: only `touchedOuterForest` + its `_elements` / nonempty are proved; M1–M3 and the value block
`ResolvedRawDecontractionBlock` are named for later; NO `ForestIdx`/`D.carrier` landing; floor-297 not revived; singleton
`promote_collapse` not used; no facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-317 — the touched outer forest.**  The sub-forest of the outer `z.1.1` cut to the components absorbed
into the quotient component `δ`; CD + pairwise disjointness are inherited from `z.1.1` by `filterElements`. -/
noncomputable def touchedOuterForest {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))) :
    ResolvedAdmissibleSubgraph G :=
  z.1.1.filterElements (fun A => D.starOf G z.1.1 A ∈ δ.vertices)

/-- **R-6c-body-317 — the touched forest's components are exactly the touched collection** (`rfl`). -/
theorem touchedOuterForest_elements {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))) :
    (touchedOuterForest z δ).elements = touchedOuterComponents z δ :=
  rfl

/-- **R-6c-body-317 — a star-touching quotient component has a nonempty touched forest.** -/
theorem touchedOuterForest_nonempty {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    {δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))}
    (h : ¬ Disjoint δ.vertices (z.1.1.starVertices (D.starOf G z.1.1))) :
    (touchedOuterForest z δ).elements.Nonempty := by
  rw [touchedOuterForest_elements]
  exact touchedOuterComponents_nonempty z h

end GaugeGeometry.QFT.Combinatorial
