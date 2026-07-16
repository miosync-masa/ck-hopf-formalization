import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRoundTripInhabitabilityAudit
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestImageClassifier

/-!
# R-6c-body-316 — the multi-component de-contraction root: `touchedOuterComponents` + its shallow laws (PROVED)

Three-hundred-and-sixteenth genuine-body step — the FIRST piece of Front 1 (the true outer-mixing geometry, body-315),
the multi-component de-contraction law that replaces the retired floor-297 `forestComponentMem` + singleton
`promote_collapse`.  The correct type is NOT "δ ↦ several parents" but

```text
δ (a star-touching quotient component)  ↦  ONE larger de-contracted parent γ  with an inner forest B ⊆ γ,
    where B.elements ↔ the several OLD outer components of z.1.1 absorbed into δ = touchedOuterComponents z δ.
```

This body defines `touchedOuterComponents` and banks its three shallow laws (membership iff, nonempty from star-touch,
disjointness), then names the remaining deep laws precisely.  No mega-record; the singleton collapse is NOT used.

## The definition + shallow laws (banked here)

`touchedOuterComponents z δ = z.1.1.elements.filter (D.starOf G z.1.1 · ∈ δ.vertices)` — the outer components of `z.1.1`
whose star vertex lands inside the quotient component `δ`.  Since `starVertices A f = A.elements.image f`
(ResolvedSubGraph.lean:256), these are exactly the components absorbed into `δ` under contraction.

* `mem_touchedOuterComponents` — the membership iff (filter).
* `touchedOuterComponents_nonempty` — a star-touching `δ` (`¬ Disjoint δ.vertices (starVertices)`, the
  `resolvedIsForestImage` predicate) has a NONEMPTY touched collection.
* `touchedOuterComponents_disjoint` — vertex-disjoint quotient components have DISJOINT touched collections (so the
  touched collections of a proper forest `B` partition part of `z.1.1.elements`).

## The deep laws still to build (named, NOT proved here) — the real outer mixing

```text
D1  parentOfQuotient / γ-with-B      δ ↦ ⟨γ : larger parent, B : inner forest ⊆ γ⟩  (ActualSigmaCover.lean:894 lands
                                     in the WRONG type γ ⊇ Aout, body-306 — the NEW datum keeps γ, B honest, NOT ∈ z.1.1)
D2  promote-to-touched-collection    (ResolvedAdmissibleSubgraph.promote γ B).elements = touchedOuterComponents z δ
                                     — REPLACES the singleton `promote_collapse` ({γ}); `promote_elements` already emits
                                       the collection `B.elements.image (γ.promote ·)` (ResolvedSubgraphPromote.lean:129).
D3  de-contraction inverse           contractWithStars γ (star of B) relates back to δ (the `promote`/`contractWithStars`
                                     collection-level adjunction).
D4  parent injectivity (load-bearing) distinct δ ↦ vertex-disjoint γ/collections, so `q.choiceAt` keeps one B per outer
                                     component — else the domain choice cannot store the multi-star assembly.
D5  coverage (re-proves 289)         leftResidual z ∪ (⋃ over quotient components δ, touchedOuterComponents z δ)
                                     = z.1.1.elements — the outer-mixing coverage that re-proves `forward_outer_value`
                                       WITHOUT `forestComponentMem` (floor-297).
```

The old single-valued `componentToForest` may survive as a parent PROJECTION, but `parent ∈ z.1.1.elements` is NEVER
required again, and the singleton `promote_collapse = {parent}` is retired in favour of D2 (promote-to-touched-collection).

## Guards

* floor-297 (`γ ∈ z.1.1.elements` for a forest-recovered parent) is NOT reintroduced.
* multi-star `B` is NOT collapsed to a singleton.
* carrier membership is kept OUT: `touchedOuterComponents` reads only `starOf` / `elements` / `vertices` — no `D.carrier`.
* No forward identity / round-trip / `recovered_raw_mem` / `forestTag_agrees` is touched.

Per the HALT: only the definition + the three shallow laws are proved; D1–D5 are named for the next bodies; no mega-record;
no facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-316 — the touched outer components.**  The components of the outer forest `z.1.1` whose star vertex
lands inside the quotient component `δ` — i.e. the old outer components absorbed into `δ` under contraction.  This is the
multi-valued replacement for the single-valued `componentToForest` (body-315 Front 1). -/
noncomputable def touchedOuterComponents {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))) :
    Finset (ResolvedFeynmanSubgraph G) :=
  z.1.1.elements.filter (fun A => D.starOf G z.1.1 A ∈ δ.vertices)

/-- **R-6c-body-316 — membership in the touched collection.** -/
theorem mem_touchedOuterComponents {G : ResolvedFeynmanGraph} {z : ForestBlockCodType D G}
    {δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))}
    {A : ResolvedFeynmanSubgraph G} :
    A ∈ touchedOuterComponents z δ ↔ A ∈ z.1.1.elements ∧ D.starOf G z.1.1 A ∈ δ.vertices :=
  Finset.mem_filter

/-- **R-6c-body-316 — a star-touching quotient component has a nonempty touched collection.**  The
`resolvedIsForestImage` touch condition `¬ Disjoint δ.vertices (starVertices)` yields an absorbed outer component. -/
theorem touchedOuterComponents_nonempty {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    {δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))}
    (h : ¬ Disjoint δ.vertices (z.1.1.starVertices (D.starOf G z.1.1))) :
    (touchedOuterComponents z δ).Nonempty := by
  rw [Finset.not_disjoint_iff] at h
  obtain ⟨v, hvδ, hvstar⟩ := h
  rw [ResolvedAdmissibleSubgraph.mem_starVertices] at hvstar
  obtain ⟨A, hA, hAv⟩ := hvstar
  exact ⟨A, mem_touchedOuterComponents.mpr ⟨hA, by rw [hAv]; exact hvδ⟩⟩

/-- **R-6c-body-316 — vertex-disjoint quotient components have disjoint touched collections.**  So the touched
collections of the components of a proper forest partition (part of) `z.1.1.elements`. -/
theorem touchedOuterComponents_disjoint {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    {δ δ' : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))}
    (h : Disjoint δ.vertices δ'.vertices) :
    Disjoint (touchedOuterComponents z δ) (touchedOuterComponents z δ') := by
  rw [Finset.disjoint_left]
  intro A hA hA'
  rw [mem_touchedOuterComponents] at hA hA'
  exact Finset.disjoint_left.mp h hA.2 hA'.2

end GaugeGeometry.QFT.Combinatorial
