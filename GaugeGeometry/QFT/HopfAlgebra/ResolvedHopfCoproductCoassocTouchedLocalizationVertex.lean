import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocTouchedOuterForest

/-!
# R-6c-body-318 — M1 vertex localization: the unused-star key + `δ.vertices ⊆ touched-contracted` (PROVED)

Three-hundred-and-eighteenth genuine-body step — M1 (Front 1): the load-bearing VERTEX obligation of localizing a quotient
component `δ` from the WHOLE-contracted graph `z.1.1.contractWithStars f` into the TOUCHED-forest-contracted graph
`(touchedOuterForest z δ).contractWithStars f`.  The M1 route is settled: localization is a **pure re-typing** (the data
`vertices`/`internalEdges`/`externalLegs` are δ's, unchanged — as `localizeRemnantComponent`, ActualSigmaCover.lean:1443-
1489, already does for a single component), so only the three support proofs change ambient.  This body banks the vertex
one; edges/legs (heavier — retarget generalization) are body-319.

## Route verdict — pure re-typing, NO `UsesOnlyStar` needed for vertices

The single-η bridge (`UsesOnlyStar`, ActualSigmaCover.lean:1313; the three `whole_local_retarget*_eq`, :1321-1368;
`usesOnlyStar_*_ok`, :1373-1436) hardcodes the singleton star `{starOf η}` and a one-component `componentAt` collapse.
For the multi-component touched forest, the vertex obligation needs NONE of that: a δ-vertex that IS a star is, by
`mem_touchedOuterComponents` (body-316), necessarily a TOUCHED star — so the `UsesOnlyStar` hypothesis is DISCHARGED, not
assumed.  This makes M1's vertex field far lighter than "generalize the retarget machinery."

## Banked here

* `unused_star_avoided` — `A ∈ z.1.1.elements → A ∉ touchedOuterComponents z δ → starOf A ∉ δ.vertices` (contrapositive
  of `mem_touchedOuterComponents.2`; the user's multi-component `UsesOnlyStars` seed).
* `touchedOuterForest_vertices_subset` — `(touchedOuterForest z δ).vertices ⊆ z.1.1.vertices` (touched ⊆ outer, the
  "larger complement" fact `G.vertices \ touched ⊇ G.vertices \ z.1.1`).
* `touchedContractedVertices_subset` — `δ.vertices ⊆ ((touchedOuterForest z δ).contractWithStars f).vertices` — the M1
  vertex field.  Outside branch: larger complement.  Star branch: a δ-star is a touched star (`mem_touchedOuterComponents`).

## The remaining M1 obligations (body-319)

```text
internalEdges_le : δ.internalEdges ≤ ((touchedOuterForest z δ).contractWithStars f).internalEdges
externalLegs_le  : δ.externalLegs  ≤ ((touchedOuterForest z δ).contractWithStars f).externalLegs
   — the multi-component analogues of ActualSigmaCover.lean:1467-1487 (generalize whole_local_retargetEdge/Leg_eq
     from single-η to touched endpoints, + Aw.complementEdges ≤ At.complementEdges).
edges_supported / legs_supported — FREE (data = δ's, unchanged).
```
Then `TouchedLocalizationData.localComponent` (value-only, NO carrier/ForestIdx) assembles; `whole_local_compat` and the
D2 promote-to-touched / CD are later.

Per the HALT: only the vertex localization (unused-star + vertex subset) is proved; edges/legs, the `localComponent`
assembly, CD, carrier, and D2 are NOT entered; singleton localization is NOT forced into a Finset fold; no proof field is
used as a transport surrogate; `parent ∈ z.1.1.elements` is not revived; no facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-318 — the unused-star key.**  An outer component not absorbed into `δ` has its star outside `δ` — the
multi-component `UsesOnlyStars`, derived (not assumed) from the touched-collection membership. -/
theorem unused_star_avoided {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    {δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))}
    {A : ResolvedFeynmanSubgraph G} (hA : A ∈ z.1.1.elements)
    (hnot : A ∉ touchedOuterComponents z δ) :
    D.starOf G z.1.1 A ∉ δ.vertices := fun hstar =>
  hnot (mem_touchedOuterComponents.mpr ⟨hA, hstar⟩)

/-- **R-6c-body-318 — the touched forest's vertices lie in the outer forest.** -/
theorem touchedOuterForest_vertices_subset {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    {δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))} :
    (touchedOuterForest z δ).vertices ⊆ z.1.1.vertices := by
  intro v hv
  rw [ResolvedAdmissibleSubgraph.mem_vertices] at hv ⊢
  obtain ⟨γ, hγ, hvγ⟩ := hv
  rw [touchedOuterForest_elements] at hγ
  exact ⟨γ, (mem_touchedOuterComponents.mp hγ).1, hvγ⟩

/-- **R-6c-body-318 — the M1 vertex field.**  A quotient component `δ` has its vertices inside the touched-forest's
contracted graph.  Outside branch: larger complement (touched ⊆ outer).  Star branch: a δ-star is a touched star. -/
theorem touchedContractedVertices_subset {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))) :
    δ.vertices ⊆ ((touchedOuterForest z δ).contractWithStars (D.starOf G z.1.1)).vertices := by
  intro v hv
  have hvw := δ.vertices_subset hv
  rw [ResolvedAdmissibleSubgraph.contractWithStars_vertices] at hvw
  rw [ResolvedAdmissibleSubgraph.contractWithStars_vertices, Finset.mem_union] at *
  rcases hvw with hout | hstar
  · left
    rw [Finset.mem_sdiff] at hout ⊢
    exact ⟨hout.1, fun hc => hout.2 (touchedOuterForest_vertices_subset z hc)⟩
  · right
    rw [ResolvedAdmissibleSubgraph.mem_starVertices] at hstar
    obtain ⟨A, hA, hAv⟩ := hstar
    rw [ResolvedAdmissibleSubgraph.mem_starVertices]
    refine ⟨A, ?_, hAv⟩
    rw [touchedOuterForest_elements]
    exact mem_touchedOuterComponents.mpr ⟨hA, by rw [hAv]; exact hv⟩

end GaugeGeometry.QFT.Combinatorial
