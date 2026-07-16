import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocTouchedLocalizationLeg

/-!
# R-6c-body-321 — M1 complete: `touchedLocalComponent` assembled (PROVED, value-only)

Three-hundred-and-twenty-first genuine-body step — the pure record assembly that COMPLETES M1 (Front 1): the quotient
component `δ`, living in the WHOLE-contracted graph `z.1.1.contractWithStars f`, re-typed as `touchedLocalComponent` in
the TOUCHED-forest-contracted graph `(touchedOuterForest z δ).contractWithStars f`.  Value-only — NO `ForestIdx`, NO
`D.carrier`.

## The assembly

`touchedLocalComponent z δ : ResolvedFeynmanSubgraph ((touchedOuterForest z δ).contractWithStars f)` with

```text
vertices        := δ.vertices        internalEdges := δ.internalEdges        externalLegs := δ.externalLegs
vertices_subset  := touchedContractedVertices_subset  (body-318)
internalEdges_le := touchedContractedInternalEdges_le (body-319)
externalLegs_le  := touchedContractedExternalLegs_le  (body-320)
edges_supported  := δ.edges_supported   legs_supported := δ.legs_supported   -- defeq: support is about δ's own data
```

The `edges_supported` / `legs_supported` fields are statements about the subgraph's OWN `internalEdges`/`externalLegs`/
`vertices` (not the ambient graph), so `δ.edges_supported` / `δ.legs_supported` land by defeq — no cast, no re-proof, no
`star`-map re-choice.  The three rfl projections are banked for downstream (M2/M3).

## M1 is now fully PROVED — Front-1 remaining is M2 + M3

With `touchedLocalComponent` built, δ is localized into the touched-forest contraction.  The B-path (body-317) can now
re-key `parentOfQuotient` with `Aout := touchedOuterForest z δ` and `δ := touchedLocalComponent z δ`.  The remaining
Front-1 obligations are exactly:

* **M2** — the localized-parent CD certificate `parent.forget.IsConnectedDivergent` (only ever assumed; audit next
  whether δ's existing CD transports to the local ambient, or an honest certificate is needed).
* **M3** — the collection-level `promote`/`contractWithStars` inverse: `(promote parent innerRaw).elements =
  touchedOuterComponents z δ` (the D2 pivot replacing the retired singleton `promote_collapse`).

Per the HALT: only the value-only `touchedLocalComponent` + its three rfl projections are proved; component data is δ's,
support inclusions are exactly 318/319/320; NO `ForestIdx`/carrier membership; the CD proof is NOT mixed into any field;
no facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-321 — the localized quotient component (M1 complete).**  `δ`, re-typed from the whole-contracted graph
into the touched-forest-contracted graph; value-only.  Support inclusions from bodies 318/319/320; the support fields are
δ's own (defeq). -/
noncomputable def touchedLocalComponent {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))) :
    ResolvedFeynmanSubgraph ((touchedOuterForest z δ).contractWithStars (D.starOf G z.1.1)) where
  vertices := δ.vertices
  internalEdges := δ.internalEdges
  externalLegs := δ.externalLegs
  vertices_subset := touchedContractedVertices_subset z δ
  internalEdges_le := touchedContractedInternalEdges_le z δ
  externalLegs_le := touchedContractedExternalLegs_le z δ
  edges_supported := δ.edges_supported
  legs_supported := δ.legs_supported

@[simp] theorem touchedLocalComponent_vertices {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))) :
    (touchedLocalComponent z δ).vertices = δ.vertices := rfl

@[simp] theorem touchedLocalComponent_internalEdges {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))) :
    (touchedLocalComponent z δ).internalEdges = δ.internalEdges := rfl

@[simp] theorem touchedLocalComponent_externalLegs {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))) :
    (touchedLocalComponent z δ).externalLegs = δ.externalLegs := rfl

end GaugeGeometry.QFT.Combinatorial
