import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocImageSideSupply

/-!
# R-6c-support-8 — term_eq supply → `ResolvedCoassocSplitPhiData`

The heart theorem `term_eq` made a single named field, so the rest of the image-side wiring closes all
the way to `ResolvedCoassocSplitPhiData` before the heart is struck.  Extending the support-7
`ResolvedCoassocImageSideSupply` with one field

  `term_eq : ∀ s, resolvedSplitChoiceTerm s = imageWeight (imageOf s)`  (in `ResolvedHopfH3`)

and applying the part-3a `ResolvedCoassocSplitPhiImageOfData.toSplitPhiData` yields the full
`ResolvedCoassocSplitPhiData`.

`term_eq` is the **resolved, facade-free replacement of the gated flat
`forestComponentSplitPhi_term_eq_of_split`** — the heart of R-6 (provable because resolved generators
are id-bearing, so the R-5 wall dissolves).  **It is NOT proved here**; it is isolated as a field so the
remaining chain (`SplitPhiData → SplitPhiFiniteData → GlobalCoverData → coassoc_gen`) becomes pure
wiring with `term_eq` the single genuine hole.

Landed:

* `ResolvedCoassocImageSideTermSupply D G` — `extends ResolvedCoassocImageSideSupply` with the `term_eq`
  field (the heart as a first-class hypothesis);
* `ResolvedCoassocImageSideTermSupply.toSplitPhiData` — `toImageOfData.toSplitPhiData term_eq`.

No facade, no flat splitPhi theorem, no `forgetHopf`, no proof of `term_eq`; finite carriers/cover and
the term agreement's proof are the remaining work.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-support-8 — the image side with the term agreement.**  The support-7 image side plus the
heart hypothesis `term_eq`: the resolved split-choice term equals the image weight along the resolved
`forestComponentSplitPhi` (`imageOf`), in `ResolvedHopfH3`.  This `term_eq` field is the resolved,
facade-free replacement of the gated flat `forestComponentSplitPhi_term_eq_of_split` — **not proved
here**, isolated as a first-class field so the rest of the chain is pure wiring. -/
structure ResolvedCoassocImageSideTermSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph) extends ResolvedCoassocImageSideSupply D G where
  /-- The resolved term agreement (the heart): `resolvedSplitChoiceTerm s = imageWeight (imageOf s)`.
  The facade-free replacement of gated `forestComponentSplitPhi_term_eq_of_split`; not proved here. -/
  term_eq : ∀ s : ResolvedCoassocSplitChoice D G,
    D.resolvedSplitChoiceTerm s =
      toResolvedCoassocImageSideSupply.toImageOfData.imageWeight
        (toResolvedCoassocImageSideSupply.toImageOfData.imageOf s)

/-- **R-6c-support-8 — assemble the full splitPhi skeleton.**  Add the `term_eq` field to the support-7
`toImageOfData` via the part-3a `toSplitPhiData`, recovering `ResolvedCoassocSplitPhiData`. -/
noncomputable def ResolvedCoassocImageSideTermSupply.toSplitPhiData
    (S : ResolvedCoassocImageSideTermSupply D G) : ResolvedCoassocSplitPhiData D G :=
  S.toImageOfData.toSplitPhiData S.term_eq

end GaugeGeometry.QFT.Combinatorial
