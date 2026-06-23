import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSelectedOuterBridge

/-!
# R-6c-support-6 — quotientForestOf supply bridge

With the selected-outer map `selectedOuterOf` wired into the image side (R-6c-support-5), the second
de-contraction obligation is the **quotient forest**: for each split choice `s`, a subforest of the
selected outer's star-contraction,

  `quotientForestOf s : ResolvedAdmissibleSubgraph ((selectedOuterOf s).1.contractWithStars …)`.

Its concrete content is the genuine right/remnant de-contraction (the resolved
`ResolvedFullQuotientForestImageData`), so per the HALT it is **isolated as a supply field** bundled
over a fixed `ResolvedCoassocSelectedOuterImageSupply S` (whose `selectedOuterOf` the field type
depends on).  The adapter `toImageSupply` then closes `quotientForestOf` (+ the still-deferred
`imageWeightOf` / `discriminatorOf`, passed as inputs) into a full `ResolvedCoassocSplitPhiImageSupply`
via the support-5 skeleton.

So after this file, all three remaining image-side fields (`quotientForestOf` / `imageWeightOf` /
`discriminatorOf`) are isolated as supply, and a `ResolvedCoassocSplitPhiImageSupply` is one adapter
call away — without `term_eq`, finite carriers, or the promote body.

Landed:

* `ResolvedCoassocQuotientForestSupply D G S` — `quotientForestOf` as a supply field over a fixed
  selected-outer supply `S`;
* `ResolvedCoassocQuotientForestSupply.toImageSupply` — assembles `ResolvedCoassocSplitPhiImageSupply`
  from `quotientForestOf` + supplied `imageWeightOf` / `discriminatorOf`.

No facade, no flat splitPhi theorem, no `forgetHopf`; the concrete `quotientForestOf` (the right/remnant
de-contraction) and `term_eq` are the remaining work.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-support-6 — the quotient-forest supply.**  Over a fixed selected-outer supply `S`, the
quotient forest of every split choice: a subforest of the selected outer's star-contraction (the
resolved analogue of the flat quotient subforest in `forestQuotientForestSigma`).  Its concrete content
is the right/remnant de-contraction, kept as a supply field. -/
structure ResolvedCoassocQuotientForestSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph) (S : ResolvedCoassocSelectedOuterImageSupply D G) where
  /-- The quotient forest of a split choice (a subforest of the selected outer's star-contraction). -/
  quotientForestOf : (s : ResolvedCoassocSplitChoice D G) →
    ResolvedAdmissibleSubgraph
      ((S.selectedOuterOf s).1.contractWithStars (D.starOf G (S.selectedOuterOf s).1))

/-- **R-6c-support-6 — assemble the splitPhi image supply.**  Given the quotient-forest supply together
with the still-deferred image weight and star discriminator, produce a full
`ResolvedCoassocSplitPhiImageSupply D G` via the support-5 `toImageSupplySkeleton`.  This closes all
three remaining image-side fields into the image supply (no `term_eq`, no finite carriers). -/
noncomputable def ResolvedCoassocQuotientForestSupply.toImageSupply
    {S : ResolvedCoassocSelectedOuterImageSupply D G}
    (Q : ResolvedCoassocQuotientForestSupply D G S)
    (imageWeightOf : ResolvedCoassocQuotientImage D G → ResolvedHopfH3)
    (discriminatorOf : ResolvedCoassocQuotientImage D G → Prop) :
    ResolvedCoassocSplitPhiImageSupply D G :=
  S.toImageSupplySkeleton Q.quotientForestOf imageWeightOf discriminatorOf

end GaugeGeometry.QFT.Combinatorial
