import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSelectedOuterMem
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocImageWeight
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocTermEq
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocImageSideTerm

/-!
# R-6c-heart-5-pre — wire the concrete selectedOuter into the image side

With the de-contraction `selectedOuter` fully built (heart-4), thread it through the image-side pipeline:
the concrete `selectedOuterOf` (heart-4 P5) + the quotient-forest supply (heart-3) + the concrete image
weight `resolvedCoassocQuotientTerm` and discriminator (heart-3b) assemble a concrete
`ResolvedCoassocImageSideSupply` whose `selectedOuter` is no longer abstract.

The remaining supply obligations are bundled into `ResolvedConcreteImageSideData` (the parametric data
`D.carrier` makes inherent — `selectedOuter_mem` carrier closure, the σ-cover structural facts `Sig`, the
quotient de-contraction `Full`, and the doubly-contracted CD `innerRight`).  The term version then adds
`term_eq` via the heart-2 factorization — so `term_eq` is exactly `product_eq` + `right_eq`, the genuine
de-contraction term geometry (heart-5), now stated against the concrete `imageOf`/`imageWeight`.

Landed:

* `ResolvedConcreteImageSideData D G` — bundles `selectedOuter_mem` + `Sig` + `Full` + `innerRight`;
* `.toImageSideSupply` — the concrete `ResolvedCoassocImageSideSupply` (selectedOuter concrete);
* `.toImageSideTermSupply` — given the per-split-choice factorization family (`product_eq`/`right_eq`),
  the `ResolvedCoassocImageSideTermSupply` (term_eq from `term_eq_of_factorizations`).

No facade, no flat term, no `forgetHopf`, no proof of `product_eq`/`right_eq`.  The factorization
(heart-5) and the finite cover/regroup/∀x (heart-6) remain.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-5-pre — the concrete image-side de-contraction data.**  The remaining supply obligations
for a concrete image side over the heart-4 selectedOuter: the carrier closure `selectedOuter_mem`, the
σ-cover structural facts `Sig`, the quotient de-contraction `Full`, and the inner-right CD `innerRight`. -/
structure ResolvedConcreteImageSideData (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph) where
  /-- The carrier-closure of the selected outer forest (parametric obligation on `D.carrier`). -/
  selectedOuter_mem :
    ∀ s, (resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s ∈ D.carrier G
  /-- The σ-cover structural facts over the (concrete) selected outer. -/
  Sig : ResolvedCoassocSigmaDataSupply D G (resolvedConcreteSelectedOuterImageSupply D G selectedOuter_mem)
  /-- The full-grain quotient de-contraction over the selected outer. -/
  Full : ResolvedCoassocFullQuotientSupply D G
    (resolvedConcreteSelectedOuterImageSupply D G selectedOuter_mem) Sig
  /-- The inner quotient-of-quotient CD. -/
  innerRight : ResolvedCoassocInnerRightSupply D G

/-- **R-6c-heart-5-pre — the concrete image-side supply.**  `selectedOuter` is the heart-4 concrete map;
`quotient` from `Full`; `imageWeightOf` is the concrete `resolvedCoassocQuotientTerm`; `discriminatorOf`
the concrete forest-by-star. -/
noncomputable def ResolvedConcreteImageSideData.toImageSideSupply
    (I : ResolvedConcreteImageSideData D G) : ResolvedCoassocImageSideSupply D G :=
  I.innerRight.toImageSideSupply (resolvedConcreteSelectedOuterImageSupply D G I.selectedOuter_mem)
    I.Sig I.Full

/-- **R-6c-heart-5-pre — the concrete image-side term supply.**  Adds `term_eq` from the heart-2
factorization family — so the only remaining mathematical content is `product_eq` / `right_eq` per split
choice (the de-contraction term geometry, heart-5). -/
noncomputable def ResolvedConcreteImageSideData.toImageSideTermSupply
    (I : ResolvedConcreteImageSideData D G)
    (factorization : ∀ s, ResolvedSplitPhiTermEqFactorization D I.innerRight.toStrictSummandSupply
      I.toImageSideSupply.toImageOfData.imageOf s) :
    ResolvedCoassocImageSideTermSupply D G where
  toResolvedCoassocImageSideSupply := I.toImageSideSupply
  term_eq := term_eq_of_factorizations factorization

end GaugeGeometry.QFT.Combinatorial
