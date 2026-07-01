import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocTermEqGrandSupply
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocImageSideTerm

/-!
# R-6c-heart-6a-11d — `term_eq` grand → support-8 image-side term supply (heart plugged into the wiring)

The `term_eq` heart (6a-11c) is plugged into the ALREADY-CLOSED coassociativity wiring: the image side is
built from the inner strict-summand supply (whose `imageWeightOf = resolvedCoassocQuotientTerm`), and the
`ResolvedTermEqGrandSupply.term_eqs` fills the support-8 `term_eq` field.  This confirms `term_eq` flows to
`ResolvedCoassocImageSideTermSupply` → `toSplitPhiData` → (support-9) `FullSupply` → `coassoc_gen`.

Since `Inner.toStrictSummandSupply.toImageSideSupply` sets `imageWeightOf := resolvedCoassocQuotientTerm`,
the support-8 term_eq target `toImageOfData.imageWeight (imageOf s)` is defeq the grand `term_eqs` RHS.

Per the HALT, no finite cover / inj / agreements / leaf fields; just the term_eq → image-side connection.

Landed:

* `ResolvedCoassocGrandImageSideSupply D G` — `Inner` + `selected` / `quotient` / `discriminatorOf` +
  `Product` / `Right` (over the derived `imageOf`);
* `.toImageSideTermSupply` — the support-8 term supply (with the heart `term_eq`);
* `.toSplitPhiData` — the resolved `forestComponentSplitPhi` data (support-8).

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-6a-11d — the grand image-side supply.**  The inner strict-summand + selected/quotient/
discriminator (building the image side), plus the two grand records over the derived `imageOf`. -/
structure ResolvedCoassocGrandImageSideSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph) where
  /-- The inner quotient-of-quotient generator supply (fixes `imageWeightOf`). -/
  Inner : ResolvedCoassocInnerRightSupply D G
  /-- The selected-outer image supply. -/
  selected : ResolvedCoassocSelectedOuterImageSupply D G
  /-- The quotient-forest supply. -/
  quotient : ResolvedCoassocQuotientForestSupply D G selected
  /-- The star discriminator. -/
  discriminatorOf : ResolvedCoassocQuotientImage D G → Prop
  /-- The product factorization record over the derived `imageOf`. -/
  Product : ResolvedProductEqGrandSupply D G
    (Inner.toStrictSummandSupply.toImageSideSupply selected quotient discriminatorOf).toImageOfData.imageOf
  /-- The right-factor record over the derived `imageOf`. -/
  Right : ResolvedRightGrandSupply D G
    (Inner.toStrictSummandSupply.toImageSideSupply selected quotient discriminatorOf).toImageOfData.imageOf

/-- **R-6c-heart-6a-11d — into the support-8 image-side term supply (the heart plugged in). -/
noncomputable def ResolvedCoassocGrandImageSideSupply.toImageSideTermSupply
    (S : ResolvedCoassocGrandImageSideSupply D G) : ResolvedCoassocImageSideTermSupply D G where
  toResolvedCoassocImageSideSupply :=
    S.Inner.toStrictSummandSupply.toImageSideSupply S.selected S.quotient S.discriminatorOf
  term_eq := (ResolvedTermEqGrandSupply.mk S.Product S.Right S.Inner).term_eqs

/-- **R-6c-heart-6a-11d — the resolved `forestComponentSplitPhi` data (support-8). -/
noncomputable def ResolvedCoassocGrandImageSideSupply.toSplitPhiData
    (S : ResolvedCoassocGrandImageSideSupply D G) : ResolvedCoassocSplitPhiData D G :=
  S.toImageSideTermSupply.toSplitPhiData

end GaugeGeometry.QFT.Combinatorial
