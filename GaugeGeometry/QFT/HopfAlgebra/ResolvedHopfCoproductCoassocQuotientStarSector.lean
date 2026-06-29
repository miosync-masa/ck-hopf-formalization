import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocQuotientStarCodomain
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocThreeRouteVertexTransport

/-!
# R-6c-heart-6a-10c-1 — quotient-star sector equivalences → `QuotientStarSupply`

The BIGGEST `quotientStarEquiv` is now `quotientDomainEquiv` (10a, constructed) + the codomain split (10b)
+ two per-sector correspondences.  This file bundles the two sector equivalences and closes the BIGGEST's
exit: from a codomain full-quotient supply `C` plus the two sector equivalences, the whole
`ResolvedThreeRouteQuotientStarSupply` is produced (via `quotientStarEquivOf`'s `sumCongr` assembly).

So after this, the BIGGEST reduces to exactly:

* `rightEquiv` — `RightPrimitiveIndex ≃ {δ ∈ rightElements}` (a right-primitive component ↔ its quotient
  right-survivor star);
* `forestEquiv` — `ForestPrimitiveIndex ≃ {δ ∈ remnantElements}` (a forest-choice ↔ its remnant star);

plus the codomain `elements_eq` / `disjoint` data (10b).

Per the HALT, neither sector equivalence is constructed, `elements_eq` / `disjoint` are NOT proved.

Landed:

* `ResolvedQuotientStarSectorEquivSupply C` — the two sector equivalences over a codomain supply `C`;
* `.toQuotientStarSupply` — the assembled `ResolvedThreeRouteQuotientStarSupply`.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}
  {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}

/-- **R-6c-heart-6a-10c-1 — the two sector equivalences.**  Over a codomain full-quotient supply `C`: the
right-primitive ↔ right-survivor and forest-choice ↔ remnant index correspondences. -/
structure ResolvedQuotientStarSectorEquivSupply
    (C : ResolvedQuotientStarCodomainFullQuotientSupply D G imageOf) where
  /-- Right-primitive components ≃ their quotient right-survivor stars. -/
  rightEquiv : ∀ s : ResolvedCoassocSplitChoice D G,
    RightPrimitiveIndex D G s ≃ {δ // δ ∈ C.rightElements s}
  /-- Forest-choice components ≃ their remnant stars. -/
  forestEquiv : ∀ s : ResolvedCoassocSplitChoice D G,
    ForestPrimitiveIndex D G s ≃ {δ // δ ∈ C.remnantElements s}

/-- **R-6c-heart-6a-10c-1 — the quotient-star supply from the codomain split + sector equivalences. -/
noncomputable def ResolvedQuotientStarSectorEquivSupply.toQuotientStarSupply
    {C : ResolvedQuotientStarCodomainFullQuotientSupply D G imageOf}
    (S : ResolvedQuotientStarSectorEquivSupply C) :
    ResolvedThreeRouteQuotientStarSupply D G imageOf where
  quotientStarEquiv := fun s =>
    quotientStarEquivOf C.toCodomainSplitSupply s (S.rightEquiv s) (S.forestEquiv s)

end GaugeGeometry.QFT.Combinatorial
