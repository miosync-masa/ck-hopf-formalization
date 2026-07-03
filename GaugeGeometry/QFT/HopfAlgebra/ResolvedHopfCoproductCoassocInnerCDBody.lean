import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocInnerRightLeaves

/-!
# R-6c-body-33 — innerCD_forget reduced to contraction CD-preservation + `D.hCD`

Thirty-third genuine-body step, reducing leaf-18's `innerCD_forget` (the doubly-contracted quotient subforest
is connected-divergent) to a single named measure principle plus the already-available carrier CD `D.hCD`.

`innerCD_forget z` asserts `(z.quotientForest.contractWithStars (D.starOf (resolvedCoassocQuotientGraph z)
z.quotientForest)).forget.IsConnectedDivergent`.  Its ambient graph `resolvedCoassocQuotientGraph z` is
DEFINITIONALLY `z.selectedOuter.1.contractWithStars (D.starOf G z.selectedOuter.1)`, and `z.selectedOuter.1 ∈
D.carrier G` (the image's selected outer is a carrier forest), so `D.hCD` already gives the ambient's CD.  The
only remaining content is the Connes–Kreimer power-counting stability principle: contracting an admissible
(divergent) subforest of a connected-divergent graph yields a connected-divergent graph.  That is the
resolved, full-`IsConnectedDivergent` analog of the flat `IsDivergencePreservedByAdmissibleForestContract`
(which only supplies `IsDivergent`), so it is isolated as a supply field `contract_preserves_CD`.

Per the HALT, no measure theorem is invented; `contract_preserves_CD` is the named measure leaf; retarget /
support-9 are untouched.

Landed:

* `ResolvedInnerCDPreservationSupply D` — `contract_preserves_CD` (the CK contraction CD-stability principle);
* `.toInnerRightCDSupply` — leaf-18's `innerCD_forget`, from `contract_preserves_CD` at the quotient graph +
  `D.hCD` (ambient CD discharged).

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-body-33 — the contraction CD-preservation supply.**  The Connes–Kreimer power-counting stability
principle in resolved, full-`IsConnectedDivergent` form: contracting an admissible subforest of a
connected-divergent graph yields a connected-divergent graph.  (The resolved analog of the flat
`IsDivergencePreservedByAdmissibleForestContract`, which supplies only `IsDivergent`.) -/
structure ResolvedInnerCDPreservationSupply (D : ResolvedCoproductProperForestData) where
  /-- Contracting an admissible subforest of a CD graph preserves CD. -/
  contract_preserves_CD : ∀ (H : ResolvedFeynmanGraph) (A : ResolvedAdmissibleSubgraph H),
    H.forget.toClass.IsConnectedDivergent →
    (A.contractWithStars (D.starOf H A)).forget.IsConnectedDivergent

/-- **R-6c-body-33 — leaf-18's `innerCD_forget` from the CK contraction CD-stability + `D.hCD`.**  The quotient
graph's CD is `D.hCD` at the carrier `z.selectedOuter`; the principle then contracts `z.quotientForest`. -/
def ResolvedInnerCDPreservationSupply.toInnerRightCDSupply
    (P : ResolvedInnerCDPreservationSupply D) :
    ResolvedInnerRightCDSupply D G where
  innerCD_forget := fun z =>
    P.contract_preserves_CD (resolvedCoassocQuotientGraph z) z.quotientForest
      (D.hCD G z.selectedOuter.1 z.selectedOuter.2)

end GaugeGeometry.QFT.Combinatorial
