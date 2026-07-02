import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocImageWeight

/-!
# R-6c-leaf-18 — inner-right CD supply connector (flat-CD form)

Fourteenth leaf-body discharge (RIGHT side, the `Inner` of the term-eq bundle).  `ResolvedCoassocInnerRightSupply`
has a single field `innerCD`: the doubly-contracted quotient subforest `(z.quotientForest.contractWithStars
…).forget.toClass.IsConnectedDivergent` — the genuine divergence-preservation of the quotient-of-quotient
(no `contractWithStars`-preserves-CD lemma exists in the development, so this stays a supplied fact).

`FeynmanGraphClass.isConnectedDivergent_toClass` (StrictGenerators:244, `g.toClass.IsConnectedDivergent ↔
g.IsConnectedDivergent`) lets the field be phrased in the plainer *flat* CD form (`.forget.IsConnectedDivergent`,
without `toClass`), which is the standard shape divergence facts are usually available in.

Per the HALT, `innerCD_forget` is a supply field (CD is instance-heavy); Sector / Perm / Retarget / finite
cover untouched.

Landed:

* `ResolvedInnerRightCDSupply D G` — `innerCD_forget` (flat CD of the doubly-contracted quotient subforest);
* `.toInnerRightSupply : ResolvedCoassocInnerRightSupply D G`.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-leaf-18 — the inner-right CD supply (flat-CD form).**  The doubly-contracted quotient subforest is
connected-divergent, phrased as the plain flat `.forget.IsConnectedDivergent`. -/
structure ResolvedInnerRightCDSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph) where
  /-- The quotient subforest contracted in the quotient graph is connected-divergent (flat form). -/
  innerCD_forget : ∀ z : ResolvedCoassocQuotientImage D G,
    (z.quotientForest.contractWithStars
        (D.starOf (resolvedCoassocQuotientGraph z) z.quotientForest)).forget.IsConnectedDivergent

/-- **R-6c-leaf-18 — the inner-right supply from the flat-CD field.**  `isConnectedDivergent_toClass` lifts
the flat CD to the `toClass` form `innerCD` needs. -/
def ResolvedInnerRightCDSupply.toInnerRightSupply
    (S : ResolvedInnerRightCDSupply D G) : ResolvedCoassocInnerRightSupply D G where
  innerCD := fun z => (FeynmanGraphClass.isConnectedDivergent_toClass _).mpr (S.innerCD_forget z)

end GaugeGeometry.QFT.Combinatorial
