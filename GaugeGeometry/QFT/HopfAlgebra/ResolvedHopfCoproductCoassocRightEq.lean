import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocImageWeight

/-!
# R-6c-heart-5c-2a — `right_eq` scout + statement isolation

`right_eq : (D.supply G).rightTerm s.1 = innerRightTerm (imageOf s)` is, unfolded, an equality of two
`MvPolynomial.X` generators — both `X (graph.toResolvedHopfGen _)`:

* **branch side** `(D.supply G).rightTerm s.1 = X ((branchRightGraph s).toResolvedHopfGen _)`, where
  `branchRightGraph s = s.1.1.contractWithStars (D.starOf G s.1.1)` — the input outer forest `A`
  contracted **once**;
* **image side** `innerRightTerm (imageOf s) = X ((imageInnerRightGraph imageOf s).toResolvedHopfGen _)`,
  where `imageInnerRightGraph imageOf s = (imageOf s).quotientForest.contractWithStars (D.starOf
  (selectedOuter-quotient-graph) (imageOf s).quotientForest)` — the selected outer `A'` contracted,
  **then** its quotient subforest `B'` contracted (contract **twice**).

Since `G.toResolvedHopfGen hCD = ⟨G.toResolvedClass, hCD⟩` (CD proof irrelevant), `right_eq` reduces — by
`congrArg X` and `Subtype.ext` — to the single **contract-twice = contract-once** class equality

  `(branchRightGraph s).toResolvedClass = (imageInnerRightGraph imageOf s).toResolvedClass`.

This file isolates the two graphs and the reduction `right_eq_of_contract_class_eq`; the class equality
itself (the genuine de-contraction composition law) is left as the one named obligation.

Landed:

* `branchRightGraph` / `imageInnerRightGraph` — the contract-once / contract-twice graphs;
* `right_eq_of_contract_class_eq` — `right_eq` from the class equality;
* `ResolvedContractTwiceOnceSupply` — the class equality packaged as a supply field.

No facade, no flat term, no `forgetHopf`, no rep/perm.  The contract-twice = contract-once class equality
is the remaining work.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-5c-2a — the branch right graph.**  The input outer forest `A` of a split choice
contracted once to its stars — the graph of `(D.supply G).rightTerm s.1`. -/
noncomputable def branchRightGraph (s : ResolvedCoassocSplitChoice D G) : ResolvedFeynmanGraph :=
  s.1.1.contractWithStars (D.starOf G s.1.1)

/-- **R-6c-heart-5c-2a — the image inner-right graph.**  The selected outer forest contracted, then its
quotient subforest contracted in the quotient graph — the doubly-contracted graph of
`innerRightTerm (imageOf s)`. -/
noncomputable def imageInnerRightGraph
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G)
    (s : ResolvedCoassocSplitChoice D G) : ResolvedFeynmanGraph :=
  (imageOf s).quotientForest.contractWithStars
    (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)

/-- **R-6c-heart-5c-2a — `right_eq` from the contract-twice = contract-once class equality.**  Both sides
of `right_eq` are `X (graph.toResolvedHopfGen _)`; since the generator is the graph's resolved class (CD
proof irrelevant), the equality reduces to the class equality. -/
theorem right_eq_of_contract_class_eq (R : ResolvedCoassocInnerRightSupply D G)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G)
    (s : ResolvedCoassocSplitChoice D G)
    (hClass : (branchRightGraph s).toResolvedClass
      = (imageInnerRightGraph imageOf s).toResolvedClass) :
    (D.supply G).rightTerm s.1 = R.innerRightTerm (imageOf s) :=
  congrArg MvPolynomial.X (Subtype.ext hClass)

/-- **R-6c-heart-5c-2a — the contract-twice = contract-once supply.**  The single graph-class obligation
behind `right_eq`, packaged as a supply field (the genuine de-contraction composition law). -/
structure ResolvedContractTwiceOnceSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G) where
  /-- Contracting the input outer forest once equals contracting the selected outer then its quotient
  subforest (as resolved graph classes). -/
  contract_class_eq : ∀ s : ResolvedCoassocSplitChoice D G,
    (branchRightGraph s).toResolvedClass = (imageInnerRightGraph imageOf s).toResolvedClass

/-- `right_eq` for every split choice, from the contract-twice = contract-once supply. -/
theorem ResolvedContractTwiceOnceSupply.right_eq (R : ResolvedCoassocInnerRightSupply D G)
    {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}
    (C : ResolvedContractTwiceOnceSupply D G imageOf) (s : ResolvedCoassocSplitChoice D G) :
    (D.supply G).rightTerm s.1 = R.innerRightTerm (imageOf s) :=
  right_eq_of_contract_class_eq R imageOf s (C.contract_class_eq s)

end GaugeGeometry.QFT.Combinatorial
