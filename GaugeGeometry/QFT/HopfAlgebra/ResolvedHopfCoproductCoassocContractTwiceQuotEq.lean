import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocQuotientForestTermFactors

/-!
# R-6c-body-110 — contract-twice quotient generator equality: `rightTerm A' = rightTerm B` from a class eq

Hundred-and-tenth genuine-body step, the LAST summand-agreement geometric piece: the quotient generator identity
`rightTerm A' = rightTerm B`.  It reduces to a single graph-CLASS equality — `(A'.contractWithStars).toResolvedClass
= (B.contractWithStars).toResolvedClass` — which is EXACTLY the contract-twice geometry already built in the
HEART-6a retarget machinery (bodies 27–49).  The earlier three-route / retarget three-field geometry reconnects
here.

## The reduction (PROVED)

`resolved_rightTerm_eq_of_class_eq`: for carrier forests `A ∈ carrier G`, `B ∈ carrier H`,

```text
(A.contractWithStars starOf).toResolvedClass = (B.contractWithStars starOf').toResolvedClass
  →  rightTerm A = rightTerm B
```

Proof: `rightTerm A = X((A.contractWithStars).toResolvedHopfGen …)` and likewise for `B`; since `(…
toResolvedHopfGen h).val = (…).toResolvedClass` (`rfl`), the class equality gives the two generators equal
(`Subtype.ext`), hence the `X`s equal (`congr`).  With `A = q.1` and `B = quotientForest q`, `H = A_target
.contractWithStars`, this discharges BOTH `mixed_quot_eq` and `forest_quot_eq`.

## The reconnection to bodies 27–49

`rightTerm A' = rightTerm B` is precisely the existing `ResolvedContractTwiceClassDataSupply.right_eq`
(`ClassDataSupply` 83, `rightTerm s.1 = innerRightTerm (imageOf s)`, and `innerRightTerm z = resolvedForestRightTerm
z.quotientForest …` IS `rightTerm B`) — and its `contract_class_eq`
(`ResolvedContractTwiceOnceGeometrySupply.contract_class_eq`, `ContractTwice` 73) is the class equality
`(branchRightGraph s).toResolvedClass = (imageInnerRightGraph imageOf s).toResolvedClass`, derived from THREE
field equalities up to a star permutation:

* `vertices_eq` / `internalEdges_eq` / `externalLegs_eq` — the branch (`A'` contracted in `G`) and image (`B`
  contracted in the quotient) graphs agree up to `mapPerm (starPerm s)`.

So the double-contraction `A'.contractWithStars-in-G = B.contractWithStars-in-quotient` (up to relabeling) — the
`retargetVertex` / three-route geometry of bodies 27–49 — is the sole remaining content of the quotient
generator identity.  `resolved_rightTerm_eq_of_class_eq` is the bridge from that class equality to the map data's
`*_quot_eq` fields.

## Summand agreement complete (modulo geometry)

With this, all THREE summand-agreement product/generator identities are reduced to selection/geometry facts:

| identity | reduced to |
|---|---|
| `*_left_eq` (`∏ leftFactor = leftTerm A_target`) | `left_primitive` + `promoted` + `hdisj` (body-108) |
| `*_right_eq` (`∏ rightFactor = leftTerm B`) | `right_primitive` + `remnant` + `union_eq` + `hdisj` (body-109) |
| `*_quot_eq` (`rightTerm A' = rightTerm B`) | contract-twice class equality (body-110, this) |

Per the HALT: the generator identity is reduced to a class equality (`resolved_rightTerm_eq_of_class_eq`, PROVED);
the class equality itself is NOT proved (it is the existing bodies-27–49 retarget three-field geometry); no
`retargetVertex` detail is entered.

Landed:

* `resolved_rightTerm_eq_of_class_eq` — `rightTerm A = rightTerm B` from the contract-twice class equality
  (PROVED); discharges `mixed_quot_eq` and `forest_quot_eq`.

Toolkit body (like body-103/107/108/109), no new supply.  No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G H : ResolvedFeynmanGraph}

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- **R-6c-body-110 — the quotient generator identity from a contract-twice class equality.**  If the two
star-contraction quotients have the same resolved class, their right terms agree.  Discharges both
`mixed_quot_eq` and `forest_quot_eq`; the class equality is the bodies-27–49 retarget geometry. -/
theorem resolved_rightTerm_eq_of_class_eq
    (A : {A : ResolvedAdmissibleSubgraph G // A ∈ D.carrier G})
    (B : {B : ResolvedAdmissibleSubgraph H // B ∈ D.carrier H})
    (class_eq : (A.1.contractWithStars (D.starOf G A.1)).toResolvedClass
      = (B.1.contractWithStars (D.starOf H B.1)).toResolvedClass) :
    (D.supply G).rightTerm A = (D.supply H).rightTerm B := by
  show MvPolynomial.X ((A.1.contractWithStars (D.starOf G A.1)).toResolvedHopfGen (D.hCD G A.1 A.2))
    = MvPolynomial.X ((B.1.contractWithStars (D.starOf H B.1)).toResolvedHopfGen (D.hCD H B.1 B.2))
  congr 1
  exact Subtype.ext class_eq

end GaugeGeometry.QFT.Combinatorial
