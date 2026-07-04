import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocContractTwiceQuotEq
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightEq
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocContractTwice

/-!
# R-6c-body-111 — quot_eq from the existing RIGHT geometry: the contract-twice class eq reconnects, DONE

Hundred-and-eleventh genuine-body step, wiring body-110's class-equality leaf to the EXISTING HEART-6a
contract-twice geometry (bodies 27–49).  The finding: the map data's `*_quot_eq` is discharged, with NO new
content, by the already-built `ResolvedContractTwiceOnceGeometrySupply` — the three-field retarget geometry
returns to the raid boss and closes the hardest summand-agreement equality.

## The wiring (PROVED)

`resolved_quot_eq_from_contract_geometry`: with `imageOf q := ⟨selectedOuterOf q, quotientRaw q⟩` (the forward
map as a `ResolvedCoassocQuotientImage`), the existing geometry supply's class equality discharges `quot_eq`:

```text
Geo : ResolvedContractTwiceOnceGeometrySupply D G (fun q => ⟨selectedOuterOf q, quotientRaw q⟩)
  ⊢  rightTerm q.1 = rightTerm ⟨quotientRaw q, quotient_mem q⟩
```

by `resolved_rightTerm_eq_of_class_eq q.1 ⟨quotientRaw q, quotient_mem q⟩ (Geo.contract_class_eq q)`.  The
definitional matching is exact:

* `branchRightGraph q = q.1.1.contractWithStars (starOf G q.1.1)` — the graph of `rightTerm q.1`;
* `imageInnerRightGraph (⟨selectedOuterOf q, quotientRaw q⟩) q = quotientRaw q.contractWithStars (starOf
  (selectedOuterOf q.contractWithStars) …)` — the graph of `rightTerm ⟨quotientRaw q, _⟩`;

so `Geo.contract_class_eq q` is precisely body-110's `class_eq`, and `resolved_rightTerm_eq_of_class_eq` bridges
it to the `*_quot_eq` field.  (`Geo` derives the class equality from `vertices_eq` / `internalEdges_eq` /
`externalLegs_eq` up to `mapPerm (starPerm q)` — the bodies-27–49 retargetVertex three-route geometry.)

## Consequence: the hardest summand-agreement equality is not new

`ResolvedContractTwiceOnceGeometrySupply` was BUILT (bodies 27–49) as the de-contraction composition law
(`branchRightGraph ≅ imageInnerRightGraph` up to a star permutation).  Body-111 shows it plugs DIRECTLY into the
forest-block map's `mixed_quot_eq` / `forest_quot_eq`.  So the contract-twice generator identity — the geometric
crux of the summand agreement — is supplied by existing machinery; the remaining `*_quot_eq` obligation is just
"supply `ResolvedContractTwiceOnceGeometrySupply` with `imageOf` = the forward map", i.e. the three retarget
field equalities (already the subject of bodies 27–49).

Per the HALT: the existing class-level `contract_class_eq` is used (not the term-level `right_eq` reversed);
`quot_eq` is supplied from the geometry supply; no retarget / perm / edge fact is reproved.

Landed:

* `resolved_quot_eq_from_contract_geometry` — `*_quot_eq` from the existing
  `ResolvedContractTwiceOnceGeometrySupply` (PROVED); discharges `mixed_quot_eq` and `forest_quot_eq`.

Toolkit body (like body-110), no new supply.  No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- **R-6c-body-111 — `*_quot_eq` from the existing contract-twice geometry.**  With the forward map as
`imageOf`, the bodies-27–49 `ResolvedContractTwiceOnceGeometrySupply` class equality discharges the quotient
generator identity `rightTerm q.1 = rightTerm B`.  Discharges `mixed_quot_eq` and `forest_quot_eq`. -/
theorem resolved_quot_eq_from_contract_geometry
    (imageSupply : ResolvedCoassocSelectedOuterImageSupply D G)
    (quotientRaw : ∀ (q : ForestBlockDomType D G),
      ResolvedAdmissibleSubgraph ((imageSupply.selectedOuterOf q).1.contractWithStars
        (D.starOf G (imageSupply.selectedOuterOf q).1)))
    (quotient_mem : ∀ (q : ForestBlockDomType D G),
      quotientRaw q ∈ D.carrier ((imageSupply.selectedOuterOf q).1.contractWithStars
        (D.starOf G (imageSupply.selectedOuterOf q).1)))
    (Geo : ResolvedContractTwiceOnceGeometrySupply D G
      (fun q => ⟨imageSupply.selectedOuterOf q, quotientRaw q⟩))
    (q : ForestBlockDomType D G) :
    (D.supply G).rightTerm q.1
      = (D.supply ((imageSupply.selectedOuterOf q).1.contractWithStars
          (D.starOf G (imageSupply.selectedOuterOf q).1))).rightTerm ⟨quotientRaw q, quotient_mem q⟩ :=
  resolved_rightTerm_eq_of_class_eq q.1 ⟨quotientRaw q, quotient_mem q⟩ (Geo.contract_class_eq q)

end GaugeGeometry.QFT.Combinatorial
