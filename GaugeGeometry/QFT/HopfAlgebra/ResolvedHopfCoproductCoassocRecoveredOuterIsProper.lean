import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSelectedOuterIsProper
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecoveredOuterNonempty

/-!
# R-6c-body-266 — circularity correction + raw recovered-outer `IsProperForest` (PROVED)

Two-hundred-and-sixty-sixth genuine-body step, a **correction** to body-265 plus the genuine, non-circular content it
should have delivered.

## Circularity correction (body-265's `.2` bypass is a packaging illusion)

Body-265 claimed the live sum bypasses the certificate because `(unionOuter z).2` supplies carrier membership "for
free".  **That is circular.**  `unionOuter z` is *defined* as `⟨rawRegionUnion z, recovered_outer_mem z⟩`
(`OuterUnionConstruction.lean:85` — its `.2` field is the body-159 leaf itself).  So

```text
recovered_outer_mem  →  unionOuter.2  →  ext_elements transport  →  recovered_outer_mem
```

is a one-loop cycle; the abstract-supply packaging hides it but the dependency graph is the same.  Likewise the
"every live `z` is a forward image" route is circular: constructing the forward image's outer as a carrier subtype
already needs the recovered membership.  So the correct status is:

* generic `recovered_eq` — **honest leaf** (body-265, forget not globally injective — this part stands);
* the certificate route — sufficient but needs the section condition;
* the `unionOuter.2` bypass — **packaging illusion**, NOT a discharge;
* "recovered membership is off the critical path" — **NOT established**.

This is the same trap as the total `selectedOuter` (bodies 128/249): a subtype `.2` is not free — value and membership
must be **separated**.  We won there by separating the raw value from the membership (the value root, body-252); the
same move applies here.

## What IS non-circular: the raw recovered outer's `IsProperForest`

The raw recovered outer is `(unionOuter (fwdMap S q)).1` — the **value** (no carrier tag consumed).  Its
`IsProperForest` is proved from the **domain outer** `q.1.1`'s carrier properness (body-264's
`isProperForest_of_elements_eq` + the body-168 partition elements-equality), using `q.1.2` — the *domain* membership,
NOT the recovered one.  This is genuinely non-circular and is exactly the `isProper` the certificate needs for `Y`.

```lean
recoveredOuter_isProperForest (P) (A) (q) : (Region.Union.unionOuter (fwdMap S q)).1.IsProperForest
```

## The two real options for recovered membership (body-267+)

1. **Rebuild the carrier** as a finite index of *all* resolved proper forests, so `IsProperForest → membership` holds
   (body-264's 5/5 `IsProperForest` then discharges membership directly).  For `Y` this needs the raw region-union
   `IsProperForest` on a generic `z` as well.
2. **Keep the forget-image carrier** and prove the shape-specific `recovered_eq` / canonical section
   (`A = ofForgetForest A.forget`) for the recovered/selected outer.

Per the HALT: only the non-circular raw `IsProperForest` is proved; the membership leaf is correctly left open with the
two options named; no `recovered_eq`, no false bypass.  No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]
  [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}
  {S : ResolvedConcreteSummandBundleSupply D}
  {Region : ResolvedRegionChoiceRoundTripSupply D S}

set_option linter.unusedSectionVars false

/-- **R-6c-body-266 — the raw recovered outer is a proper forest on the forward image** (non-circular).  Its elements
equal the domain outer `q.1.1.elements` (body-168 partition + `union_eq`), and `q.1.1` is a proper carrier member
(`q.1.2`), so the raw recovered outer `(unionOuter (fwdMap S q)).1` is proper.  Uses the *domain* membership, not the
recovered one — no `recovered_outer_mem` / `recovered_eq`. -/
theorem recoveredOuter_isProperForest (P : ResolvedCarrierProperProvider D)
    (A : ResolvedRecoveredRegionMembershipAssemblySupply D S Region)
    (q : ForestBlockDomType D G) :
    (Region.Union.unionOuter (fwdMap S q)).1.IsProperForest := by
  have hunion : (Region.Union.unionOuter (fwdMap S q)).1.elements = q.1.1.elements := by
    rw [Region.Union.union_eq (fwdMap S q),
      A.toRecoveredOuterRegionPartitionSupply.recovered_region_partition q]
  exact isProperForest_of_elements_eq P q.1 _ hunion

end GaugeGeometry.QFT.Combinatorial
