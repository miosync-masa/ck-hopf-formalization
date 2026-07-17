import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocMultiStarRegionTagValue
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForwardQuotientHEqScout

/-!
# R-6c-body-344 — quotient partition core + the 290-independent forward-quotient assembly (PROVED)

Three-hundred-and-forty-fourth genuine-body step — the floor plan for culprit B (forward quotient).  Two
things: the pure-filter codomain partition `rightDomain z ∪ forestDomain z = z.2.1.elements`, and the
`290`-independent HEq assembly `ResolvedForwardQuotientMultiSupply`, whose sole residual is the survivor⊔remnant
elements bridge — from which `forward_quotient_value_multi` is DERIVED via body-203's `heq_forestIdx` and
body-341's outer equality (`houter`), with NO detour through the false body-289/290 `Geom` supply.

## The decomposition (dual to body-341's outer)

```text
z.2.1.elements = rightDomain z ∪ forestDomain z            -- pure filter partition (this body)
(V.quotientForestRaw recovered).1 = rightSurvivorForest ∪ remnantForest   -- V.union_eq
```

so the elements bridge factors as `rightSurvivorForest.elements = rightDomain z` (survivor alignment, body-345)
and `remnantForest.elements = forestDomain z` (remnant alignment, body-346), assembled in body-347.  The lift
from the elements bridge to `HEq (V.quotientForestRaw recovered) z.2` is `heq_forestIdx` fed by the two graph
sides: `houter` (= body-341's `selectedOuterRawOf(recovered) = z.1.1`) and the elements HEq.

Landed (all axiom-clean):

* `rightDomain_union_forestDomain` — `rightDomain z ∪ forestDomain z = z.2.1.elements` (filter partition);
* `rightDomain_disjoint_forestDomain` — the two are disjoint (complementary filters);
* `ResolvedForwardQuotientMultiSupply` — the 290-independent assembly (sole field: the elements HEq);
* `forward_quotient_value_multi` — `HEq (V.quotientForestRaw recovered) z.2` from the elements HEq + `houter`.

Per the HALT: only the partition and the assembly type + its `heq_forestIdx` derivation are built; the two
collection alignments (bodies 345/346) and the final union assembly (body-347) are NOT entered; no forward
round-trip, no carrier membership re-request, no body-289/290 `Geom`.  No facade, no flat term, no `forgetHopf`,
no rep/perm, and NO `promote_collapse` / singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

variable {D : ResolvedCoproductProperForestData}

set_option linter.unusedSectionVars false

/-- **R-6c-body-344 — the codomain partition.**  The star-avoiding survivors and the star-touching remnants
exhaust `z.2.1`'s components (a pure filter partition on `Disjoint · starOfZ`). -/
theorem rightDomain_union_forestDomain {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) :
    rightDomain z ∪ forestDomain z = z.2.1.elements := by
  ext δ
  simp only [rightDomain, forestDomain, Finset.mem_union, Finset.mem_filter]
  tauto

/-- **R-6c-body-344 — the codomain partition is disjoint** (complementary filters). -/
theorem rightDomain_disjoint_forestDomain {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) :
    Disjoint (rightDomain z) (forestDomain z) := by
  rw [Finset.disjoint_left]
  intro δ hr hf
  exact (Finset.mem_filter.mp hf).2 (Finset.mem_filter.mp hr).2

/-- **R-6c-body-344 — the 290-independent forward-quotient assembly.**  Its sole residual is the survivor⊔remnant
elements bridge (`HEq (V.quotientForestRaw recovered).1.elements z.2.1.elements`), discharged by bodies 345/346/347;
`forward_quotient_value_multi` lifts it to the `ForestIdx` HEq. -/
structure ResolvedForwardQuotientMultiSupply {Fmem : ResolvedSelectedOuterFilteredMemSupply D}
    (V : ResolvedConcreteSummandValueSupply D) (T : ResolvedRegionTagValueSupply Fmem V) where
  /-- The survivor⊔remnant elements bridge = the codomain forest components (heterogeneous over the graph). -/
  quotient_elements_heq : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    HEq (V.quotientForestRaw (T.recoveredPreimageValue z)).1.elements z.2.1.elements

/-- **R-6c-body-344 — body-285's leaf 2 (value, multi-star), 290-independent.**  `heq_forestIdx` fed by
body-341's outer equality (`houter`) and the assembly's elements bridge — no false `Geom`. -/
theorem forward_quotient_value_multi {Fmem : ResolvedSelectedOuterFilteredMemSupply D}
    {V : ResolvedConcreteSummandValueSupply D} {T : ResolvedRegionTagValueSupply Fmem V}
    (Q : ResolvedForwardQuotientMultiSupply V T)
    (houter : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
      (resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf (T.recoveredPreimageValue z) = z.1.1)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) :
    HEq (V.quotientForestRaw (T.recoveredPreimageValue z)) z.2 :=
  heq_forestIdx (V.quotientForestRaw (T.recoveredPreimageValue z)) z.2 (houter z)
    (Q.quotient_elements_heq z)

end GaugeGeometry.QFT.Combinatorial
