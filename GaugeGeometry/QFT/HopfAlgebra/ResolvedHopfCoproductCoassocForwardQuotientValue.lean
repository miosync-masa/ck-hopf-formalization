import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForwardOuterValue
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForwardQuotientHEqScout
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocQuotientElementsRecovery
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSurvivorElementsRecovery

/-!
# R-6c-body-290 — forward quotient round-trip reduced to two element bridges (PROVED)

Two-hundred-and-ninetieth genuine-body step — the value-root re-key of the total-root forward quotient HEq
(bodies 203-208).  It reduces body-285's leaf 2 (`forward_quotient_value`,
`HEq (V.quotientForestRaw (recoveredPreimageValue z)) z.2`) to TWO honest generic-`z` element membership bridges
(`survivor_mem_value`, `remnant_mem_value`), proving everything else through the generic S-free HEq transports
(`heq_forestIdx` body-203, `heq_of_membership_split` body-204, `heq_finset_of_mem_iff` body-206) + body-289's outer
equality.

## No circularity

The right-hand split `z.2.1.elements = rightDomain z ∪ forestDomain z` is the pure complementary star-filter partition
(generic in `z`); the left-hand split is `V.union_eq (recoveredPreimageValue z)` (survivor ∪ remnant); the ambient
`ForestIdx` graph transport is body-289's `forward_outer_value` (`selectedOuterRawOf (recoveredPreimageValue z) =
z.1.1`).  NONE uses the forward round-trip `fwd q = z` — body-274's fwd-direction `rightDomain_value_mem` (which WOULD be
circular) is NOT on this path.

## The two element bridges

```text
survivor_mem_value : HEq x₁ x₂ → (x₁ ∈ survivor(recovered).elements ↔ x₂ ∈ rightDomain z)   -- tag-reducible (inl false ⟷ star-avoiding)
remnant_mem_value  : HEq x₁ x₂ → (x₁ ∈ remnant(recovered).elements  ↔ x₂ ∈ forestDomain z)  -- genuine de-contraction (the one heavy leaf)
```

Per the HALT: `forward_quotient_value` is reduced to these two membership bridges; the generic HEq assembly is proved via
the reused S-free transports; `forestTag_agrees` (body-288) is NOT needed (a component-set HEq, not an exact-`B` match);
body-289's `forward_outer_value` supplies the graph transport; the assembly body is next.  No `S` / `Forward` / legacy in
any declaration type.  No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData}

set_option linter.unusedSectionVars false

/-- **R-6c-body-290 — the forward quotient geometry supply.**  Body-289's forward-outer geometry (for the graph
transport) + the two generic-`z` survivor / remnant element membership bridges. -/
structure ResolvedForwardQuotientValueGeometrySupply (F : ResolvedSelectedOuterFilteredMemSupply D)
    (V : ResolvedConcreteSummandValueSupply D) where
  /-- The forward-outer geometry (body-289): supplies `forward_outer_value` (the outer transport) + the data. -/
  Geom : ResolvedForwardOuterValueGeometrySupply F V
  /-- The survivor membership bridge (tag-reducible: `inl false` ⟷ star-avoiding). -/
  survivor_mem_value : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (x₁ : ResolvedFeynmanSubgraph (ResolvedCoassocSplitChoice.selectedOuterContractGraph
        (Geom.Data.Tags.recoveredPreimageValue z)))
    (x₂ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))),
    HEq x₁ x₂ →
    (x₁ ∈ (V.Survivor.survivor.rightSurvivorForest (Geom.Data.Tags.recoveredPreimageValue z)).elements
      ↔ x₂ ∈ rightDomain z)
  /-- The remnant membership bridge (genuine de-contraction geometry). -/
  remnant_mem_value : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (x₁ : ResolvedFeynmanSubgraph (ResolvedCoassocSplitChoice.selectedOuterContractGraph
        (Geom.Data.Tags.recoveredPreimageValue z)))
    (x₂ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))),
    HEq x₁ x₂ →
    (x₁ ∈ (V.Remnant.remnant.remnantForest (Geom.Data.Tags.recoveredPreimageValue z)).elements
      ↔ x₂ ∈ forestDomain z)

namespace ResolvedForwardQuotientValueGeometrySupply

variable {F : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}

/-- **R-6c-body-290 — the quotient element sets are heterogeneously equal** (body-204 shape, value root). -/
theorem quotient_elements_heq_value (R : ResolvedForwardQuotientValueGeometrySupply F V)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) :
    HEq (V.quotientForestRaw (R.Geom.Data.Tags.recoveredPreimageValue z)).1.elements z.2.1.elements := by
  refine heq_of_membership_split (R.Geom.forward_outer_value z)
    (Q := (V.quotientForestRaw (R.Geom.Data.Tags.recoveredPreimageValue z)).1.elements)
    (Z := z.2.1.elements)
    (surv := (V.Survivor.survivor.rightSurvivorForest (R.Geom.Data.Tags.recoveredPreimageValue z)).elements)
    (rem := (V.Remnant.remnant.remnantForest (R.Geom.Data.Tags.recoveredPreimageValue z)).elements)
    (rightDom := rightDomain z) (forestDom := forestDomain z)
    ?_ ?_
    (heq_finset_of_mem_iff (R.Geom.forward_outer_value z) (R.survivor_mem_value z))
    (heq_finset_of_mem_iff (R.Geom.forward_outer_value z) (R.remnant_mem_value z))
  · intro x
    rw [V.union_eq (R.Geom.Data.Tags.recoveredPreimageValue z),
      ResolvedAdmissibleSubgraph.union_elements]
    convert Finset.mem_union using 2
  · intro x
    simp only [rightDomain, forestDomain, Finset.mem_filter]
    tauto

/-- **R-6c-body-290 — body-285's leaf 2 from the two element bridges** (`heq_forestIdx`, body-203). -/
theorem forward_quotient_value (R : ResolvedForwardQuotientValueGeometrySupply F V)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) :
    HEq (V.quotientForestRaw (R.Geom.Data.Tags.recoveredPreimageValue z)) z.2 :=
  heq_forestIdx (V.quotientForestRaw (R.Geom.Data.Tags.recoveredPreimageValue z)) z.2
    (R.Geom.forward_outer_value z) (R.quotient_elements_heq_value z)

end ResolvedForwardQuotientValueGeometrySupply

end GaugeGeometry.QFT.Combinatorial
