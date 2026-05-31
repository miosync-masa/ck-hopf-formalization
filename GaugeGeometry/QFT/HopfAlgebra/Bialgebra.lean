import GaugeGeometry.QFT.HopfAlgebra.Coassoc
import Mathlib.RingTheory.Bialgebra.Basic

/-!
# Coalgebra and Bialgebra instances on `HopfH`  [Sprint E Stages 2 + 3]

This file assembles the Mathlib `Coalgebra ℚ HopfH` and `Bialgebra ℚ HopfH`
instances for the **forest** strict coproduct artifact
`coproduct_strict_forest`. The connected-only `coproduct_strict` is
internal Plan-D Hybrid scaffolding and is intentionally **not** used as
the comultiplication: the comul is always `coproduct_strict_forest.toLinearMap`.

## Sprint E pipeline

* Stage 0 (`Coassoc.lean`): public facade `CoassocStrictForestH58Ready`
  carries the LinearMap-form coassociativity for `coproduct_strict_forest`.
  The internal `forestComponentSplitPhiIndexedBranchClassifier` machinery
  is hidden behind this facade.
* Stage 1 (`Counit.lean`): forest counit axioms
  `rTensor_counit_comp_coproduct_strict_forest` and
  `lTensor_counit_comp_coproduct_strict_forest` (Mathlib `Coalgebra`
  LinearMap shape).
* Stage 2 (this file): `Coalgebra ℚ HopfH` instance, named
  `instCoalgebraHopfHStrictForest`.
* Stage 3 (this file): `Bialgebra ℚ HopfH` instance via
  `Bialgebra.mk'`, named `instBialgebraHopfHStrictForest`.

## Sprint E facade discharge (open task)

`CoassocStrictForestH58Ready` is a **facade** typeclass: its only field
is the LinearMap-form coassociativity equality. Sprint D step 161 already
proved this canonically from `forestComponentSplitPhiIndexedBranchClassifier`
+ canonical RHS branch decision data, but the canonical instance
constructor has not yet been wired to the facade. Before the **final
axiom audit** (after H6.8 `HopfAlgebra ℚ HopfH` instance), the facade
must be discharged via the canonical classifier path.

Until that discharge, the `Coalgebra` and `Bialgebra` instances below
require `[CoassocStrictForestH58Ready]` as an explicit hypothesis. Once
the facade is discharged, this hypothesis becomes globally satisfiable
and the instances become unconditional.

**The connected-only `coproduct_strict` MUST NOT be used in this file.**
That artifact has no closed coassociativity proof in Sprint D (the
naive bijection's image is strictly contained in the RHS sum, see
`Coassoc.lean` step 1 `contractRestrict_star_mem`). Its role is purely
internal scaffolding for the Plan-D Hybrid construction. The comul of
the public Bialgebra is always `coproduct_strict_forest.toLinearMap`.
-/

open scoped TensorProduct

namespace GaugeGeometry.QFT.Combinatorial

section StrictForestInstance

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
         [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
         [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
         [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
         [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
         [IsDivergencePreservedByAdmissibleForestContract]

/-- **Sprint E Stage 2 — `Coalgebra ℚ HopfH` instance** for the forest
strict coproduct artifact.

* `comul := coproduct_strict_forest.toLinearMap`
* `counit := counit.toLinearMap`
* `coassoc` from the Sprint D facade `CoassocStrictForestH58Ready`
* counit axioms `rTensor`/`lTensor` from forest H5.6F/H5.7F

The `[CoassocStrictForestH58Ready]` hypothesis is a Sprint E facade
that will be discharged from the canonical
`forestComponentSplitPhiIndexedBranchClassifier` constructor before the
final axiom audit.

The connected-only `coproduct_strict` is deliberately NOT used here. -/
noncomputable instance instCoalgebraHopfHStrictForest
    [CoassocStrictForestH58Ready] :
    Coalgebra ℚ HopfH where
  comul := coproduct_strict_forest.toLinearMap
  counit := counit.toLinearMap
  coassoc := coassoc_strict_forest_linearMap
  rTensor_counit_comp_comul := rTensor_counit_comp_coproduct_strict_forest
  lTensor_counit_comp_comul := lTensor_counit_comp_coproduct_strict_forest

/-- **Sprint E Stage 3 — `Bialgebra ℚ HopfH` instance** assembled via
`Bialgebra.mk'`.

The four required field-level facts are:

* `counit_one`: `counit (1 : HopfH) = 1` (existing H5.3 `counit_one`,
  which holds at the AlgHom level and transports to LinearMap).
* `counit_mul`: counit is multiplicative (existing `counit_mul`).
* `comul_one`: `coproduct_strict_forest 1 = 1` (existing H4.10F
  `coproduct_strict_forest_one`).
* `comul_mul`: coproduct is multiplicative (existing H4.11F
  `coproduct_strict_forest_mul`).

Each fact is shown for the AlgHom and transports to the LinearMap form
that `Bialgebra.mk'` consumes through the underlying `Coalgebra` carrier
(the `instCoalgebraHopfHStrictForest` instance above). -/
noncomputable instance instBialgebraHopfHStrictForest
    [CoassocStrictForestH58Ready] :
    Bialgebra ℚ HopfH :=
  Bialgebra.mk' ℚ HopfH
    (counit_one := counit_one)
    (counit_mul := fun {a b} => counit_mul a b)
    (comul_one := coproduct_strict_forest_one)
    (comul_mul := fun {a b} => coproduct_strict_forest_mul a b)

end StrictForestInstance

end GaugeGeometry.QFT.Combinatorial
