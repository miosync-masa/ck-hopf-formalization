import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaRegionBridgeAssembly
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocOuterUnionRegionTagValue

/-!
# R-6c-body-476 — the alpha region closure + carrier-tagged outer value (stage 2 of the tag-chain mirror) (PARALLEL)

Four-hundred-and-seventy-sixth genuine-body step — the SECOND staged mirror: the coherent region closure over the alpha
value root (holding the body-475 alpha assembly as the SAME owner) and the carrier-tagged recovered outer value.  Fully
mechanical — the three disjointness leaves and `recovered_raw_mem` read `Assembly.Region` / `Assembly.Left` DIRECTLY
(they are `z`-keyed and V-independent), so no region maps are re-input.

* `ResolvedRegionAlphaValueClosureSupply` — the 6-field alpha closure (alpha assembly + `selected` + three disjointness +
  `recovered_raw_mem`);
* `ResolvedRegionAlphaValueClosureSupply.unionOuterAlphaValue` — the carrier-tagged recovered outer, value =
  `recoveredRawUnion (Left.leftResidual z) (Region.rightRecovered z) (Region.forestRecovered z) …`, membership =
  `recovered_raw_mem z`;
* `unionOuterAlphaValue_val` — the projection anchor (`rfl`);
* `ResolvedRegionValueClosureSupply.toAlpha` — the legacy adapter (`Assembly := C.Assembly.toAlpha`, everything else
  verbatim; the disjointness/membership fields are `z`-keyed so they transport by `rfl`);
* `toAlpha_unionOuterAlphaValue_val` — the legacy compatibility (`(C.toAlpha.unionOuterAlphaValue z).1 =
  (C.unionOuterValue z).1`, `rfl`).

Per the HALT/guards: NO tags / `forestTag` / exclusivity / recover choice; the filtered recovered witness is NOT issued;
the canonical closure geometry is NOT re-proved; `recovered_raw_mem` is NOT re-derived from `W'`; the old closure is NOT
edited in place; NO `quot_eq`, NO `W'` membership, NO new geometry; strict `StarProm` / `InnerStarRaw` NOT restored;
body-445 stays a valid conditional.  NOT the unconditional theorem.  No facade, no flat term, no `forgetHopf`, no
rep/perm, and NO `promote_collapse` / singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

variable {D : ResolvedCoproductProperForestData}

/-- **R-6c-body-476 — the alpha region closure.**  The body-475 alpha assembly plus the selected-outer carrier closure,
the three region disjointnesses, and the raw recovered-outer carrier membership. -/
structure ResolvedRegionAlphaValueClosureSupply
    (F : ResolvedSelectedOuterFilteredMemSupply D)
    (V : ResolvedFilteredConcreteSummandValueSupply D) where
  /-- The shared alpha value bridge assembly (body-475). -/
  Assembly : ResolvedRecoveredRegionAlphaValueBridgeAssemblySupply F V
  /-- The filtered selected-outer carrier closure (body-245). -/
  selected : ResolvedSelectedOuterFilteredMemSupply D
  /-- Left / right pairwise disjointness of the assembly's maps. -/
  left_right_disjoint : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    ∀ γ ∈ (Assembly.Left.leftResidual z).elements, ∀ δ ∈ (Assembly.Region.rightRecovered z).elements,
      γ ≠ δ → γ.Disjoint δ
  /-- Left / forest pairwise disjointness of the assembly's maps. -/
  left_forest_disjoint : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    ∀ γ ∈ (Assembly.Left.leftResidual z).elements, ∀ δ ∈ (Assembly.Region.forestRecovered z).elements,
      γ ≠ δ → γ.Disjoint δ
  /-- Right / forest pairwise disjointness of the assembly's maps. -/
  right_forest_disjoint : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    ∀ γ ∈ (Assembly.Region.rightRecovered z).elements, ∀ δ ∈ (Assembly.Region.forestRecovered z).elements,
      γ ≠ δ → γ.Disjoint δ
  /-- The raw recovered outer (assembly's maps) lies in the carrier. -/
  recovered_raw_mem : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    recoveredRawUnion (Assembly.Left.leftResidual z) (Assembly.Region.rightRecovered z)
        (Assembly.Region.forestRecovered z)
        (left_right_disjoint z) (left_forest_disjoint z) (right_forest_disjoint z) ∈ D.carrier G

/-- **R-6c-body-476 — the carrier-tagged recovered outer value.** -/
noncomputable def ResolvedRegionAlphaValueClosureSupply.unionOuterAlphaValue
    {F : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedFilteredConcreteSummandValueSupply D}
    (C : ResolvedRegionAlphaValueClosureSupply F V) {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType D G) : {A' : ResolvedAdmissibleSubgraph G // A' ∈ D.carrier G} :=
  ⟨recoveredRawUnion (C.Assembly.Left.leftResidual z) (C.Assembly.Region.rightRecovered z)
      (C.Assembly.Region.forestRecovered z)
      (C.left_right_disjoint z) (C.left_forest_disjoint z) (C.right_forest_disjoint z),
    C.recovered_raw_mem z⟩

/-- **R-6c-body-476 — the tagged-outer projection anchor** (`rfl`). -/
@[simp] theorem ResolvedRegionAlphaValueClosureSupply.unionOuterAlphaValue_val
    {F : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedFilteredConcreteSummandValueSupply D}
    (C : ResolvedRegionAlphaValueClosureSupply F V) {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType D G) :
    (C.unionOuterAlphaValue z).1
      = recoveredRawUnion (C.Assembly.Left.leftResidual z) (C.Assembly.Region.rightRecovered z)
          (C.Assembly.Region.forestRecovered z)
          (C.left_right_disjoint z) (C.left_forest_disjoint z) (C.right_forest_disjoint z) :=
  rfl

/-- **R-6c-body-476 ∎ — the legacy adapter into the alpha closure over `V.toFiltered`.** -/
def ResolvedRegionValueClosureSupply.toAlpha
    {F : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}
    (C : ResolvedRegionValueClosureSupply F V) : ResolvedRegionAlphaValueClosureSupply F V.toFiltered where
  Assembly := C.Assembly.toAlpha
  selected := C.selected
  left_right_disjoint := C.left_right_disjoint
  left_forest_disjoint := C.left_forest_disjoint
  right_forest_disjoint := C.right_forest_disjoint
  recovered_raw_mem := C.recovered_raw_mem

/-- **R-6c-body-476 — the legacy compatibility anchor** (`rfl`). -/
theorem ResolvedRegionValueClosureSupply.toAlpha_unionOuterAlphaValue_val
    {F : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}
    (C : ResolvedRegionValueClosureSupply F V) {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType D G) :
    (C.toAlpha.unionOuterAlphaValue z).1 = (C.unionOuterValue z).1 :=
  rfl

end GaugeGeometry.QFT.Combinatorial
