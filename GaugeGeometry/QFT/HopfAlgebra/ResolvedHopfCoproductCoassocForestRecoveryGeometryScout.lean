import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestRecoveryGeometry
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRegionConstructionFromSector

/-!
# R-6c-body-183 — forest recovery geometry scout: body-179 split into three precise leaves

Hundred-and-eighty-third genuine-body step, a structure audit + decomposition of body-179's forest-recovery box
before its deepest leaf is attacked.  The audit (below) matched the two fielded facts of body-179
(`forestRecovered_mem`, `promoted_region_eq`) against the existing sector machinery; the decomposition then splits
body-179 into three precise leaves and **proves the glue**, isolating the one genuinely deep de-contraction leaf.

## Audit — the existing machinery (exact types)

```text
forestRecovered z       = ofElements ((forestDomain z).attach.image (componentToForest z))     (body-156)
  forestRecovered_elements_eq : (T.forestRecovered z).elements
                              = (forestDomain z).attach.image (T.componentToForest z)   (rfl, simp)
forestDomain z          = z.2.1.elements.filter (¬ Disjoint δ.vertices (starOfZ z))            (star-touching remnants of B)
componentToForest z     : {x // x ∈ forestDomain z} → ResolvedFeynmanSubgraph G                (remnant ↦ forest parent, body-156)
      (concrete version: Classical.choose of forest_surj; inverse of Forward.forestToComponent)

promotedOf recovered .elements = recovered.promotedElements                                    (rfl)
  promotedElements    = unionOuter.elements.attach.biUnion promotedComponentElements
  promotedComponentElements γ = match choiceAt γ with inl _ => ∅ | inr B => (promote γ.1 B.1).elements
  promote γ B         = ofElements (B.elements.image (fun δ => γ.promote δ))                    (de-contraction into G)
```

So the two views are two projections of ONE round-trip:

* **`forestRecovered_mem` (classifier view)** — `forestRecovered` is the `componentToForest` image of the remnants;
  its components are exactly the forest-choice **parents**, so `γ ∈ forestRecovered ↔ γ ∈ A ∧ representedByForest`;
* **`promoted_region_eq` (selected-outer view)** — `promotedOf recovered` is the `biUnion` of `promote γ Bᵧ` over
  the `inr`-tagged components; the identity says this de-contracted forest equals the `componentToForest` parents.

The genuinely deep fact is that the `biUnion` of the promoted sub-forests equals the `componentToForest` image
(`promoted_eq_forestRecovered`) — the `componentToForest` / `promote` de-contraction round-trip.  Everything else is
membership plumbing.

## The decomposition (three leaves, glue PROVED)

`ResolvedForestRecoveryDecompositionSupply D S Region` fields body-156's construction plus three leaves:

* `forestRecovered_eq` — the wiring bridge `(Region.Union.forestRecovered z).elements = (Construction.forestRecovered
  z).elements` (abstract union region ↔ body-156's `componentToForest` image; the `forestRecovered` twin of
  body-178's `leftResidual_eq`);
* `parent_mem_carrier` — a forest parent lands in the target outer `A` (`γ ∈ Construction.forestRecovered z → γ ∈
  z.1.1.elements`; shallow — the parent is a component of `A`);
* `promoted_eq_forestRecovered` — the deep round-trip `(promotedOf recovered).elements = (Construction.forestRecovered
  z).elements` (the `componentToForest` / `promote` de-contraction identity — the one hard leaf).

With `representedByForest z γ := γ ∈ (Construction.forestRecovered z).elements`, body-179's two facts are **PROVED**:

* `forestRecovered_membership` — `rw` the bridge, then `⟨parent_mem_carrier, id⟩` / `.2`;
* `promoted_region_equality` — `promoted_eq_forestRecovered.trans forestRecovered_eq.symm`.

`.toForestRecoveryGeometrySupply` produces body-179's `ResolvedForestRecoveryGeometrySupply`.  So body-179 is now
three leaves — two shallow (`forestRecovered_eq`, `parent_mem_carrier`) and one deep
(`promoted_eq_forestRecovered`) — and the next body can attack the shallowest first.

Per the HALT: the `componentToForest` inverse law body is not entered; `promoted_eq_forestRecovered` is fielded
(not forced); only the membership glue is proved.

Landed:

* `ResolvedForestRecoveryDecompositionSupply D S Region` — body-156's construction + the three leaves;
* `.forestRecovered_membership` — body-179's `forestRecovered_mem` (PROVED from the leaves);
* `.promoted_region_equality` — body-179's `promoted_region_eq` (PROVED from the leaves);
* `.toForestRecoveryGeometrySupply` — body-179's supply.

Scout / toolkit body (like body-178).  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-183 — the forest-recovery decomposition supply.**  Body-156's `componentToForest`-image
construction, the wiring bridge to the abstract union region, the parent-in-carrier fact, and the deep
`promote` / `componentToForest` de-contraction round-trip. -/
structure ResolvedForestRecoveryDecompositionSupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) (Region : ResolvedRegionChoiceRoundTripSupply D S) where
  /-- Body-156's forest region construction (the `componentToForest` image of the remnants). -/
  Construction : ResolvedRegionConstructionFromSectorSupply D S
  /-- Wiring bridge: the abstract union forest region agrees with body-156's construction (element level). -/
  forestRecovered_eq : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    (Region.Union.forestRecovered z).elements = (Construction.forestRecovered z).elements
  /-- A forest parent lands in the target outer `A` (shallow). -/
  parent_mem_carrier : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (γ : ResolvedFeynmanSubgraph G),
    γ ∈ (Construction.forestRecovered z).elements → γ ∈ z.1.1.elements
  /-- The deep round-trip: the promoted (de-contracted) forest equals the `componentToForest` parents. -/
  promoted_eq_forestRecovered : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    ((S.Forward.imageSupply G).promotedOf
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).elements
      = (Construction.forestRecovered z).elements

namespace ResolvedForestRecoveryDecompositionSupply

variable {S : ResolvedConcreteSummandBundleSupply D} {Region : ResolvedRegionChoiceRoundTripSupply D S}

/-- **R-6c-body-183 — body-179's `forestRecovered_mem` from the leaves** (`representedByForest := γ ∈
Construction.forestRecovered`). -/
theorem forestRecovered_membership (F : ResolvedForestRecoveryDecompositionSupply D S Region)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) (γ : ResolvedFeynmanSubgraph G) :
    γ ∈ (Region.Union.forestRecovered z).elements
      ↔ γ ∈ z.1.1.elements ∧ γ ∈ (F.Construction.forestRecovered z).elements := by
  rw [F.forestRecovered_eq z]
  constructor
  · intro h; exact ⟨F.parent_mem_carrier z γ h, h⟩
  · intro h; exact h.2

/-- **R-6c-body-183 — body-179's `promoted_region_eq` from the leaves.** -/
theorem promoted_region_equality (F : ResolvedForestRecoveryDecompositionSupply D S Region)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) :
    ((S.Forward.imageSupply G).promotedOf
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).elements
      = (Region.Union.forestRecovered z).elements :=
  (F.promoted_eq_forestRecovered z).trans (F.forestRecovered_eq z).symm

/-- **R-6c-body-183 — body-179's forest-recovery geometry supply from the decomposition.** -/
def toForestRecoveryGeometrySupply (F : ResolvedForestRecoveryDecompositionSupply D S Region) :
    ResolvedForestRecoveryGeometrySupply D S Region where
  representedByForest := fun {G} z γ => γ ∈ (F.Construction.forestRecovered z).elements
  forestRecovered_mem := fun {G} z γ => F.forestRecovered_membership z γ
  promoted_region_eq := fun {G} z => F.promoted_region_equality z

end ResolvedForestRecoveryDecompositionSupply

end GaugeGeometry.QFT.Combinatorial
