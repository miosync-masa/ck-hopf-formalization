import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestRecoveryGeometryScout

/-!
# R-6c-body-185 — forest parent carrier: `parent_mem_carrier` from a componentwise membership field

Hundred-and-eighty-fifth genuine-body step, discharging body-183's shallow `parent_mem_carrier` leaf — the last
light stone before the deep `promoted_eq_forestRecovered` round-trip.

## Why it must be freshly fielded (scout result)

`body-156`'s `componentToForest z : {x // x ∈ forestDomain z} → ResolvedFeynmanSubgraph G` returns a *bare*
subgraph, constrained only by `forestComponentCD` (connected-divergent) and `forestComponentDisjoint` (pairwise
disjoint) — **no** field ties its image to `z.1.1.elements`.  The genuine source-outer memberships that exist
(`OneStageStarIndex.hη`, `ForestChoiceOccurrence.γ`) are against the *split-choice* outer `s.1.1`, not the codomain
target `z.1.1`, and are severed from the region-level abstract field.  So `parent_mem_carrier` is not derivable
from the existing supply; it needs a new well-formedness field.

## The finer field and the leaf (PROVED)

Rather than field `parent_mem_carrier` directly, `ResolvedForestParentCarrierSupply D S` fields the **componentwise**
membership — the natural well-formedness of `componentToForest` (each remnant parent is a component of the target
outer `A`):

```text
forestComponentMem : ∀ z (δ : {x // x ∈ forestDomain z}), componentToForest z δ ∈ z.1.1.elements
```

Then `parent_mem_carrier` is **PROVED**: unfolding `forestRecovered z .elements = (forestDomain z).attach.image
(componentToForest z)` (`rfl`), a member is `componentToForest z δ` for some `δ` (`Finset.mem_image`), and
`forestComponentMem` places it in `z.1.1.elements`.

`.toForestRecoveryDecompositionSupply` grafts this proved `parent_mem_carrier` onto body-183's decomposition,
taking the remaining two leaves (`forestRecovered_eq`, `promoted_eq_forestRecovered`) as arguments — so body-183's
forest box now stands on `forestRecovered_eq` (`rfl`, body-184), this componentwise membership, and the deep
round-trip alone.

Per the HALT: the `componentToForest` inverse / `promoted_eq_forestRecovered` are not entered; only the
componentwise membership is fielded and `parent_mem_carrier` read off it by `Finset.mem_image`.

Landed:

* `ResolvedForestParentCarrierSupply D S` — body-156's construction + the componentwise membership;
* `.parent_mem_carrier` — body-183's leaf (PROVED from the componentwise membership);
* `.toForestRecoveryDecompositionSupply` — body-183's decomposition with `parent_mem_carrier` proved.

Toolkit body (like body-184).  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-185 — the forest parent carrier supply.**  Body-156's sector region construction plus the
componentwise well-formedness: each `componentToForest` parent is a component of the target outer `A`. -/
structure ResolvedForestParentCarrierSupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) where
  /-- Body-156's sector region construction. -/
  Construction : ResolvedRegionConstructionFromSectorSupply D S
  /-- Each `componentToForest` parent is a component of the target outer `A`. -/
  forestComponentMem : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (δ : {x // x ∈ forestDomain z}),
    Construction.componentToForest z δ ∈ z.1.1.elements

namespace ResolvedForestParentCarrierSupply

variable {S : ResolvedConcreteSummandBundleSupply D}

/-- **R-6c-body-185 — body-183's `parent_mem_carrier` from the componentwise membership.** -/
theorem parent_mem_carrier (P : ResolvedForestParentCarrierSupply D S)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) (γ : ResolvedFeynmanSubgraph G)
    (hγ : γ ∈ (P.Construction.forestRecovered z).elements) : γ ∈ z.1.1.elements := by
  obtain ⟨δ, _, rfl⟩ := Finset.mem_image.mp hγ
  exact P.forestComponentMem z δ

/-- **R-6c-body-185 — body-183's decomposition with `parent_mem_carrier` proved.**  The remaining two leaves
(`forestRecovered_eq`, `promoted_eq_forestRecovered`) are taken as arguments. -/
def toForestRecoveryDecompositionSupply (P : ResolvedForestParentCarrierSupply D S)
    (Region : ResolvedRegionChoiceRoundTripSupply D S)
    (forestRecovered_eq : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
      (Region.Union.forestRecovered z).elements = (P.Construction.forestRecovered z).elements)
    (promoted_eq_forestRecovered : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
      ((S.Forward.imageSupply G).promotedOf
          (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).elements
        = (P.Construction.forestRecovered z).elements) :
    ResolvedForestRecoveryDecompositionSupply D S Region where
  Construction := P.Construction
  forestRecovered_eq := fun {G} z => forestRecovered_eq z
  parent_mem_carrier := fun {G} z γ hγ => P.parent_mem_carrier z γ hγ
  promoted_eq_forestRecovered := fun {G} z => promoted_eq_forestRecovered z

end ResolvedForestParentCarrierSupply

end GaugeGeometry.QFT.Combinatorial
