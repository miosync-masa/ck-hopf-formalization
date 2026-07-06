import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocPromotedForestRecoveryCollapse
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestParentCarrier
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocTargetOuterCoverageAssembly

/-!
# R-6c-body-190 — forward outer geometry assembly: the whole forward outer from the compatibility leaves

Hundred-and-ninetieth genuine-body step, the forward-outer geometry assembly.  After body-189 proved the
de-contraction round-trip, this body wires the concrete geometry — the region constructions, the two wiring
bridges, the componentwise membership, the body-188 compatibility, and the star/remnant classifier — into body-181's
coverage assembly, and runs the whole forward-outer partition out to body-162's
`ResolvedSelectedOuterPartitionSupply` in one line.

## The pieces (the irreducible geometric leaves)

`ResolvedForwardOuterGeometryAssemblySupply D S Region` fields:

* `L` — body-157's left-residual construction (`representedInQuotient`);
* `Construction` — body-156's sector region construction (`componentToForest`);
* `leftResidual_eq` — the body-178 wiring bridge `Region.Union.leftResidual = L.leftResidual`;
* `forestRecovered_eq` — the body-183 wiring bridge `Region.Union.forestRecovered = Construction.forestRecovered`;
* `forestComponentMem` — body-185's componentwise membership (each forest parent ∈ `A`);
* `Compat` — body-188's `componentToForest` / `promote` compatibility (`forestTag`, `recoverChoice_forest_eq`,
  `promote_collapse`);
* `represented_cases` — body-180's star/remnant classifier (a quotient-represented `A`-component is a forest parent).

## The wiring (all downstream facts PROVED)

* body-179's `ResolvedForestRecoveryGeometrySupply` — `representedByForest := γ ∈ Region.Union.forestRecovered`;
  `forestRecovered_mem` from body-185's `parent_mem_carrier` (via `forestRecovered_eq`); `promoted_region_eq` from
  body-189's collapse (`⟨Compat⟩.promoted_region_eq`);
* body-178's `ResolvedLeftResidualMembershipSupply` — `L` + `leftResidual_eq`;
* body-181's `ResolvedTargetOuterCoverageAssemblySupply` — the two above + `represented_cases`;
* body-162's `ResolvedSelectedOuterPartitionSupply` — `.toSelectedOuterPartitionSupply`.

So the forward-outer partition (`leftOf ⊔ promotedOf = A`, body-162) is now supplied entirely by the irreducible
geometric leaves: `forestTag` / `recoverChoice_forest_eq` / `promote_collapse` (body-188), `forestComponentMem`
(body-185), `represented_cases` (body-180), the two region constructions, and the two wiring bridges.  Everything
structural above is proved.

Per the HALT: the compatibility / classifier bodies are not entered; this body is the 178/179/180/181/185/188/189
wiring only.

Landed:

* `ResolvedForwardOuterGeometryAssemblySupply D S Region` — the irreducible geometric leaves;
* `.toForestRecoveryGeometrySupply` / `.toLeftResidualMembershipSupply` — bodies 179 / 178;
* `.toTargetOuterCoverageAssemblySupply` — body-181;
* `.toSelectedOuterPartitionSupply` — body-162 (the forward-outer chain closed on the geometry).

Toolkit body (like body-181).  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-190 — the forward outer geometry assembly supply.**  The irreducible geometric leaves of the
forward-outer partition: the two region constructions, the two wiring bridges, the componentwise membership, the
body-188 compatibility, and the star/remnant classifier. -/
structure ResolvedForwardOuterGeometryAssemblySupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) (Region : ResolvedRegionChoiceRoundTripSupply D S) where
  /-- Body-157's left-residual construction. -/
  L : ResolvedLeftResidualConstructionSupply D S
  /-- Body-156's sector region construction. -/
  Construction : ResolvedRegionConstructionFromSectorSupply D S
  /-- Body-178's wiring bridge: the abstract union left region agrees with body-157's construction. -/
  leftResidual_eq : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    (Region.Union.leftResidual z).elements = (L.leftResidual z).elements
  /-- Body-183's wiring bridge: the abstract union forest region agrees with body-156's construction. -/
  forestRecovered_eq : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    (Region.Union.forestRecovered z).elements = (Construction.forestRecovered z).elements
  /-- Body-185's componentwise membership: each `componentToForest` parent is a component of `A`. -/
  forestComponentMem : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (δ : {x // x ∈ forestDomain z}),
    Construction.componentToForest z δ ∈ z.1.1.elements
  /-- Body-188's `componentToForest` / `promote` compatibility. -/
  Compat : ResolvedComponentToForestPromoteCompatibility D S Region
  /-- Body-180's star/remnant classifier: a quotient-represented `A`-component is a forest parent. -/
  represented_cases : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (γ : ResolvedFeynmanSubgraph G),
    γ ∈ z.1.1.elements → L.representedInQuotient z γ → γ ∈ (Region.Union.forestRecovered z).elements

namespace ResolvedForwardOuterGeometryAssemblySupply

variable {S : ResolvedConcreteSummandBundleSupply D} {Region : ResolvedRegionChoiceRoundTripSupply D S}

/-- **R-6c-body-190 — body-179's forest-recovery geometry supply.** -/
def toForestRecoveryGeometrySupply (A : ResolvedForwardOuterGeometryAssemblySupply D S Region) :
    ResolvedForestRecoveryGeometrySupply D S Region where
  representedByForest := fun {G} z γ => γ ∈ (Region.Union.forestRecovered z).elements
  forestRecovered_mem := fun {G} z γ => by
    constructor
    · intro h
      have hA : γ ∈ z.1.1.elements :=
        (⟨A.Construction, A.forestComponentMem⟩ : ResolvedForestParentCarrierSupply D S).parent_mem_carrier
          z γ ((A.forestRecovered_eq z) ▸ h)
      exact ⟨hA, h⟩
    · intro h; exact h.2
  promoted_region_eq := fun {G} z =>
    (⟨A.Compat⟩ : ResolvedPromotedForestRecoveryCollapseSupply D S Region).promoted_region_eq z

/-- **R-6c-body-190 — body-178's left-residual membership supply.** -/
def toLeftResidualMembershipSupply (A : ResolvedForwardOuterGeometryAssemblySupply D S Region) :
    ResolvedLeftResidualMembershipSupply D S Region where
  L := A.L
  leftResidual_eq := fun {G} z => A.leftResidual_eq z

/-- **R-6c-body-190 — body-181's target outer coverage assembly supply.** -/
def toTargetOuterCoverageAssemblySupply (A : ResolvedForwardOuterGeometryAssemblySupply D S Region) :
    ResolvedTargetOuterCoverageAssemblySupply D S Region where
  Left := A.toLeftResidualMembershipSupply
  Forest := A.toForestRecoveryGeometrySupply
  represented_cases := fun {G} z γ hγ hrep => A.represented_cases z γ hγ hrep

/-- **R-6c-body-190 — body-162's selected-outer partition supply (the forward-outer chain closed on the
geometry).** -/
def toSelectedOuterPartitionSupply (A : ResolvedForwardOuterGeometryAssemblySupply D S Region) :
    ResolvedSelectedOuterPartitionSupply D S Region :=
  A.toTargetOuterCoverageAssemblySupply.toSelectedOuterPartitionSupply

end ResolvedForwardOuterGeometryAssemblySupply

end GaugeGeometry.QFT.Combinatorial
