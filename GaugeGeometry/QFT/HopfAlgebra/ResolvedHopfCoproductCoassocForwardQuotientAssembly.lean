import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSurvivorElementsRecovery
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRemnantElementsRecovery
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocQuotientElementsRecovery

/-!
# R-6c-body-208 — forward quotient assembly: the whole `forward_quotient_heq` from the two membership bridges

Two-hundred-and-eighth genuine-body step, the forward-quotient assembly.  After bodies 205–207 reduced each half
of the quotient `HEq` to a membership bridge, this body wires the survivor bridge (body-206), the remnant bridge
(body-207), and the reused ambient transport into body-204's quotient-elements supply, and runs the whole
forward-quotient `HEq` out to body-165's `ResolvedRecoveredQuotientRoundTripSupply` in one line.

## The pieces (the two fresh bridges + the reused transport)

`ResolvedForwardQuotientAssemblySupply D S Region` fields:

* `selectedOuter_partition` — the reused ambient transport (body-162/190);
* `survivor_mem` — body-206's survivor membership bridge (recovered survivors ↔ `B`'s star-avoiding components);
* `remnant_mem` — body-207's remnant membership bridge (recovered remnants ↔ `B`'s star-touching components).

## The wiring (all downstream PROVED)

* body-206's `ResolvedSurvivorElementsRecoverySupply` → `survivor_elements_heq`;
* body-207's `ResolvedRemnantElementsRecoverySupply` → `remnant_elements_heq`;
* body-204's `ResolvedQuotientElementsRecoverySupply` — the two above + the transport → `quotient_elements_heq`;
* body-203's `ResolvedForwardQuotientHEqDecompositionSupply` → `forward_quotient_heq`;
* body-165's `ResolvedRecoveredQuotientRoundTripSupply` — `.toRecoveredQuotientRoundTripSupply`.

So the forward-quotient `HEq` (body-165) is now supplied entirely by the two fresh membership bridges plus the
reused ambient transport: the survivor/remnant recovered-side sector bridges, the duals of the backward sector
bridges (bodies 170/171).

## Consequence — all four round-trips at their floor

With this, every round-trip obligation of the resolved coassociativity backward map is reduced to local sector
bridges:

```text
backward outer   → the three sector bridges (170/171/172) + choice_tag_trichotomy (173, proved)
forward outer    → the compatibility leaves (188/185/180) + region constructions
backward choice  → parent_recovered = rfl via the forest bridge (171/202) — the three bridges
forward quotient → the survivor / remnant membership bridges (206/207) — the duals
```

Per the HALT: the survivor/remnant bridge bodies are not entered; this body is the 203/204/206/207 wiring only.

Landed:

* `ResolvedForwardQuotientAssemblySupply D S Region` — the two membership bridges + the ambient transport;
* `.toSurvivorElementsRecoverySupply` / `.toRemnantElementsRecoverySupply` — bodies 206 / 207;
* `.toQuotientElementsRecoverySupply` — body-204;
* `.toForwardQuotientHEqDecompositionSupply` — body-203;
* `.toRecoveredQuotientRoundTripSupply` — body-165 (the forward-quotient round-trip closed on the bridges).

Toolkit body (like body-190).  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-208 — the forward quotient assembly supply.**  The reused ambient transport and the two fresh
survivor / remnant membership bridges (bodies 206/207), from which the whole forward-quotient `HEq` follows. -/
structure ResolvedForwardQuotientAssemblySupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) (Region : ResolvedRegionChoiceRoundTripSupply D S) where
  /-- Body-162/190: the recovered selected outer has exactly `A`'s components (the ambient transport). -/
  selectedOuter_partition : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    ((S.Forward.imageSupply G).selectedOuterOf
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).1.elements
      = z.1.1.elements
  /-- Body-206's survivor membership bridge. -/
  survivor_mem : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (x₁ : ResolvedFeynmanSubgraph (((S.Forward.imageSupply G).selectedOuterOf
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).1.contractWithStars
        (D.starOf G ((S.Forward.imageSupply G).selectedOuterOf
          (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).1)))
    (x₂ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))),
    HEq x₁ x₂ →
    (x₁ ∈ (S.Survivor.survivor.rightSurvivorForest
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).elements
      ↔ x₂ ∈ rightDomain z)
  /-- Body-207's remnant membership bridge. -/
  remnant_mem : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (x₁ : ResolvedFeynmanSubgraph (((S.Forward.imageSupply G).selectedOuterOf
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).1.contractWithStars
        (D.starOf G ((S.Forward.imageSupply G).selectedOuterOf
          (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).1)))
    (x₂ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))),
    HEq x₁ x₂ →
    (x₁ ∈ (S.Remnant.remnant.remnantForest
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).elements
      ↔ x₂ ∈ forestDomain z)

namespace ResolvedForwardQuotientAssemblySupply

variable {S : ResolvedConcreteSummandBundleSupply D} {Region : ResolvedRegionChoiceRoundTripSupply D S}

/-- **R-6c-body-208 — body-206's survivor elements recovery supply.** -/
def toSurvivorElementsRecoverySupply (F : ResolvedForwardQuotientAssemblySupply D S Region) :
    ResolvedSurvivorElementsRecoverySupply D S Region where
  selectedOuter_partition := fun {G} z => F.selectedOuter_partition z
  survivor_mem := fun {G} z x₁ x₂ h => F.survivor_mem z x₁ x₂ h

/-- **R-6c-body-208 — body-207's remnant elements recovery supply.** -/
def toRemnantElementsRecoverySupply (F : ResolvedForwardQuotientAssemblySupply D S Region) :
    ResolvedRemnantElementsRecoverySupply D S Region where
  selectedOuter_partition := fun {G} z => F.selectedOuter_partition z
  remnant_mem := fun {G} z x₁ x₂ h => F.remnant_mem z x₁ x₂ h

/-- **R-6c-body-208 — body-204's quotient elements recovery supply.** -/
def toQuotientElementsRecoverySupply (F : ResolvedForwardQuotientAssemblySupply D S Region) :
    ResolvedQuotientElementsRecoverySupply D S Region where
  selectedOuter_partition := fun {G} z => F.selectedOuter_partition z
  survivor_elements_heq := fun {G} z => F.toSurvivorElementsRecoverySupply.survivor_elements_heq z
  remnant_elements_heq := fun {G} z => F.toRemnantElementsRecoverySupply.remnant_elements_heq z

/-- **R-6c-body-208 — body-203's forward-quotient HEq decomposition supply.** -/
def toForwardQuotientHEqDecompositionSupply (F : ResolvedForwardQuotientAssemblySupply D S Region) :
    ResolvedForwardQuotientHEqDecompositionSupply D S Region :=
  F.toQuotientElementsRecoverySupply.toForwardQuotientHEqDecompositionSupply

/-- **R-6c-body-208 — body-165's recovered-quotient round-trip supply (the forward-quotient chain closed on the
bridges).** -/
def toRecoveredQuotientRoundTripSupply (F : ResolvedForwardQuotientAssemblySupply D S Region) :
    ResolvedRecoveredQuotientRoundTripSupply D S Region :=
  F.toForwardQuotientHEqDecompositionSupply.toRecoveredQuotientRoundTripSupply

end ResolvedForwardQuotientAssemblySupply

end GaugeGeometry.QFT.Combinatorial
