import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestValueEqValue
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForwardQuotientValue
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecoveredPreimageValueCover

/-!
# R-6c-body-291 — the local-geometry assembly: coassociativity from six component-level leaves (PROVED)

Two-hundred-and-ninety-first genuine-body step — the flat assembly of the three reduced leaves (bodies 288/289/290)
into the top-level coassociativity theorem.  All three geometry supplies share ONE `Data`
(`ResolvedRecoveredPreimageValueMemSupply`), so no equality bridge / transport between records is needed.  After this,
the top-level theorem's residual is exactly the region / model / base assumptions + **six component-level geometry
leaves** — every abstract round-trip / global-HEq leaf is gone.

## The six leaves (all over the single `Data`)

```text
forestTag_agrees     (288)  forestTag = the occurrence-recovered index
promote_collapse     (289)  (promote γ (forestTag …)).elements = {γ}
forestComponentMem   (289)  forest parent ∈ target outer A
represented_cases    (289)  represented A-component ∈ forestRecovered
survivor_mem_value   (290)  survivor ⟷ rightDomain (tag-reducible)
remnant_mem_value    (290)  remnant ⟷ forestDomain (de-contraction)
```

## The wiring

`.toForestValueEqSupply` / `.toForwardOuterGeometrySupply` / `.toForwardQuotientGeometrySupply` rebuild bodies
288/289/290's supplies from the shared `Data` + the six leaves (the quotient supply's `Geom` IS the forward-outer
supply, by construction).  `.toRoundTripLeafSupply` fills body-285's three leaves; `coassoc_gen_of_local_value_geometry`
chains it through body-286's S-free top-level theorem.

Per the HALT: `Data` appears once; no inter-record equality/transport; the six leaves are not duplicated; no global-HEq /
round-trip leaf is returned to the final theorem's arguments.  No `S` / `Forward` / legacy in any declaration type.  No
facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-291 — the local-geometry assembly supply.**  One `Data` + the six component-level geometry leaves
(bodies 288/289/290). -/
structure ResolvedRecoveredPreimageValueGeometryAssemblySupply
    (F : ResolvedSelectedOuterFilteredMemSupply D) (V : ResolvedConcreteSummandValueSupply D) where
  /-- The single membership supply (body-283). -/
  Data : ResolvedRecoveredPreimageValueMemSupply F V
  /-- Body-288 leaf: the opaque `forestTag` agrees with the occurrence-recovered index. -/
  forestTag_agrees : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ q.1.1.1.elements})
    (hu : γ.1 ∈ (Data.Tags.Closure.unionOuterValue (fwdMapFilteredValue F V q)).1.elements)
    (hmem : γ.1 ∈ (Data.Tags.Closure.Assembly.Region.forestRecovered (fwdMapFilteredValue F V q)).elements),
    Data.Tags.forestTag (fwdMapFilteredValue F V q) ⟨γ.1, hu⟩ hmem = Data.forestTag_fwd_value q γ hmem
  /-- Body-289 leaf 1: the de-contracted forest of a recovered parent is the parent singleton. -/
  promote_collapse : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ (Data.Tags.Closure.unionOuterValue z).1.elements})
    (h : γ.1 ∈ (Data.Tags.Closure.Assembly.Region.forestRecovered z).elements),
    (ResolvedAdmissibleSubgraph.promote γ.1 (Data.Tags.forestTag z γ h).1).elements = {γ.1}
  /-- Body-289 leaf 2: a forest-recovered parent is a component of the target outer `A`. -/
  forestComponentMem : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (γ : ResolvedFeynmanSubgraph G),
    γ ∈ (Data.Tags.Closure.Assembly.Region.forestRecovered z).elements → γ ∈ z.1.1.elements
  /-- Body-289 leaf 3: a represented `A`-component is a forest-recovered parent. -/
  represented_cases : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (γ : ResolvedFeynmanSubgraph G),
    γ ∈ z.1.1.elements → Data.Tags.Closure.Assembly.Left.representedInQuotient z γ →
      γ ∈ (Data.Tags.Closure.Assembly.Region.forestRecovered z).elements
  /-- Body-290 leaf: the survivor membership bridge (tag-reducible). -/
  survivor_mem_value : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (x₁ : ResolvedFeynmanSubgraph (ResolvedCoassocSplitChoice.selectedOuterContractGraph
        (Data.Tags.recoveredPreimageValue z)))
    (x₂ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))),
    HEq x₁ x₂ →
    (x₁ ∈ (V.Survivor.survivor.rightSurvivorForest (Data.Tags.recoveredPreimageValue z)).elements
      ↔ x₂ ∈ rightDomain z)
  /-- Body-290 leaf: the remnant membership bridge (de-contraction). -/
  remnant_mem_value : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (x₁ : ResolvedFeynmanSubgraph (ResolvedCoassocSplitChoice.selectedOuterContractGraph
        (Data.Tags.recoveredPreimageValue z)))
    (x₂ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))),
    HEq x₁ x₂ →
    (x₁ ∈ (V.Remnant.remnant.remnantForest (Data.Tags.recoveredPreimageValue z)).elements
      ↔ x₂ ∈ forestDomain z)

namespace ResolvedRecoveredPreimageValueGeometryAssemblySupply

variable {F : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}

/-- **R-6c-body-291 — body-288's forest exact-B supply.** -/
def toForestValueEqSupply (A : ResolvedRecoveredPreimageValueGeometryAssemblySupply F V) :
    ResolvedForestValueEqValueSupply F V where
  Data := A.Data
  forestTag_agrees := A.forestTag_agrees

/-- **R-6c-body-291 — body-289's forward-outer geometry supply.** -/
def toForwardOuterGeometrySupply (A : ResolvedRecoveredPreimageValueGeometryAssemblySupply F V) :
    ResolvedForwardOuterValueGeometrySupply F V where
  Data := A.Data
  promote_collapse := A.promote_collapse
  forestComponentMem := A.forestComponentMem
  represented_cases := A.represented_cases

/-- **R-6c-body-291 — body-290's forward-quotient geometry supply** (its `Geom` IS the forward-outer supply). -/
def toForwardQuotientGeometrySupply (A : ResolvedRecoveredPreimageValueGeometryAssemblySupply F V) :
    ResolvedForwardQuotientValueGeometrySupply F V where
  Geom := A.toForwardOuterGeometrySupply
  survivor_mem_value := A.survivor_mem_value
  remnant_mem_value := A.remnant_mem_value

/-- **R-6c-body-291 — body-285's round-trip leaf supply** from the three geometry supplies (shared `Data`). -/
def toRoundTripLeafSupply (A : ResolvedRecoveredPreimageValueGeometryAssemblySupply F V) :
    ResolvedRecoveredPreimageValueRoundTripLeafSupply F V where
  Data := A.Data
  forward_outer_value := A.toForwardOuterGeometrySupply.forward_outer_value
  forward_quotient_value := A.toForwardQuotientGeometrySupply.forward_quotient_value
  forest_value_eq := A.toForestValueEqSupply.forest_value_eq

/-- **R-6c-body-291 — native `Δᵣ`-coassociativity from the local component-level geometry** (S-free top-level).  The six
component-level leaves (bodies 288/289/290) + the base leaves feed body-286's raid-boss chain; no global-HEq / round-trip
leaf, no `.ofLegacy`, no phantom `S`. -/
theorem coassoc_gen_of_local_value_geometry
    (A : ResolvedRecoveredPreimageValueGeometryAssemblySupply F V)
    (carrier_isProperForest : ∀ (G : ResolvedFeynmanGraph) (B : ResolvedAdmissibleSubgraph G),
      B ∈ D.carrier G → B.IsProperForest)
    (rep : ResolvedHopfGen → ResolvedFeynmanGraph)
    (repCD : ∀ x : ResolvedHopfGen, (rep x).forget.toClass.IsConnectedDivergent)
    (rep_gen : ∀ x : ResolvedHopfGen, x = (rep x).toResolvedHopfGen (repCD x))
    (x : ResolvedHopfGen) :
    D.coassocLeft (MvPolynomial.X x) = D.coassocRight (MvPolynomial.X x) :=
  coassoc_gen_of_recovered_preimage_value A.toRoundTripLeafSupply carrier_isProperForest rep repCD rep_gen x

end ResolvedRecoveredPreimageValueGeometryAssemblySupply

end GaugeGeometry.QFT.Combinatorial
