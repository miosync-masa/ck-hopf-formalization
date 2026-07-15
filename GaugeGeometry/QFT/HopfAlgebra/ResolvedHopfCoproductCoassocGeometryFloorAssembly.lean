import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecoveredPreimageValueGeometryAssembly
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSurvivorMemValue
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRemnantMemValue
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestComponentMemValue
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRepresentedCasesValue

/-!
# R-6c-body-299 — coassociativity from eight local model-geometry floor facts (PROVED)

Two-hundred-and-ninety-ninth genuine-body step — the final floor assembly.  It bundles the EIGHT local model-geometry
floor facts (bodies 293-298) over ONE shared `Data`, rebuilds the four reduced supplies (293/294/297/298) which derive
four of body-291's six leaves, keeps the two genuine floor fields (`forestTag_agrees`, body-295; `promote_collapse`,
body-296) directly, and chains through body-291/286 to `coassoc_gen`.  This closes the round-trip geometry residual to
its true floor: **eight local component-level facts ⟹ `Δᵣ`-coassociativity**.

## The eight floor facts (all over the single `Data`)

```text
forestTag_agrees                   floor (295)  occurrence-B agreement at forward images
promote_collapse                   floor (296)  de-contraction whole-component singleton
forest_parent_mem_value            floor (297)  componentToForest z δ ∈ z.1.1.elements (pointwise)
represented_forest_complete_value  floor (298)  represented A-component has a componentToForest preimage
survivor_sound_value               (293)        survivor image ⟹ star-avoiding
survivor_complete_value            (293)        star-avoiding has a survivor preimage
remnant_sound_value                (294)        remnant image ⟹ star-touching
remnant_complete_value             (294)        star-touching has a remnant preimage
```

## The one-way wiring

`.toSurvivorSupply` / `.toRemnantSupply` / `.toForestComponentMemSupply` / `.toRepresentedCasesSupply` rebuild bodies
293/294/297/298 from the shared `Data` + the floor facts; their theorems (`survivor_mem_value`, `remnant_mem_value`,
`forestComponentMem`, `represented_cases`) discharge four of body-291's leaves.  `.toGeometryAssemblySupply` fills body-291
(the two remaining leaves are the direct floor fields).  `coassoc_gen_of_geometry_floor` chains through body-286's S-free
top-level theorem — the old six leaves are gone from its arguments; only the eight floor facts + the base leaves remain.

Per the HALT: `Data` appears once; converters rebuild with `Data := A.Data` (no equality bridge); the final theorem
exposes only the eight floor facts + base leaves; no global-HEq / round-trip leaf is returned; no `Forward` / phantom `S`
/ legacy.  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-299 — the geometry floor supply.**  One `Data` + the eight local model-geometry floor facts
(bodies 293-298). -/
structure ResolvedRecoveredPreimageValueGeometryFloorSupply
    (F : ResolvedSelectedOuterFilteredMemSupply D) (V : ResolvedConcreteSummandValueSupply D) where
  /-- The single membership supply (body-283). -/
  Data : ResolvedRecoveredPreimageValueMemSupply F V
  /-- Floor (295): the opaque `forestTag` agrees with the occurrence-recovered index at forward images. -/
  forestTag_agrees : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ q.1.1.1.elements})
    (hu : γ.1 ∈ (Data.Tags.Closure.unionOuterValue (fwdMapFilteredValue F V q)).1.elements)
    (hmem : γ.1 ∈ (Data.Tags.Closure.Assembly.Region.forestRecovered (fwdMapFilteredValue F V q)).elements),
    Data.Tags.forestTag (fwdMapFilteredValue F V q) ⟨γ.1, hu⟩ hmem = Data.forestTag_fwd_value q γ hmem
  /-- Floor (296): the de-contracted forest of a recovered parent is the parent singleton. -/
  promote_collapse : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ (Data.Tags.Closure.unionOuterValue z).1.elements})
    (h : γ.1 ∈ (Data.Tags.Closure.Assembly.Region.forestRecovered z).elements),
    (ResolvedAdmissibleSubgraph.promote γ.1 (Data.Tags.forestTag z γ h).1).elements = {γ.1}
  /-- Floor (297): each recovered forest parent is a component of the target outer `A`. -/
  forest_parent_mem_value : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) // x ∈ forestDomain z}),
    Data.Tags.Closure.Assembly.Region.componentToForest z δ ∈ z.1.1.elements
  /-- Floor (298): a represented `A`-component has a `componentToForest` preimage (completeness). -/
  represented_forest_complete_value : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (γ : ResolvedFeynmanSubgraph G),
    γ ∈ z.1.1.elements → Data.Tags.Closure.Assembly.Left.representedInQuotient z γ →
    ∃ δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) // x ∈ forestDomain z},
      Data.Tags.Closure.Assembly.Region.componentToForest z δ = γ
  /-- Floor (293): a survivor image (`HEq`-linked) forces `x₂` star-avoiding. -/
  survivor_sound_value : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (γ : {y // y ∈ ResolvedCoassocSplitChoice.rightComponents (Data.Tags.recoveredPreimageValue z)})
    (x₂ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))),
    HEq (V.Survivor.survivor.survivorComponent (Data.Tags.recoveredPreimageValue z) γ) x₂ →
    (x₂ ∈ z.2.1.elements ∧ Disjoint x₂.vertices (starOfZ z))
  /-- Floor (293): every star-avoiding `x₂` has a survivor preimage. -/
  survivor_complete_value : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (x₂ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))),
    (x₂ ∈ z.2.1.elements ∧ Disjoint x₂.vertices (starOfZ z)) →
    ∃ γ : {y // y ∈ ResolvedCoassocSplitChoice.rightComponents (Data.Tags.recoveredPreimageValue z)},
      HEq (V.Survivor.survivor.survivorComponent (Data.Tags.recoveredPreimageValue z) γ) x₂
  /-- Floor (294): a remnant image (`HEq`-linked) forces `x₂` star-touching. -/
  remnant_sound_value : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (γ : {y // y ∈ ResolvedCoassocSplitChoice.forestComponents (Data.Tags.recoveredPreimageValue z)})
    (x₂ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))),
    HEq (V.Remnant.remnant.remnantComponent (Data.Tags.recoveredPreimageValue z)
        (ResolvedCoassocSplitChoice.forestComponentOccurrence
          (Data.Tags.recoveredPreimageValue z) γ)) x₂ →
    (x₂ ∈ z.2.1.elements ∧ ¬ Disjoint x₂.vertices (starOfZ z))
  /-- Floor (294): every star-touching `x₂` has a remnant preimage. -/
  remnant_complete_value : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (x₂ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))),
    (x₂ ∈ z.2.1.elements ∧ ¬ Disjoint x₂.vertices (starOfZ z)) →
    ∃ γ : {y // y ∈ ResolvedCoassocSplitChoice.forestComponents (Data.Tags.recoveredPreimageValue z)},
      HEq (V.Remnant.remnant.remnantComponent (Data.Tags.recoveredPreimageValue z)
        (ResolvedCoassocSplitChoice.forestComponentOccurrence
          (Data.Tags.recoveredPreimageValue z) γ)) x₂

namespace ResolvedRecoveredPreimageValueGeometryFloorSupply

variable {F : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}

/-- **R-6c-body-299 — body-293's survivor supply.** -/
def toSurvivorSupply (A : ResolvedRecoveredPreimageValueGeometryFloorSupply F V) :
    ResolvedSurvivorImageCorrespondenceValueSupply F V where
  Data := A.Data
  survivor_sound_value := A.survivor_sound_value
  survivor_complete_value := A.survivor_complete_value

/-- **R-6c-body-299 — body-294's remnant supply.** -/
def toRemnantSupply (A : ResolvedRecoveredPreimageValueGeometryFloorSupply F V) :
    ResolvedRemnantImageCorrespondenceValueSupply F V where
  Data := A.Data
  remnant_sound_value := A.remnant_sound_value
  remnant_complete_value := A.remnant_complete_value

/-- **R-6c-body-299 — body-297's forest-component membership supply.** -/
def toForestComponentMemSupply (A : ResolvedRecoveredPreimageValueGeometryFloorSupply F V) :
    ResolvedForestComponentMemValueSupply F V where
  Data := A.Data
  forest_parent_mem_value := A.forest_parent_mem_value

/-- **R-6c-body-299 — body-298's represented-cases supply.** -/
def toRepresentedCasesSupply (A : ResolvedRecoveredPreimageValueGeometryFloorSupply F V) :
    ResolvedRepresentedCasesValueSupply F V where
  Data := A.Data
  represented_forest_complete_value := A.represented_forest_complete_value

/-- **R-6c-body-299 — body-291's geometry assembly** (the four reduced leaves discharged, two floor leaves direct). -/
def toGeometryAssemblySupply (A : ResolvedRecoveredPreimageValueGeometryFloorSupply F V) :
    ResolvedRecoveredPreimageValueGeometryAssemblySupply F V where
  Data := A.Data
  forestTag_agrees := A.forestTag_agrees
  promote_collapse := A.promote_collapse
  forestComponentMem := A.toForestComponentMemSupply.forestComponentMem
  represented_cases := A.toRepresentedCasesSupply.represented_cases
  survivor_mem_value := A.toSurvivorSupply.survivor_mem_value
  remnant_mem_value := A.toRemnantSupply.remnant_mem_value

/-- **R-6c-body-299 — native `Δᵣ`-coassociativity from the eight local model-geometry floor facts** (S-free top-level).
The eight floor facts (bodies 293-298) + the base leaves feed body-291/286's chain; no global-HEq / round-trip leaf, no
`.ofLegacy`, no phantom `S`. -/
theorem coassoc_gen_of_geometry_floor
    (A : ResolvedRecoveredPreimageValueGeometryFloorSupply F V)
    (carrier_isProperForest : ∀ (G : ResolvedFeynmanGraph) (B : ResolvedAdmissibleSubgraph G),
      B ∈ D.carrier G → B.IsProperForest)
    (rep : ResolvedHopfGen → ResolvedFeynmanGraph)
    (repCD : ∀ x : ResolvedHopfGen, (rep x).forget.toClass.IsConnectedDivergent)
    (rep_gen : ∀ x : ResolvedHopfGen, x = (rep x).toResolvedHopfGen (repCD x))
    (x : ResolvedHopfGen) :
    D.coassocLeft (MvPolynomial.X x) = D.coassocRight (MvPolynomial.X x) :=
  A.toGeometryAssemblySupply.coassoc_gen_of_local_value_geometry carrier_isProperForest rep repCD rep_gen x

end ResolvedRecoveredPreimageValueGeometryFloorSupply

end GaugeGeometry.QFT.Combinatorial
