import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocConcreteSummandBundle
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocOuterMixingAssembly

/-!
# R-6c-body-130 — bijection-side assembly: the summand bundle + the index/cover bijection → `coassoc_gen`

Hundred-and-thirtieth genuine-body step, the other half of the fold.  Body-129 collapsed the summand-agreement
PRODUCT side into one base-supply bundle; this body collects the remaining half — the index/cover BIJECTION
(`invConstruct` + the eight membership / inverse laws), the quotient providers (`quotientForest` is already in the
summand bundle; `quot_eq`'s underlying contract-twice geometry `contract`), and the base data — into one supply,
and streams BOTH into body-113's `ResolvedOuterMixingAssemblySupply` → `coassoc_gen`.

So after this body, `coassoc_gen` on every generator flows from exactly two bundles plus the base/provider leaves:

```text
coassoc_gen  ⟸  ResolvedForestBlockBijectionSideSupply
             =  ResolvedConcreteSummandBundleSupply (body-129, the whole PRODUCT side)
              + [ invConstruct + 8 membership/inverse laws ]     -- the index/cover bijection (sector backward)
              + [ contract ]                                     -- the contract-twice geometry (bodies 27–49)
              + [ carrier_isProperForest + rep/repCD/rep_gen ]   -- the base
```

## What is streamed (PROVED)

`.toOuterMixingAssemblySupply` fills body-113's `ResolvedOuterMixingAssemblySupply` field-by-field:

* `imageSupply` ← `Summand.Forward.imageSupply` (the concrete image supply, body-128);
* `quotientRaw` / `quotient_mem` ← the two projections of `Summand.quotientForest`;
* the LEFT / RIGHT factor products, disjointnesses and survivor/remnant forests ← the summand bundle exactly as in
  body-129 (`left_primitive_factor_concrete`, `promoted_factor_of_hPD` + `Measure.promotedHPD`, `Measure.leftHDisj`,
  `Survivor` / `Remnant`);
* `invConstruct`, the eight membership / inverse laws, `contract`, and the base ← this supply's own fields.

Because body-128 makes the ambient contract graph `rfl`-equal to `q.selectedOuterContractGraph`, the survivor /
remnant forests and factor products slot into body-113's slots with no cast, exactly as in body-129.

## What is still fielded (the genuine bijection / geometry / base leaves)

The eight membership / inverse laws (the sector backward map's `maps_to` + `left_inv` / `right_inv`, body-112),
`invConstruct` itself, the contract-twice geometry `contract` (bodies 27–49, feeds `quot_eq` inside body-113), and
the base (`carrier_isProperForest`, `rep` / `repCD` / `rep_gen`) are exposed as supply fields — these are the
residual bijection / geometry / base obligations, to be discharged by the sector backward machinery and the
proper-forest / representative providers.

Per the HALT: only wiring / inventory; the summand side is streamed from body-129, the bijection / geometry / base
leaves are exposed as fields, and no inverse law is proved here.

Landed:

* `ResolvedForestBlockBijectionSideSupply D` — the summand bundle + the index/cover bijection + contract + base;
* `.toOuterMixingAssemblySupply` — body-113's assembly supply, fed from the two halves;
* `.coassoc_gen` — `Δᵣ`-coassociativity on every generator, from the two bundles + the fielded leaves.

Toolkit body (like body-129), one bundling supply.  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-130 — the bijection-side assembly supply.**  The summand bundle (body-129, the whole PRODUCT side)
together with the index/cover bijection (`invConstruct` + eight membership / inverse laws, sector backward), the
contract-twice geometry `contract` (bodies 27–49) and the base data. -/
structure ResolvedForestBlockBijectionSideSupply (D : ResolvedCoproductProperForestData) where
  /-- The summand-agreement PRODUCT side (body-129). -/
  Summand : ResolvedConcreteSummandBundleSupply D
  /-- The backward map `(A_target, B) ↦ (A', p)` (body-112). -/
  invConstruct : ∀ (G : ResolvedFeynmanGraph), ForestBlockCodType D G → ForestBlockDomType D G
  /-- Mixed forward lands in the mixed codomain. -/
  mixed_toFun_mem : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G) (hq : q ∈ mixedDomFinset G),
    (⟨(Summand.Forward.imageSupply G).selectedOuterOf q, Summand.quotientForest q⟩ : ForestBlockCodType D G)
      ∈ mixedCodFinset (D := D) (fun {G} A B => resolvedIsForestImage A B) G
  /-- Mixed inverse lands in the mixed domain. -/
  mixed_invFun_mem : ∀ (G : ResolvedFeynmanGraph) (r : ForestBlockCodType D G)
    (hr : r ∈ mixedCodFinset (D := D) (fun {G} A B => resolvedIsForestImage A B) G),
    invConstruct G r ∈ mixedDomFinset G
  /-- Mixed `invConstruct ∘ toFun = id`. -/
  mixed_left_inv : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G) (hq : q ∈ mixedDomFinset G),
    invConstruct G
        (⟨(Summand.Forward.imageSupply G).selectedOuterOf q, Summand.quotientForest q⟩ : ForestBlockCodType D G)
      = q
  /-- Mixed `toFun ∘ invConstruct = id`. -/
  mixed_right_inv : ∀ (G : ResolvedFeynmanGraph) (r : ForestBlockCodType D G)
    (hr : r ∈ mixedCodFinset (D := D) (fun {G} A B => resolvedIsForestImage A B) G),
    (⟨(Summand.Forward.imageSupply G).selectedOuterOf (invConstruct G r),
        Summand.quotientForest (invConstruct G r)⟩ : ForestBlockCodType D G) = r
  /-- Forest forward lands in the forest-image codomain. -/
  forest_toFun_mem : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G)
    (hq : q ∈ forestCarryingDomFinset G),
    (⟨(Summand.Forward.imageSupply G).selectedOuterOf q, Summand.quotientForest q⟩ : ForestBlockCodType D G)
      ∈ forestCarryingCodFinset (D := D) (fun {G} A B => resolvedIsForestImage A B) G
  /-- Forest inverse lands in the forest-carrying domain. -/
  forest_invFun_mem : ∀ (G : ResolvedFeynmanGraph) (r : ForestBlockCodType D G)
    (hr : r ∈ forestCarryingCodFinset (D := D) (fun {G} A B => resolvedIsForestImage A B) G),
    invConstruct G r ∈ forestCarryingDomFinset G
  /-- Forest `invConstruct ∘ toFun = id`. -/
  forest_left_inv : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G)
    (hq : q ∈ forestCarryingDomFinset G),
    invConstruct G
        (⟨(Summand.Forward.imageSupply G).selectedOuterOf q, Summand.quotientForest q⟩ : ForestBlockCodType D G)
      = q
  /-- Forest `toFun ∘ invConstruct = id`. -/
  forest_right_inv : ∀ (G : ResolvedFeynmanGraph) (r : ForestBlockCodType D G)
    (hr : r ∈ forestCarryingCodFinset (D := D) (fun {G} A B => resolvedIsForestImage A B) G),
    (⟨(Summand.Forward.imageSupply G).selectedOuterOf (invConstruct G r),
        Summand.quotientForest (invConstruct G r)⟩ : ForestBlockCodType D G) = r
  /-- The contract-twice geometry (bodies 27–49; feeds `quot_eq` inside body-113). -/
  contract : ∀ (G : ResolvedFeynmanGraph),
    ResolvedContractTwiceOnceGeometrySupply D G
      (fun q => ⟨(Summand.Forward.imageSupply G).selectedOuterOf q, (Summand.quotientForest q).1⟩)
  /-- Every carrier forest is a proper forest (body-96). -/
  carrier_isProperForest : ∀ (G : ResolvedFeynmanGraph) (A : ResolvedAdmissibleSubgraph G),
    A ∈ D.carrier G → A.IsProperForest
  /-- A representative graph for each generator. -/
  rep : ResolvedHopfGen → ResolvedFeynmanGraph
  /-- The representative is connected-divergent. -/
  repCD : ∀ x : ResolvedHopfGen, (rep x).forget.toClass.IsConnectedDivergent
  /-- The representative's generator IS `x`. -/
  rep_gen : ∀ x : ResolvedHopfGen, x = (rep x).toResolvedHopfGen (repCD x)

/-- **R-6c-body-130 — body-113's assembly supply from the two halves.**  The summand bundle streams the PRODUCT
side; this supply's fields provide the bijection / contract / base. -/
noncomputable def ResolvedForestBlockBijectionSideSupply.toOuterMixingAssemblySupply
    (S : ResolvedForestBlockBijectionSideSupply D) : ResolvedOuterMixingAssemblySupply D where
  imageSupply G := S.Summand.Forward.imageSupply G
  quotientRaw G q := (S.Summand.quotientForest q).1
  quotient_mem G q := (S.Summand.quotientForest q).2
  invConstruct := S.invConstruct
  mixed_toFun_mem := S.mixed_toFun_mem
  mixed_invFun_mem := S.mixed_invFun_mem
  mixed_left_inv := S.mixed_left_inv
  mixed_right_inv := S.mixed_right_inv
  forest_toFun_mem := S.forest_toFun_mem
  forest_invFun_mem := S.forest_invFun_mem
  forest_left_inv := S.forest_left_inv
  forest_right_inv := S.forest_right_inv
  left_primitive_factor G q := left_primitive_factor_concrete q
  promoted_factor G q := promoted_factor_of_hPD q (S.Summand.Measure.promotedHPD q)
  left_hdisj G q := S.Summand.Measure.leftHDisj q
  rightSurvivor G q := S.Summand.Survivor.survivor.rightSurvivorForest q
  remnant G q := S.Summand.Remnant.remnant.remnantForest q
  right_hcross G q := S.Summand.hcross q
  right_union_eq G q := S.Summand.union_eq q
  right_hdisj G q := S.Summand.hRdisj q
  right_primitive_factor G q :=
    S.Summand.Survivor.toRightPrimitiveSurvivalTransportSupply.right_primitive_factor q
  remnant_factor G q := S.Summand.Remnant.remnant_factor q
  contract := S.contract
  carrier_isProperForest := S.carrier_isProperForest
  rep := S.rep
  repCD := S.repCD
  rep_gen := S.rep_gen

/-- **R-6c-body-130 — `Δᵣ`-coassociativity on every generator, from the two bundles + the fielded leaves.** -/
theorem ResolvedForestBlockBijectionSideSupply.coassoc_gen
    (S : ResolvedForestBlockBijectionSideSupply D) (x : ResolvedHopfGen) :
    D.coassocLeft (MvPolynomial.X x) = D.coassocRight (MvPolynomial.X x) :=
  S.toOuterMixingAssemblySupply.coassoc_gen x

end GaugeGeometry.QFT.Combinatorial
