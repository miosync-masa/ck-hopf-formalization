import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocBijectionSideAssembly

/-!
# R-6c-body-131 — bijection provider decomposition: the nine outer-mixing bijection fields, classified

Hundred-and-thirty-first genuine-body step, decomposing body-130's index/cover bijection.  The nine outer-mixing
bijection fields (`invConstruct` + the eight membership / inverse laws) are pulled out of
`ResolvedForestBlockBijectionSideSupply` into their own record `ResolvedOuterMixingBijectionProvider`, parameterized
by the summand bundle (so the field types line up), and mapped onto the EXISTING sector backward machinery.  This
isolates precisely which fields are already provided by the sector equivalence and which are the genuinely-new
outer-level reconstruction.

## The classification (per body-112's inverse scout)

The outer-mixing map is `(A', p) ↦ (A, B)` with `A = leftOf ∪ promotedOf`, `B = rightSurvivor ∪ remnant`.  Its
inverse and round-trips decompose by the `star`-classification of `B`'s components:

| field | provided by | status |
|---|---|---|
| `invConstruct` | sector backward maps (`componentToRight` / `componentToForest`, from `right_surj` / `forest_surj`, `SectorBackwardMaps`) **+ the `A'` reassembly** | reassembly is the NEW leaf |
| `mixed_toFun_mem` / `forest_toFun_mem` | the `resolvedIsForestImage` star-touch classifier (`SectorForwardMembership`) | classifier fact |
| `mixed_invFun_mem` / `forest_invFun_mem` | the `p`-tag assignment of `invConstruct` (all-primitive ↔ ≥1 forest choice) | follows from reassembly |
| `mixed_left_inv` / `forest_left_inv` | the sector round-trips `right_left_inv` / `forest_left_inv` (`SectorLeafBundle`) lifted to the outer domain | sector inverse + outer lift |
| `mixed_right_inv` / `forest_right_inv` | the sector round-trips `right_right_inv` / `forest_right_inv` (`SectorLeafBundle`) lifted to the outer codomain | sector inverse + outer lift |

So the EXISTING sector pieces (`right_surj` / `forest_surj` / the four `SectorLeafBundle` inverse laws + the
`componentTo…_spec`s) cover the per-component surjectivity and per-sector round-trips; the genuinely-new content is
exactly the **`A'` reassembly** (gluing left-primitive pieces of `A`, right-survivor pieces of `B`, and forest
pieces reassembled from `promotedOf ⊔ remnant`, each tagged `inl true` / `inl false` / `inr Bᵧ`) and the **outer
lift** of the per-sector round-trips through that reassembly.  The `mixed` class (all-primitive) is the light case
— no forest choices, so its reconstruction is the left/right-primitive gluing only; the `forest` class carries the
remnant/forest sector.

## The record

`ResolvedOuterMixingBijectionProvider D S` fields exactly the nine outer-mixing bijection obligations against a
fixed summand bundle `S`; `.toBijectionSideSupply` plugs it, together with the contract-twice geometry and the base
data, into body-130's `ResolvedForestBlockBijectionSideSupply` (and hence `coassoc_gen`).  So the bijection half of
`coassoc_gen` is now a single named provider, and the residual is the `A'` reassembly + the outer round-trip lifts.

Per the HALT: only the dependency map / inventory; the nine fields are isolated and classified against the sector
machinery, the `A'` reassembly is named as the new leaf, and no inverse law is proved.

Landed:

* `ResolvedOuterMixingBijectionProvider D S` — the nine outer-mixing bijection fields against a summand bundle;
* `.toBijectionSideSupply` — into body-130's bijection-side supply (→ `coassoc_gen`).

Toolkit body (like body-130), one provider record.  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-131 — the outer-mixing bijection provider.**  The nine outer-mixing bijection obligations
(`invConstruct` + eight membership / inverse laws) against a fixed summand bundle `S` — the index/cover bijection
half of `coassoc_gen`, isolated for provider instantiation from the sector backward machinery. -/
structure ResolvedOuterMixingBijectionProvider (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) where
  /-- The backward map `(A_target, B) ↦ (A', p)` (sector backward + `A'` reassembly). -/
  invConstruct : ∀ (G : ResolvedFeynmanGraph), ForestBlockCodType D G → ForestBlockDomType D G
  /-- Mixed forward lands in the mixed codomain (star-avoiding classifier). -/
  mixed_toFun_mem : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G) (hq : q ∈ mixedDomFinset G),
    (⟨(S.Forward.imageSupply G).selectedOuterOf q, S.quotientForest q⟩ : ForestBlockCodType D G)
      ∈ mixedCodFinset (D := D) (fun {G} A B => resolvedIsForestImage A B) G
  /-- Mixed inverse lands in the mixed domain (all-primitive). -/
  mixed_invFun_mem : ∀ (G : ResolvedFeynmanGraph) (r : ForestBlockCodType D G)
    (hr : r ∈ mixedCodFinset (D := D) (fun {G} A B => resolvedIsForestImage A B) G),
    invConstruct G r ∈ mixedDomFinset G
  /-- Mixed `invConstruct ∘ toFun = id`. -/
  mixed_left_inv : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G) (hq : q ∈ mixedDomFinset G),
    invConstruct G
        (⟨(S.Forward.imageSupply G).selectedOuterOf q, S.quotientForest q⟩ : ForestBlockCodType D G)
      = q
  /-- Mixed `toFun ∘ invConstruct = id`. -/
  mixed_right_inv : ∀ (G : ResolvedFeynmanGraph) (r : ForestBlockCodType D G)
    (hr : r ∈ mixedCodFinset (D := D) (fun {G} A B => resolvedIsForestImage A B) G),
    (⟨(S.Forward.imageSupply G).selectedOuterOf (invConstruct G r),
        S.quotientForest (invConstruct G r)⟩ : ForestBlockCodType D G) = r
  /-- Forest forward lands in the forest-image codomain (star-touching classifier). -/
  forest_toFun_mem : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G)
    (hq : q ∈ forestCarryingDomFinset G),
    (⟨(S.Forward.imageSupply G).selectedOuterOf q, S.quotientForest q⟩ : ForestBlockCodType D G)
      ∈ forestCarryingCodFinset (D := D) (fun {G} A B => resolvedIsForestImage A B) G
  /-- Forest inverse lands in the forest-carrying domain (≥1 forest choice). -/
  forest_invFun_mem : ∀ (G : ResolvedFeynmanGraph) (r : ForestBlockCodType D G)
    (hr : r ∈ forestCarryingCodFinset (D := D) (fun {G} A B => resolvedIsForestImage A B) G),
    invConstruct G r ∈ forestCarryingDomFinset G
  /-- Forest `invConstruct ∘ toFun = id`. -/
  forest_left_inv : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G)
    (hq : q ∈ forestCarryingDomFinset G),
    invConstruct G
        (⟨(S.Forward.imageSupply G).selectedOuterOf q, S.quotientForest q⟩ : ForestBlockCodType D G)
      = q
  /-- Forest `toFun ∘ invConstruct = id`. -/
  forest_right_inv : ∀ (G : ResolvedFeynmanGraph) (r : ForestBlockCodType D G)
    (hr : r ∈ forestCarryingCodFinset (D := D) (fun {G} A B => resolvedIsForestImage A B) G),
    (⟨(S.Forward.imageSupply G).selectedOuterOf (invConstruct G r),
        S.quotientForest (invConstruct G r)⟩ : ForestBlockCodType D G) = r

/-- **R-6c-body-131 — the bijection-side supply from the provider + contract + base.**  Plugs the nine bijection
fields, the contract-twice geometry and the base data into body-130's `ResolvedForestBlockBijectionSideSupply`. -/
def ResolvedOuterMixingBijectionProvider.toBijectionSideSupply
    {S : ResolvedConcreteSummandBundleSupply D} (P : ResolvedOuterMixingBijectionProvider D S)
    (contract : ∀ (G : ResolvedFeynmanGraph),
      ResolvedContractTwiceOnceGeometrySupply D G
        (fun q => ⟨(S.Forward.imageSupply G).selectedOuterOf q, (S.quotientForest q).1⟩))
    (carrier_isProperForest : ∀ (G : ResolvedFeynmanGraph) (A : ResolvedAdmissibleSubgraph G),
      A ∈ D.carrier G → A.IsProperForest)
    (rep : ResolvedHopfGen → ResolvedFeynmanGraph)
    (repCD : ∀ x : ResolvedHopfGen, (rep x).forget.toClass.IsConnectedDivergent)
    (rep_gen : ∀ x : ResolvedHopfGen, x = (rep x).toResolvedHopfGen (repCD x)) :
    ResolvedForestBlockBijectionSideSupply D where
  Summand := S
  invConstruct := P.invConstruct
  mixed_toFun_mem := P.mixed_toFun_mem
  mixed_invFun_mem := P.mixed_invFun_mem
  mixed_left_inv := P.mixed_left_inv
  mixed_right_inv := P.mixed_right_inv
  forest_toFun_mem := P.forest_toFun_mem
  forest_invFun_mem := P.forest_invFun_mem
  forest_left_inv := P.forest_left_inv
  forest_right_inv := P.forest_right_inv
  contract := contract
  carrier_isProperForest := carrier_isProperForest
  rep := rep
  repCD := repCD
  rep_gen := rep_gen

/-- **R-6c-body-131 — `coassoc_gen` from the provider + contract + base.** -/
theorem ResolvedOuterMixingBijectionProvider.coassoc_gen
    {S : ResolvedConcreteSummandBundleSupply D} (P : ResolvedOuterMixingBijectionProvider D S)
    (contract : ∀ (G : ResolvedFeynmanGraph),
      ResolvedContractTwiceOnceGeometrySupply D G
        (fun q => ⟨(S.Forward.imageSupply G).selectedOuterOf q, (S.quotientForest q).1⟩))
    (carrier_isProperForest : ∀ (G : ResolvedFeynmanGraph) (A : ResolvedAdmissibleSubgraph G),
      A ∈ D.carrier G → A.IsProperForest)
    (rep : ResolvedHopfGen → ResolvedFeynmanGraph)
    (repCD : ∀ x : ResolvedHopfGen, (rep x).forget.toClass.IsConnectedDivergent)
    (rep_gen : ∀ x : ResolvedHopfGen, x = (rep x).toResolvedHopfGen (repCD x))
    (x : ResolvedHopfGen) :
    D.coassocLeft (MvPolynomial.X x) = D.coassocRight (MvPolynomial.X x) :=
  (P.toBijectionSideSupply contract carrier_isProperForest rep repCD rep_gen).coassoc_gen x

end GaugeGeometry.QFT.Combinatorial
