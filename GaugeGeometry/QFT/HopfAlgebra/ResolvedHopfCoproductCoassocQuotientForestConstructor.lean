import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocLeftSubgraphConstructor

/-!
# R-6c-body-106 — quotientForest constructor recovery: `B` is the existing `quotientForestOf` + membership

Hundred-and-sixth genuine-body step, recovering body-104/105's target quotient forest `quotientForest G q` from
the existing σ-cover quotient machinery — the second half of the forward map.  The existing
`ResolvedCoassocFullQuotientSupply.quotientForestOf s` (`QuotientBody` 97) already has the target ambient type
`ResolvedAdmissibleSubgraph ((selectedOuterOf s).1.contractWithStars (D.starOf G (selectedOuterOf s).1))` — the
raw quotient subgraph over `A_target.contractWithStars`.  So the only new obligation is its CARRIER membership;
`quotientForest = ⟨quotientRaw, quotient_mem⟩`.

## The recovery

For a split choice `q` with `A_target = (imageSupply G).selectedOuterOf q` (body-105):

* `quotientRaw G q : ResolvedAdmissibleSubgraph (A_target.contractWithStars starOf)` — the raw quotient forest
  `B`, EXACTLY the type of `(fullQuotient G).quotientForestOf q = (fullQuotientOf q).toImage` (remnant ⊔ right
  survivors);
* `quotient_mem G q : quotientRaw G q ∈ D.carrier (A_target.contractWithStars starOf)` — the carrier membership
  (a proper-forest obligation on the quotient, NOT provided by the existing `quotientForestOf`, which only
  carries the `isForestByStar` discriminator witness).

Then `quotientForest G q := ⟨quotientRaw G q, quotient_mem G q⟩ : (D.supply _).ForestIdx`, and the forward map
`outerMixingToFun q = ⟨A_target, B⟩` is LITERALLY the existing image-side construction `⟨selectedOuterOf q,
quotientForestOf q⟩` — both halves recovered from σ-cover machinery.

## The connector

`ResolvedOuterMixingMapFromQuotientData` is body-105's data with `quotientForest` split into `quotientRaw` (the
existing quotient subgraph type) plus `quotient_mem`.  `.toImageData` sets `quotientForest := ⟨quotientRaw,
quotient_mem⟩` and passes the rest through; `.coassoc_gen` chains body-105/104/…/88.

Per the HALT: the quotient forest's ambient type is identified with the existing `quotientForestOf`; only its
carrier membership is a new field; inverse laws / geometry are NOT proved; no `FullQuotientSupply` /
`SigmaDataSupply` chain instantiated (`quotientRaw` abstracts it).

Landed:

* `ResolvedOuterMixingMapFromQuotientData D` — the map data with `quotientForest` from `quotientRaw` +
  `quotient_mem` (and `leftSubgraph` from body-105's `imageSupply`);
* `.toImageData` / `.coassoc_gen` — to body-105/104/102/101/98/…/88.

No facade, no flat term, no `forgetHopf`.
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
set_option linter.unusedVariables false

/-- **R-6c-body-106 — the map data with `quotientForest` recovered from the existing `quotientForestOf`.**
Body-105's data, but the target quotient forest `B` is a raw quotient subgraph (`quotientRaw`, the existing
`quotientForestOf` type) plus a carrier-membership field (`quotient_mem`). -/
structure ResolvedOuterMixingMapFromQuotientData (D : ResolvedCoproductProperForestData) where
  /-- The selected-outer image supply per graph (body-105): `leftSubgraph = selectedOuterOf`. -/
  imageSupply : ∀ (G : ResolvedFeynmanGraph), ResolvedCoassocSelectedOuterImageSupply D G
  /-- The raw quotient forest `B` (the existing `quotientForestOf` type). -/
  quotientRaw : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G),
    ResolvedAdmissibleSubgraph (((imageSupply G).selectedOuterOf q).1.contractWithStars
      (D.starOf G ((imageSupply G).selectedOuterOf q).1))
  /-- The quotient forest lies in the quotient graph's carrier. -/
  quotient_mem : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G),
    quotientRaw G q ∈ D.carrier (((imageSupply G).selectedOuterOf q).1.contractWithStars
      (D.starOf G ((imageSupply G).selectedOuterOf q).1))
  /-- The inverse constructor `(A_target, B) ↦ (A', p)`. -/
  invConstruct : ∀ (G : ResolvedFeynmanGraph), ForestBlockCodType D G → ForestBlockDomType D G
  -- MIXED class
  /-- Mixed target has no star touch. -/
  mixed_toFun_mem : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G) (hq : q ∈ mixedDomFinset G),
    (⟨(imageSupply G).selectedOuterOf q, ⟨quotientRaw G q, quotient_mem G q⟩⟩ : ForestBlockCodType D G)
      ∈ mixedCodFinset (D := D) (fun {G} A B => resolvedIsForestImage A B) G
  /-- Mixed inverse lands in the mixed domain. -/
  mixed_invFun_mem : ∀ (G : ResolvedFeynmanGraph) (r : ForestBlockCodType D G)
    (hr : r ∈ mixedCodFinset (D := D) (fun {G} A B => resolvedIsForestImage A B) G),
    invConstruct G r ∈ mixedDomFinset G
  /-- Mixed `invConstruct ∘ toFun = id`. -/
  mixed_left_inv : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G) (hq : q ∈ mixedDomFinset G),
    invConstruct G
        (⟨(imageSupply G).selectedOuterOf q, ⟨quotientRaw G q, quotient_mem G q⟩⟩ : ForestBlockCodType D G) = q
  /-- Mixed `toFun ∘ invConstruct = id`. -/
  mixed_right_inv : ∀ (G : ResolvedFeynmanGraph) (r : ForestBlockCodType D G)
    (hr : r ∈ mixedCodFinset (D := D) (fun {G} A B => resolvedIsForestImage A B) G),
    (⟨(imageSupply G).selectedOuterOf (invConstruct G r),
        ⟨quotientRaw G (invConstruct G r), quotient_mem G (invConstruct G r)⟩⟩ : ForestBlockCodType D G) = r
  /-- Mixed geometric identity: `∏ leftFactor = leftTerm A_target`. -/
  mixed_left_eq : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G) (hq : q ∈ mixedDomFinset G),
    (∏ γ ∈ (q.1.1.elements.attach).attach,
        localLeftFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2))
      = (D.supply G).leftTerm ((imageSupply G).selectedOuterOf q)
  /-- Mixed geometric identity: `∏ rightFactor = leftTerm B`. -/
  mixed_right_eq : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G) (hq : q ∈ mixedDomFinset G),
    (∏ γ ∈ (q.1.1.elements.attach).attach,
        localRightFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2))
      = (D.supply (((imageSupply G).selectedOuterOf q).1.contractWithStars
          (D.starOf G ((imageSupply G).selectedOuterOf q).1))).leftTerm ⟨quotientRaw G q, quotient_mem G q⟩
  /-- Mixed geometric identity: `rightTerm A' = rightTerm B` (contract-twice). -/
  mixed_quot_eq : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G) (hq : q ∈ mixedDomFinset G),
    (D.supply G).rightTerm q.1
      = (D.supply (((imageSupply G).selectedOuterOf q).1.contractWithStars
          (D.starOf G ((imageSupply G).selectedOuterOf q).1))).rightTerm ⟨quotientRaw G q, quotient_mem G q⟩
  -- FOREST class
  /-- Forest target has a star touch. -/
  forest_toFun_mem : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G)
    (hq : q ∈ forestCarryingDomFinset G),
    (⟨(imageSupply G).selectedOuterOf q, ⟨quotientRaw G q, quotient_mem G q⟩⟩ : ForestBlockCodType D G)
      ∈ forestCarryingCodFinset (D := D) (fun {G} A B => resolvedIsForestImage A B) G
  /-- Forest inverse lands in the forest domain. -/
  forest_invFun_mem : ∀ (G : ResolvedFeynmanGraph) (r : ForestBlockCodType D G)
    (hr : r ∈ forestCarryingCodFinset (D := D) (fun {G} A B => resolvedIsForestImage A B) G),
    invConstruct G r ∈ forestCarryingDomFinset G
  /-- Forest `invConstruct ∘ toFun = id`. -/
  forest_left_inv : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G)
    (hq : q ∈ forestCarryingDomFinset G),
    invConstruct G
        (⟨(imageSupply G).selectedOuterOf q, ⟨quotientRaw G q, quotient_mem G q⟩⟩ : ForestBlockCodType D G) = q
  /-- Forest `toFun ∘ invConstruct = id`. -/
  forest_right_inv : ∀ (G : ResolvedFeynmanGraph) (r : ForestBlockCodType D G)
    (hr : r ∈ forestCarryingCodFinset (D := D) (fun {G} A B => resolvedIsForestImage A B) G),
    (⟨(imageSupply G).selectedOuterOf (invConstruct G r),
        ⟨quotientRaw G (invConstruct G r), quotient_mem G (invConstruct G r)⟩⟩ : ForestBlockCodType D G) = r
  /-- Forest geometric identity: `∏ leftFactor = leftTerm A_target`. -/
  forest_left_eq : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G)
    (hq : q ∈ forestCarryingDomFinset G),
    (∏ γ ∈ (q.1.1.elements.attach).attach,
        localLeftFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2))
      = (D.supply G).leftTerm ((imageSupply G).selectedOuterOf q)
  /-- Forest geometric identity: `∏ rightFactor = leftTerm B`. -/
  forest_right_eq : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G)
    (hq : q ∈ forestCarryingDomFinset G),
    (∏ γ ∈ (q.1.1.elements.attach).attach,
        localRightFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2))
      = (D.supply (((imageSupply G).selectedOuterOf q).1.contractWithStars
          (D.starOf G ((imageSupply G).selectedOuterOf q).1))).leftTerm ⟨quotientRaw G q, quotient_mem G q⟩
  /-- Forest geometric identity: `rightTerm A' = rightTerm B` (contract-twice). -/
  forest_quot_eq : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G)
    (hq : q ∈ forestCarryingDomFinset G),
    (D.supply G).rightTerm q.1
      = (D.supply (((imageSupply G).selectedOuterOf q).1.contractWithStars
          (D.starOf G ((imageSupply G).selectedOuterOf q).1))).rightTerm ⟨quotientRaw G q, quotient_mem G q⟩
  -- shared
  /-- Every carrier forest is a proper forest (body-96). -/
  carrier_isProperForest : ∀ (G : ResolvedFeynmanGraph) (A : ResolvedAdmissibleSubgraph G),
    A ∈ D.carrier G → A.IsProperForest
  /-- A representative graph for each generator. -/
  rep : ResolvedHopfGen → ResolvedFeynmanGraph
  /-- The representative is connected-divergent. -/
  repCD : ∀ x : ResolvedHopfGen, (rep x).forget.toClass.IsConnectedDivergent
  /-- The representative's generator IS `x`. -/
  rep_gen : ∀ x : ResolvedHopfGen, x = (rep x).toResolvedHopfGen (repCD x)

/-- **R-6c-body-106 — body-105's image map data from the recovered quotient forest.**  `quotientForest G q :=
⟨quotientRaw G q, quotient_mem G q⟩`. -/
def ResolvedOuterMixingMapFromQuotientData.toImageData
    (S : ResolvedOuterMixingMapFromQuotientData D) : ResolvedOuterMixingMapFromImageData D where
  imageSupply := S.imageSupply
  quotientForest := fun G q => ⟨S.quotientRaw G q, S.quotient_mem G q⟩
  invConstruct := S.invConstruct
  mixed_toFun_mem := S.mixed_toFun_mem
  mixed_invFun_mem := S.mixed_invFun_mem
  mixed_left_inv := S.mixed_left_inv
  mixed_right_inv := S.mixed_right_inv
  mixed_left_eq := S.mixed_left_eq
  mixed_right_eq := S.mixed_right_eq
  mixed_quot_eq := S.mixed_quot_eq
  forest_toFun_mem := S.forest_toFun_mem
  forest_invFun_mem := S.forest_invFun_mem
  forest_left_inv := S.forest_left_inv
  forest_right_inv := S.forest_right_inv
  forest_left_eq := S.forest_left_eq
  forest_right_eq := S.forest_right_eq
  forest_quot_eq := S.forest_quot_eq
  carrier_isProperForest := S.carrier_isProperForest
  rep := S.rep
  repCD := S.repCD
  rep_gen := S.rep_gen

/-- **R-6c-body-106 — `coassoc_gen` from the recovered quotient forest** (via body-105/…/88). -/
theorem ResolvedOuterMixingMapFromQuotientData.coassoc_gen
    (S : ResolvedOuterMixingMapFromQuotientData D) (x : ResolvedHopfGen) :
    D.coassocLeft (MvPolynomial.X x) = D.coassocRight (MvPolynomial.X x) :=
  S.toImageData.coassoc_gen x

end GaugeGeometry.QFT.Combinatorial
