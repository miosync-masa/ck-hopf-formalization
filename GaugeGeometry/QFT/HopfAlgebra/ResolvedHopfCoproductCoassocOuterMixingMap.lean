import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestBlockTermFactors

/-!
# R-6c-body-104 — outer-mixing map construction scout: one shared `leftSubgraph`/`quotientForest` constructor

Hundred-and-fourth genuine-body step, placing the outer-mixing map itself into types.  Both `mixedToFun` and
`forestToFun` (body-101/102) are built from a SINGLE shared constructor — a `leftSubgraph`/`quotientForest` pair
that sends a split choice `(A', p)` to its target `(A_target, B)` — with a shared `invConstruct` for the inverse.
The remaining obligations are exactly the membership/inverse/geometry facts, now fielded against these concrete
constructors.

## The shared map constructor

For a split choice `q = (A', p)` (note `ForestBlockDomType D G` IS `ResolvedCoassocSplitChoice D G`):

* `leftSubgraph G q : {A ∈ carrier G}` — the target outer forest `A_target`: the components `p` selects to the
  LEFT (left-primitive components `p γ = inl true`, plus the sub-forest components of the forest choices `p γ =
  inr Bᵧ`).  Flat `forestComponentChoiceLeftSubgraph` (`Coassoc` 2651);
* `quotientForest G q : (D.supply (leftSubgraph.contractWithStars starOf)).ForestIdx` — the quotient forest `B`
  in `A_target.contractWithStars`: the right-primitive components (mixed) plus the quotient images of the forest
  choices (forest).  Flat `forestComponent{Mixed,Forest}…RepQuotientSubgraphCanonical` (14456/14540).

`outerMixingToFun G q := ⟨leftSubgraph G q, quotientForest G q⟩ : ForestBlockCodType D G` is then the shared
target, and `mixedToFun = forestToFun = outerMixingToFun` (restricted to their sub-domains).  `invConstruct`
reconstructs `(A', p)` from `(A_target, B)`.

## What remains (all fielded against the constructors)

* MEMBERSHIP (`…ToFun_mem` / `…InvFun_mem`): the classification — a mixed choice's target has `¬
  resolvedIsForestImage` (no star touch), a forest choice's has `resolvedIsForestImage` (star touch);
* INVERSE (`…Left_inv` / `…Right_inv`): `invConstruct ∘ toFun = id` and `toFun ∘ invConstruct = id`;
* the six GEOMETRIC identities (body-103): `∏ leftFactor = leftTerm (leftSubgraph G q)`, `∏ rightFactor =
  leftTerm (quotientForest G q)`, `rightTerm A' = rightTerm (quotientForest G q)` — each a component-set
  correspondence + the proved product algebra + the contract-twice generator identity.

## The reduction

`.toForestBlockConcreteMapData` sets `mixedToFun = forestToFun = ⟨leftSubgraph, quotientForest⟩` and
`mixedInvFun = forestInvFun = invConstruct`, and passes the remaining fields through; `.coassoc_gen` chains
body-102/101/98/…/88.

Per the HALT: the map SHAPE is fixed via one shared `leftSubgraph`/`quotientForest`/`invConstruct` triple;
membership / inverse laws / geometric identities are NOT proved (they are the fields); no FullQuotient
construction is instantiated; no star allocation detail.

Landed:

* `ResolvedOuterMixingMapData D` — the shared map constructor + membership/inverse/geometry fields;
* `.toForestBlockConcreteMapData` / `.coassoc_gen` — to body-102/101/98/96/95/94/93/92/91/90/88.

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

/-- **R-6c-body-104 — the outer-mixing map data.**  One shared `leftSubgraph`/`quotientForest` constructor for
`(A', p) ↦ (A_target, B)` (used for BOTH `mixedToFun` and `forestToFun`) and a shared `invConstruct`, plus the
membership / inverse / geometric fields against these constructors. -/
structure ResolvedOuterMixingMapData (D : ResolvedCoproductProperForestData) where
  /-- The target outer forest `A_target` — the left-selected components of `p`. -/
  leftSubgraph : ∀ (G : ResolvedFeynmanGraph), ForestBlockDomType D G →
    {A : ResolvedAdmissibleSubgraph G // A ∈ D.carrier G}
  /-- The quotient forest `B` in `A_target.contractWithStars` — the right-selected / forest pieces. -/
  quotientForest : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G),
    (D.supply ((leftSubgraph G q).1.contractWithStars (D.starOf G (leftSubgraph G q).1))).ForestIdx
  /-- The inverse constructor `(A_target, B) ↦ (A', p)`. -/
  invConstruct : ∀ (G : ResolvedFeynmanGraph), ForestBlockCodType D G → ForestBlockDomType D G
  -- MIXED class
  /-- Mixed target has no star touch. -/
  mixed_toFun_mem : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G) (hq : q ∈ mixedDomFinset G),
    (⟨leftSubgraph G q, quotientForest G q⟩ : ForestBlockCodType D G)
      ∈ mixedCodFinset (D := D) (fun {G} A B => resolvedIsForestImage A B) G
  /-- Mixed inverse lands in the mixed domain. -/
  mixed_invFun_mem : ∀ (G : ResolvedFeynmanGraph) (r : ForestBlockCodType D G)
    (hr : r ∈ mixedCodFinset (D := D) (fun {G} A B => resolvedIsForestImage A B) G),
    invConstruct G r ∈ mixedDomFinset G
  /-- Mixed `invConstruct ∘ toFun = id`. -/
  mixed_left_inv : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G) (hq : q ∈ mixedDomFinset G),
    invConstruct G (⟨leftSubgraph G q, quotientForest G q⟩ : ForestBlockCodType D G) = q
  /-- Mixed `toFun ∘ invConstruct = id`. -/
  mixed_right_inv : ∀ (G : ResolvedFeynmanGraph) (r : ForestBlockCodType D G)
    (hr : r ∈ mixedCodFinset (D := D) (fun {G} A B => resolvedIsForestImage A B) G),
    (⟨leftSubgraph G (invConstruct G r), quotientForest G (invConstruct G r)⟩ : ForestBlockCodType D G) = r
  /-- Mixed geometric identity: `∏ leftFactor = leftTerm A_target`. -/
  mixed_left_eq : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G) (hq : q ∈ mixedDomFinset G),
    (∏ γ ∈ (q.1.1.elements.attach).attach,
        localLeftFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2))
      = (D.supply G).leftTerm (leftSubgraph G q)
  /-- Mixed geometric identity: `∏ rightFactor = leftTerm B`. -/
  mixed_right_eq : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G) (hq : q ∈ mixedDomFinset G),
    (∏ γ ∈ (q.1.1.elements.attach).attach,
        localRightFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2))
      = (D.supply ((leftSubgraph G q).1.contractWithStars (D.starOf G (leftSubgraph G q).1))).leftTerm
          (quotientForest G q)
  /-- Mixed geometric identity: `rightTerm A' = rightTerm B` (contract-twice). -/
  mixed_quot_eq : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G) (hq : q ∈ mixedDomFinset G),
    (D.supply G).rightTerm q.1
      = (D.supply ((leftSubgraph G q).1.contractWithStars (D.starOf G (leftSubgraph G q).1))).rightTerm
          (quotientForest G q)
  -- FOREST class
  /-- Forest target has a star touch. -/
  forest_toFun_mem : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G)
    (hq : q ∈ forestCarryingDomFinset G),
    (⟨leftSubgraph G q, quotientForest G q⟩ : ForestBlockCodType D G)
      ∈ forestCarryingCodFinset (D := D) (fun {G} A B => resolvedIsForestImage A B) G
  /-- Forest inverse lands in the forest domain. -/
  forest_invFun_mem : ∀ (G : ResolvedFeynmanGraph) (r : ForestBlockCodType D G)
    (hr : r ∈ forestCarryingCodFinset (D := D) (fun {G} A B => resolvedIsForestImage A B) G),
    invConstruct G r ∈ forestCarryingDomFinset G
  /-- Forest `invConstruct ∘ toFun = id`. -/
  forest_left_inv : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G)
    (hq : q ∈ forestCarryingDomFinset G),
    invConstruct G (⟨leftSubgraph G q, quotientForest G q⟩ : ForestBlockCodType D G) = q
  /-- Forest `toFun ∘ invConstruct = id`. -/
  forest_right_inv : ∀ (G : ResolvedFeynmanGraph) (r : ForestBlockCodType D G)
    (hr : r ∈ forestCarryingCodFinset (D := D) (fun {G} A B => resolvedIsForestImage A B) G),
    (⟨leftSubgraph G (invConstruct G r), quotientForest G (invConstruct G r)⟩ : ForestBlockCodType D G) = r
  /-- Forest geometric identity: `∏ leftFactor = leftTerm A_target`. -/
  forest_left_eq : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G)
    (hq : q ∈ forestCarryingDomFinset G),
    (∏ γ ∈ (q.1.1.elements.attach).attach,
        localLeftFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2))
      = (D.supply G).leftTerm (leftSubgraph G q)
  /-- Forest geometric identity: `∏ rightFactor = leftTerm B`. -/
  forest_right_eq : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G)
    (hq : q ∈ forestCarryingDomFinset G),
    (∏ γ ∈ (q.1.1.elements.attach).attach,
        localRightFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2))
      = (D.supply ((leftSubgraph G q).1.contractWithStars (D.starOf G (leftSubgraph G q).1))).leftTerm
          (quotientForest G q)
  /-- Forest geometric identity: `rightTerm A' = rightTerm B` (contract-twice). -/
  forest_quot_eq : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G)
    (hq : q ∈ forestCarryingDomFinset G),
    (D.supply G).rightTerm q.1
      = (D.supply ((leftSubgraph G q).1.contractWithStars (D.starOf G (leftSubgraph G q).1))).rightTerm
          (quotientForest G q)
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

/-- **R-6c-body-104 — body-102's concrete map data from the shared constructor.**  `mixedToFun = forestToFun =
⟨leftSubgraph, quotientForest⟩`, `mixedInvFun = forestInvFun = invConstruct`. -/
def ResolvedOuterMixingMapData.toForestBlockConcreteMapData
    (S : ResolvedOuterMixingMapData D) : ResolvedForestBlockConcreteMapData D where
  mixedToFun := fun G q _ => ⟨S.leftSubgraph G q, S.quotientForest G q⟩
  mixedInvFun := fun G r _ => S.invConstruct G r
  mixedToFun_mem := S.mixed_toFun_mem
  mixedInvFun_mem := S.mixed_invFun_mem
  mixedLeft_inv := S.mixed_left_inv
  mixedRight_inv := S.mixed_right_inv
  mixed_left_eq := S.mixed_left_eq
  mixed_right_eq := S.mixed_right_eq
  mixed_quot_eq := S.mixed_quot_eq
  forestToFun := fun G q _ => ⟨S.leftSubgraph G q, S.quotientForest G q⟩
  forestInvFun := fun G r _ => S.invConstruct G r
  forestToFun_mem := S.forest_toFun_mem
  forestInvFun_mem := S.forest_invFun_mem
  forestLeft_inv := S.forest_left_inv
  forestRight_inv := S.forest_right_inv
  forest_left_eq := S.forest_left_eq
  forest_right_eq := S.forest_right_eq
  forest_quotient_eq := S.forest_quot_eq
  carrier_isProperForest := S.carrier_isProperForest
  rep := S.rep
  repCD := S.repCD
  rep_gen := S.rep_gen

/-- **R-6c-body-104 — `coassoc_gen` from the shared map constructor** (via body-102/…/88). -/
theorem ResolvedOuterMixingMapData.coassoc_gen
    (S : ResolvedOuterMixingMapData D) (x : ResolvedHopfGen) :
    D.coassocLeft (MvPolynomial.X x) = D.coassocRight (MvPolynomial.X x) :=
  S.toForestBlockConcreteMapData.coassoc_gen x

end GaugeGeometry.QFT.Combinatorial
