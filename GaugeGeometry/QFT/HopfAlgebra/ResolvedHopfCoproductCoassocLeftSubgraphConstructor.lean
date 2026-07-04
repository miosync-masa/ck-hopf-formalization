import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocOuterMixingMap
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSelectedOuterBridge

/-!
# R-6c-body-105 — leftSubgraph constructor: it IS the existing `selectedOuterOf` (left ∪ promoted)

Hundred-and-fifth genuine-body step, identifying body-104's target outer `leftSubgraph G q` with the EXISTING
selected-outer machinery.  The find: `ResolvedForestPromoteSupply.selectedOuterRawOf s = (leftOf s).union
(promotedOf s)` (`Promote` 61) — the union of the left-selected and promoted-forest components — is EXACTLY the
outer-mixing left subgraph (its own comment: "the resolved `forestComponentForestChoiceOuterSubgraph`").  So
`leftSubgraph G q = (imageSupply G).selectedOuterOf q`, and half the map is the existing image-side
construction.

## The identification

For a split choice `q = (A', p)` (`ForestBlockDomType D G = ResolvedCoassocSplitChoice D G`):

* `ResolvedSplitChoiceLeftSelectionSupply.leftOf q` — the LEFT-selected admissible forest (the primitive-left
  components `p γ = inl true`);
* `promotedOf q` — the PROMOTED admissible forest (the sub-forest components of the forest choices `p γ = inr
  Bᵧ`);
* `selectedOuterRawOf q = (leftOf q).union (promotedOf q)` — their union, and
  `ResolvedCoassocSelectedOuterImageSupply.selectedOuterOf q = ⟨selectedOuterRawOf q, selectedOuter_mem q⟩ : {A ∈
  carrier G}` bundles the carrier membership.

This is `A_target` on the nose.  Membership is FREE (the subtype `{A ∈ carrier G}`), and the left/promoted
component structure (`leftOf` / `promotedOf`) is now available for the left/right geometric identities.

## The connector

`ResolvedOuterMixingMapFromImageData` is body-104's map data with `leftSubgraph` replaced by a family
`imageSupply : ∀ G, ResolvedCoassocSelectedOuterImageSupply D G` (giving `leftSubgraph = selectedOuterOf` and its
membership for free).  `.toOuterMixingMapData` sets `leftSubgraph G q := (imageSupply G).selectedOuterOf q` and
passes the rest through; `.coassoc_gen` chains body-104/102/…/88.

Per the HALT: `leftSubgraph` is identified with the existing `selectedOuterOf` (union of left + promoted); its
membership is free; `quotientForest` / inverse / geometry are NOT constructed (still fielded); no FullQuotient
promote-supply construction (`leftOf` / `promotedOf`) is discharged.

Landed:

* `ResolvedOuterMixingMapFromImageData D` — body-104's map data with `leftSubgraph` from the image supply;
* `.toOuterMixingMapData` / `.coassoc_gen` — to body-104/102/101/98/…/88.

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

/-- **R-6c-body-105 — the map data with `leftSubgraph` from the image supply.**  Body-104's outer-mixing map
data, but the target outer `leftSubgraph` is the existing `selectedOuterOf` (`leftOf ∪ promotedOf`, with carrier
membership free), supplied by a family of `ResolvedCoassocSelectedOuterImageSupply`. -/
structure ResolvedOuterMixingMapFromImageData (D : ResolvedCoproductProperForestData) where
  /-- The selected-outer image supply per graph: `leftSubgraph = selectedOuterOf` (union of left + promoted). -/
  imageSupply : ∀ (G : ResolvedFeynmanGraph), ResolvedCoassocSelectedOuterImageSupply D G
  /-- The quotient forest `B` in `A_target.contractWithStars`. -/
  quotientForest : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G),
    (D.supply (((imageSupply G).selectedOuterOf q).1.contractWithStars
      (D.starOf G ((imageSupply G).selectedOuterOf q).1))).ForestIdx
  /-- The inverse constructor `(A_target, B) ↦ (A', p)`. -/
  invConstruct : ∀ (G : ResolvedFeynmanGraph), ForestBlockCodType D G → ForestBlockDomType D G
  -- MIXED class
  /-- Mixed target has no star touch. -/
  mixed_toFun_mem : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G) (hq : q ∈ mixedDomFinset G),
    (⟨(imageSupply G).selectedOuterOf q, quotientForest G q⟩ : ForestBlockCodType D G)
      ∈ mixedCodFinset (D := D) (fun {G} A B => resolvedIsForestImage A B) G
  /-- Mixed inverse lands in the mixed domain. -/
  mixed_invFun_mem : ∀ (G : ResolvedFeynmanGraph) (r : ForestBlockCodType D G)
    (hr : r ∈ mixedCodFinset (D := D) (fun {G} A B => resolvedIsForestImage A B) G),
    invConstruct G r ∈ mixedDomFinset G
  /-- Mixed `invConstruct ∘ toFun = id`. -/
  mixed_left_inv : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G) (hq : q ∈ mixedDomFinset G),
    invConstruct G (⟨(imageSupply G).selectedOuterOf q, quotientForest G q⟩ : ForestBlockCodType D G) = q
  /-- Mixed `toFun ∘ invConstruct = id`. -/
  mixed_right_inv : ∀ (G : ResolvedFeynmanGraph) (r : ForestBlockCodType D G)
    (hr : r ∈ mixedCodFinset (D := D) (fun {G} A B => resolvedIsForestImage A B) G),
    (⟨(imageSupply G).selectedOuterOf (invConstruct G r),
        quotientForest G (invConstruct G r)⟩ : ForestBlockCodType D G) = r
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
          (D.starOf G ((imageSupply G).selectedOuterOf q).1))).leftTerm (quotientForest G q)
  /-- Mixed geometric identity: `rightTerm A' = rightTerm B` (contract-twice). -/
  mixed_quot_eq : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G) (hq : q ∈ mixedDomFinset G),
    (D.supply G).rightTerm q.1
      = (D.supply (((imageSupply G).selectedOuterOf q).1.contractWithStars
          (D.starOf G ((imageSupply G).selectedOuterOf q).1))).rightTerm (quotientForest G q)
  -- FOREST class
  /-- Forest target has a star touch. -/
  forest_toFun_mem : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G)
    (hq : q ∈ forestCarryingDomFinset G),
    (⟨(imageSupply G).selectedOuterOf q, quotientForest G q⟩ : ForestBlockCodType D G)
      ∈ forestCarryingCodFinset (D := D) (fun {G} A B => resolvedIsForestImage A B) G
  /-- Forest inverse lands in the forest domain. -/
  forest_invFun_mem : ∀ (G : ResolvedFeynmanGraph) (r : ForestBlockCodType D G)
    (hr : r ∈ forestCarryingCodFinset (D := D) (fun {G} A B => resolvedIsForestImage A B) G),
    invConstruct G r ∈ forestCarryingDomFinset G
  /-- Forest `invConstruct ∘ toFun = id`. -/
  forest_left_inv : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G)
    (hq : q ∈ forestCarryingDomFinset G),
    invConstruct G (⟨(imageSupply G).selectedOuterOf q, quotientForest G q⟩ : ForestBlockCodType D G) = q
  /-- Forest `toFun ∘ invConstruct = id`. -/
  forest_right_inv : ∀ (G : ResolvedFeynmanGraph) (r : ForestBlockCodType D G)
    (hr : r ∈ forestCarryingCodFinset (D := D) (fun {G} A B => resolvedIsForestImage A B) G),
    (⟨(imageSupply G).selectedOuterOf (invConstruct G r),
        quotientForest G (invConstruct G r)⟩ : ForestBlockCodType D G) = r
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
          (D.starOf G ((imageSupply G).selectedOuterOf q).1))).leftTerm (quotientForest G q)
  /-- Forest geometric identity: `rightTerm A' = rightTerm B` (contract-twice). -/
  forest_quot_eq : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G)
    (hq : q ∈ forestCarryingDomFinset G),
    (D.supply G).rightTerm q.1
      = (D.supply (((imageSupply G).selectedOuterOf q).1.contractWithStars
          (D.starOf G ((imageSupply G).selectedOuterOf q).1))).rightTerm (quotientForest G q)
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

/-- **R-6c-body-105 — body-104's map data from the image supply.**  `leftSubgraph G q := (imageSupply
G).selectedOuterOf q`. -/
noncomputable def ResolvedOuterMixingMapFromImageData.toOuterMixingMapData
    (S : ResolvedOuterMixingMapFromImageData D) : ResolvedOuterMixingMapData D where
  leftSubgraph := fun G q => (S.imageSupply G).selectedOuterOf q
  quotientForest := S.quotientForest
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

/-- **R-6c-body-105 — `coassoc_gen` from the image-supply map data** (via body-104/…/88). -/
theorem ResolvedOuterMixingMapFromImageData.coassoc_gen
    (S : ResolvedOuterMixingMapFromImageData D) (x : ResolvedHopfGen) :
    D.coassocLeft (MvPolynomial.X x) = D.coassocRight (MvPolynomial.X x) :=
  S.toOuterMixingMapData.coassoc_gen x

end GaugeGeometry.QFT.Combinatorial
