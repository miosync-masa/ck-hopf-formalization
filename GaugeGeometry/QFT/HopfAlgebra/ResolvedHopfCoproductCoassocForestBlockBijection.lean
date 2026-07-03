import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocOuterNonemptyAdapter

/-!
# R-6c-body-97 — forest_block bijection skeleton: the outer-mixing `(A', p) ↔ (A, B)` reindex

Ninety-seventh genuine-body step, entering the raid boss `forest_block` itself.  This pass fixes the domain /
codomain index types and the outer-mixing bijection map, deferring only the inverse laws and summand agreement to
supply fields.  The crucial design point — the outer forest is NOT preserved — is encoded in the types: the
domain outer `A'` and the codomain outer `A` are separate `Σ`-components.

## The two flattened `Σ`-indices (outer NOT preserved)

* DOMAIN `ForestBlockDomType` = `Σ A' : {A' ∈ carrier G}, (component choice `p`)`.  The forest sum's index, with
  `p` ranging over `forestChoiceCarrier A'` (= `piCarrier A' \ {p_R, p_L}`, body-94/95).
* CODOMAIN `ForestBlockCodType` = `Σ A : {A ∈ carrier G}, (D.supply (A.contractWithStars (starOf G A))).ForestIdx`.
  The quotient-forest sum's index: outer `A` plus a proper forest `B` of the quotient graph.

`forest_block` is exactly `∑_{domF} splitTerm = ∑_{codF} leftTerm A ⊗ (leftTerm B ⊗ rightTerm B)` after
`Finset.sum_sigma'` flattens both double sums.

## The bijection (outer-mixing), matching flat 27348

`ResolvedForestBlockBijectionSupply` fields the `Finset.sum_bij'` data between `domF` and `codF`: `toFun` (`(A',
p) ↦ (A, B)`), `invFun`, the membership `maps_to`s, the two inverse laws, and `summand_agree` (`splitTerm ⟨A', p⟩
= leftTerm A ⊗ (leftTerm B ⊗ rightTerm B)`).  Because `toFun`'s codomain outer `A` is a fresh `Σ`-component, the
outer-mixing (`A ⊇ A'`) is free in the type — exactly the flat picture, where the two class maps
`forestComponentForestChoiceToQuotientForestSigma` / `forestComponentMixedBoundaryToQuotientForestSigma`
(`Coassoc` 14456 / 14540) send `⟨A', p⟩` to `⟨…OuterIndex g q hq, …RepQuotientSubgraphCanonical g q hq⟩` with a
DIFFERENT outer `…OuterIndex ≠ A'`.

## The two internal classes (documented, folded into the single map)

The flat domain splits into `forestComponentForestChoiceSigmaIndex` (≥ 1 component picks a real sub-forest) and
`forestComponentMixedBoundaryChoiceSigmaIndex` (only left/right primitives, mixed) — a DISJOINT union covering
`forestChoiceCarrier`.  Here they are folded into the single `toFun` (definable by cases on `p`); the skeleton
fixes the endpoints, and the case split is the map's internal business, deferred with the inverse laws.  (The
left-selected components of `p` enlarge `A'` to `A`; the right-primitive / forest components form `B`.)

## The reduction

`.toForestCarrierProperSupply` builds body-96's supply: it flattens both sides (`Finset.sum_sigma'`) and applies
`Finset.sum_bij'` with the fielded data; `.coassoc_gen` chains body-96/95/94/93/92/91/90/88.

Per the HALT: the inverse laws / summand agreement are NOT proved (they are the fields); the domain/codomain
index types and the outer-mixing map are fixed; the two-class split is documented; no forest-cover union
construction, no star/retarget detail.

Landed:

* `ForestBlockDomType` / `ForestBlockCodType` — the flattened `Σ`-indices (outer NOT preserved);
* `forestBlockDomFinset` / `forestBlockCodFinset` — the two carriers;
* `ResolvedForestBlockBijectionSupply D` — the `sum_bij'` data + `carrier_isProperForest` + representative lift;
* `.toForestCarrierProperSupply` / `.coassoc_gen` — to body-96/95/94/93/92/91/90/88.

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

/-- **R-6c-body-97 — the DOMAIN index type** (forest sum): an outer forest `A'` plus a component choice. -/
abbrev ForestBlockDomType (D : ResolvedCoproductProperForestData) (G : ResolvedFeynmanGraph) :=
  (A : {A : ResolvedAdmissibleSubgraph G // A ∈ D.carrier G}) ×
    (∀ γ ∈ A.1.elements.attach, Bool ⊕ (D.supply (γ.1.toResolvedFeynmanGraph)).ForestIdx)

/-- **R-6c-body-97 — the CODOMAIN index type** (quotient-forest sum): an outer forest `A` plus a proper forest
`B` of the quotient graph.  The outer `A` is a SEPARATE component — the outer is not preserved by the map. -/
abbrev ForestBlockCodType (D : ResolvedCoproductProperForestData) (G : ResolvedFeynmanGraph) :=
  (A : {A : ResolvedAdmissibleSubgraph G // A ∈ D.carrier G}) ×
    (D.supply (A.1.contractWithStars (D.starOf G A.1))).ForestIdx

/-- **R-6c-body-97 — the DOMAIN carrier.**  `Σ A', forestChoiceCarrier A'`. -/
noncomputable def forestBlockDomFinset (G : ResolvedFeynmanGraph) : Finset (ForestBlockDomType D G) :=
  ((D.carrier G).attach).sigma (fun A => forestChoiceCarrier A)

/-- **R-6c-body-97 — the CODOMAIN carrier.**  `Σ A, (quotient graph proper forests)`. -/
noncomputable def forestBlockCodFinset (G : ResolvedFeynmanGraph) : Finset (ForestBlockCodType D G) :=
  ((D.carrier G).attach).sigma
    (fun A => (D.supply (A.1.contractWithStars (D.starOf G A.1))).forestCarrier)

/-- **R-6c-body-97 — the forest-block bijection supply.**  The `Finset.sum_bij'` data for the outer-mixing
reindex `(A', p) ↔ (A, B)`, plus `carrier_isProperForest` (body-96) and a representative lift. -/
structure ResolvedForestBlockBijectionSupply (D : ResolvedCoproductProperForestData) where
  /-- The outer-mixing map `(A', p) ↦ (A, B)` (`A` a fresh outer, generally `⊇ A'`). -/
  toFun : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G),
    q ∈ forestBlockDomFinset G → ForestBlockCodType D G
  /-- The inverse `(A, B) ↦ (A', p)`. -/
  invFun : ∀ (G : ResolvedFeynmanGraph) (r : ForestBlockCodType D G),
    r ∈ forestBlockCodFinset G → ForestBlockDomType D G
  /-- `toFun` lands in the codomain carrier. -/
  toFun_mem : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G) (hq : q ∈ forestBlockDomFinset G),
    toFun G q hq ∈ forestBlockCodFinset G
  /-- `invFun` lands in the domain carrier. -/
  invFun_mem : ∀ (G : ResolvedFeynmanGraph) (r : ForestBlockCodType D G) (hr : r ∈ forestBlockCodFinset G),
    invFun G r hr ∈ forestBlockDomFinset G
  /-- `invFun ∘ toFun = id`. -/
  left_inv : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G) (hq : q ∈ forestBlockDomFinset G),
    invFun G (toFun G q hq) (toFun_mem G q hq) = q
  /-- `toFun ∘ invFun = id`. -/
  right_inv : ∀ (G : ResolvedFeynmanGraph) (r : ForestBlockCodType D G) (hr : r ∈ forestBlockCodFinset G),
    toFun G (invFun G r hr) (invFun_mem G r hr) = r
  /-- The summand agreement: `splitTerm ⟨A', p⟩ = leftTerm A ⊗ (leftTerm B ⊗ rightTerm B)`. -/
  summand_agree : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G) (hq : q ∈ forestBlockDomFinset G),
    D.resolvedSplitChoiceTerm (⟨q.1, q.2⟩ : ResolvedCoassocSplitChoice D G)
      = (D.supply G).leftTerm (toFun G q hq).1 ⊗ₜ[ℚ]
          ((D.supply ((toFun G q hq).1.1.contractWithStars (D.starOf G (toFun G q hq).1.1))).leftTerm
              (toFun G q hq).2
            ⊗ₜ[ℚ] (D.supply ((toFun G q hq).1.1.contractWithStars (D.starOf G (toFun G q hq).1.1))).rightTerm
              (toFun G q hq).2)
  /-- Every carrier forest is a proper forest (body-96; gives `outer_nonempty`). -/
  carrier_isProperForest : ∀ (G : ResolvedFeynmanGraph) (A : ResolvedAdmissibleSubgraph G),
    A ∈ D.carrier G → A.IsProperForest
  /-- A representative graph for each generator. -/
  rep : ResolvedHopfGen → ResolvedFeynmanGraph
  /-- The representative is connected-divergent. -/
  repCD : ∀ x : ResolvedHopfGen, (rep x).forget.toClass.IsConnectedDivergent
  /-- The representative's generator IS `x`. -/
  rep_gen : ∀ x : ResolvedHopfGen, x = (rep x).toResolvedHopfGen (repCD x)

/-- **R-6c-body-97 — body-96's proper-forest supply from the bijection.**  Flatten both double sums
(`Finset.sum_sigma'`) and apply `Finset.sum_bij'` with the fielded outer-mixing data. -/
def ResolvedForestBlockBijectionSupply.toForestCarrierProperSupply
    (S : ResolvedForestBlockBijectionSupply D) : ResolvedForestCarrierProperSupply D where
  forest_block := fun G => by
    rw [show (∑ A ∈ (D.supply G).forestCarrier,
          ∑ p ∈ forestChoiceCarrier A,
            D.resolvedSplitChoiceTerm (⟨A, p⟩ : ResolvedCoassocSplitChoice D G))
        = ∑ q ∈ forestBlockDomFinset (D := D) G,
            D.resolvedSplitChoiceTerm (⟨q.1, q.2⟩ : ResolvedCoassocSplitChoice D G) from by
        rw [forestBlockDomFinset, Finset.sum_sigma']; rfl]
    rw [show (∑ A ∈ (D.supply G).forestCarrier,
          ∑ B ∈ (D.supply (A.1.contractWithStars (D.starOf G A.1))).forestCarrier,
            (D.supply G).leftTerm A ⊗ₜ[ℚ]
              ((D.supply (A.1.contractWithStars (D.starOf G A.1))).leftTerm B
                ⊗ₜ[ℚ] (D.supply (A.1.contractWithStars (D.starOf G A.1))).rightTerm B))
        = ∑ r ∈ forestBlockCodFinset (D := D) G,
            (D.supply G).leftTerm r.1 ⊗ₜ[ℚ]
              ((D.supply (r.1.1.contractWithStars (D.starOf G r.1.1))).leftTerm r.2
                ⊗ₜ[ℚ] (D.supply (r.1.1.contractWithStars (D.starOf G r.1.1))).rightTerm r.2) from by
        rw [forestBlockCodFinset, Finset.sum_sigma']; rfl]
    exact Finset.sum_bij' (S.toFun G) (S.invFun G) (S.toFun_mem G) (S.invFun_mem G)
      (S.left_inv G) (S.right_inv G) (S.summand_agree G)
  carrier_isProperForest := S.carrier_isProperForest
  rep := S.rep
  repCD := S.repCD
  rep_gen := S.rep_gen

/-- **R-6c-body-97 — `coassoc_gen` from the forest-block bijection** (via body-96/95/94/93/92/91/90/88). -/
theorem ResolvedForestBlockBijectionSupply.coassoc_gen
    (S : ResolvedForestBlockBijectionSupply D) (x : ResolvedHopfGen) :
    D.coassocLeft (MvPolynomial.X x) = D.coassocRight (MvPolynomial.X x) :=
  S.toForestCarrierProperSupply.coassoc_gen x

end GaugeGeometry.QFT.Combinatorial
