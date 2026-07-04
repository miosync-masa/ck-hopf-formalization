import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestCarryingBlock

/-!
# R-6c-body-101 — forest-block map combiner: both classes in one flat supply (nothing deferred)

Hundred-and-first genuine-body step, compressing the raid boss to its final logical form: a single flat supply
`ResolvedForestBlockMapData` carrying BOTH outer-mixing maps (mixed body-99, forest body-100) with their
`Finset.sum_bij'` data and geometric identities, proving BOTH class equalities and assembling body-98's
`ResolvedForestBlockClassSupply` with NOTHING deferred.

## Why a flat combiner (not a bundle of the two supplies)

Body-99's `ResolvedMixedBoundaryMapSupply` carries `forest_class_block` as a field, and body-100's
`ResolvedForestCarryingMapSupply` carries `mixed_class_block` — each expects the OTHER class as input.  Bundling
them is circular.  The fix is a FLAT record holding the raw map fields of both classes (plus the shared
`isForestImage` / `carrier_isProperForest` / representative lift), from which both class equalities are proved
directly (each is the `Finset.sum_sigma'` + `Finset.sum_bij'` + `resolved_splitChoice_summand_agree_of_factor_eqs`
argument of body-99/100, inlined here with no cross-dependency).

## The final primitive list

After this combiner the ENTIRE remaining coassoc content is exactly:

* the mixed map: `mixedToFun` / `mixedInvFun` / two `maps_to` / two inverse laws + three geometric identities
  (`∏ leftFactor = leftTerm A`, `∏ rightFactor = leftTerm B`, `rightTerm A' = rightTerm B`);
* the forest map: `forestToFun` / `forestInvFun` / two `maps_to` / two inverse laws + three geometric identities;
* `isForestImage` (the codomain classification) and `carrier_isProperForest` (body-96, canonical-provable).

All tensor algebra is proved; every remaining obligation is the FullQuotient outer-mixing geometry.

## The reduction

`.toForestBlockClassSupply` proves `mixed_class_block` and `forest_class_block` inline and assembles body-98's
supply; `.coassoc_gen` chains body-98/96/95/94/93/92/91/90/88.

Per the HALT: no new geometry proof; no circular `extends`; a single flat combined supply; the two block
equalities are proved from the raw map fields; no star/retarget detail.

Landed:

* `ResolvedForestBlockMapData D` — both outer-mixing maps + geometric identities + shared data;
* `.toForestBlockClassSupply` / `.coassoc_gen` — to body-98/96/95/94/93/92/91/90/88.

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

/-- **R-6c-body-101 — the combined forest-block map data.**  BOTH outer-mixing maps (mixed + forest), each with
its `Finset.sum_bij'` data and three geometric identities, plus the shared `isForestImage`,
`carrier_isProperForest`, and representative lift.  The final flat primitive package for `forest_block`. -/
structure ResolvedForestBlockMapData (D : ResolvedCoproductProperForestData) where
  /-- The codomain classification: which quotient forests `B` are forest-images. -/
  isForestImage : ∀ {G : ResolvedFeynmanGraph} (A : {A : ResolvedAdmissibleSubgraph G // A ∈ D.carrier G}),
    (D.supply (A.1.contractWithStars (D.starOf G A.1))).ForestIdx → Prop
  -- MIXED map
  /-- The mixed-boundary map `(A', p) ↦ (A, B)`. -/
  mixedToFun : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G),
    q ∈ mixedDomFinset G → ForestBlockCodType D G
  /-- The mixed inverse. -/
  mixedInvFun : ∀ (G : ResolvedFeynmanGraph) (r : ForestBlockCodType D G),
    r ∈ mixedCodFinset (D := D) (fun {G} A B => isForestImage A B) G → ForestBlockDomType D G
  /-- `mixedToFun` lands in the mixed codomain. -/
  mixedToFun_mem : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G) (hq : q ∈ mixedDomFinset G),
    mixedToFun G q hq ∈ mixedCodFinset (D := D) (fun {G} A B => isForestImage A B) G
  /-- `mixedInvFun` lands in the mixed domain. -/
  mixedInvFun_mem : ∀ (G : ResolvedFeynmanGraph) (r : ForestBlockCodType D G)
    (hr : r ∈ mixedCodFinset (D := D) (fun {G} A B => isForestImage A B) G),
    mixedInvFun G r hr ∈ mixedDomFinset G
  /-- `mixedInvFun ∘ mixedToFun = id`. -/
  mixedLeft_inv : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G) (hq : q ∈ mixedDomFinset G),
    mixedInvFun G (mixedToFun G q hq) (mixedToFun_mem G q hq) = q
  /-- `mixedToFun ∘ mixedInvFun = id`. -/
  mixedRight_inv : ∀ (G : ResolvedFeynmanGraph) (r : ForestBlockCodType D G)
    (hr : r ∈ mixedCodFinset (D := D) (fun {G} A B => isForestImage A B) G),
    mixedToFun G (mixedInvFun G r hr) (mixedInvFun_mem G r hr) = r
  /-- Mixed geometric identity: left-factor product = target outer's left term. -/
  mixed_left_eq : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G) (hq : q ∈ mixedDomFinset G),
    (∏ γ ∈ (q.1.1.elements.attach).attach,
        localLeftFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2))
      = (D.supply G).leftTerm (mixedToFun G q hq).1
  /-- Mixed geometric identity: right-factor product = quotient forest's left term. -/
  mixed_right_eq : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G) (hq : q ∈ mixedDomFinset G),
    (∏ γ ∈ (q.1.1.elements.attach).attach,
        localRightFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2))
      = (D.supply ((mixedToFun G q hq).1.1.contractWithStars (D.starOf G (mixedToFun G q hq).1.1))).leftTerm
          (mixedToFun G q hq).2
  /-- Mixed geometric identity: source quotient right term = quotient forest's right term. -/
  mixed_quot_eq : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G) (hq : q ∈ mixedDomFinset G),
    (D.supply G).rightTerm q.1
      = (D.supply ((mixedToFun G q hq).1.1.contractWithStars (D.starOf G (mixedToFun G q hq).1.1))).rightTerm
          (mixedToFun G q hq).2
  -- FOREST map
  /-- The forest-carrying map `(A', p) ↦ (A, B)`. -/
  forestToFun : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G),
    q ∈ forestCarryingDomFinset G → ForestBlockCodType D G
  /-- The forest inverse. -/
  forestInvFun : ∀ (G : ResolvedFeynmanGraph) (r : ForestBlockCodType D G),
    r ∈ forestCarryingCodFinset (D := D) (fun {G} A B => isForestImage A B) G → ForestBlockDomType D G
  /-- `forestToFun` lands in the forest-image codomain. -/
  forestToFun_mem : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G)
    (hq : q ∈ forestCarryingDomFinset G),
    forestToFun G q hq ∈ forestCarryingCodFinset (D := D) (fun {G} A B => isForestImage A B) G
  /-- `forestInvFun` lands in the forest-carrying domain. -/
  forestInvFun_mem : ∀ (G : ResolvedFeynmanGraph) (r : ForestBlockCodType D G)
    (hr : r ∈ forestCarryingCodFinset (D := D) (fun {G} A B => isForestImage A B) G),
    forestInvFun G r hr ∈ forestCarryingDomFinset G
  /-- `forestInvFun ∘ forestToFun = id`. -/
  forestLeft_inv : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G)
    (hq : q ∈ forestCarryingDomFinset G),
    forestInvFun G (forestToFun G q hq) (forestToFun_mem G q hq) = q
  /-- `forestToFun ∘ forestInvFun = id`. -/
  forestRight_inv : ∀ (G : ResolvedFeynmanGraph) (r : ForestBlockCodType D G)
    (hr : r ∈ forestCarryingCodFinset (D := D) (fun {G} A B => isForestImage A B) G),
    forestToFun G (forestInvFun G r hr) (forestInvFun_mem G r hr) = r
  /-- Forest geometric identity: left-factor product = target outer's left term. -/
  forest_left_eq : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G)
    (hq : q ∈ forestCarryingDomFinset G),
    (∏ γ ∈ (q.1.1.elements.attach).attach,
        localLeftFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2))
      = (D.supply G).leftTerm (forestToFun G q hq).1
  /-- Forest geometric identity: right-factor product = quotient forest's left term. -/
  forest_right_eq : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G)
    (hq : q ∈ forestCarryingDomFinset G),
    (∏ γ ∈ (q.1.1.elements.attach).attach,
        localRightFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2))
      = (D.supply ((forestToFun G q hq).1.1.contractWithStars (D.starOf G (forestToFun G q hq).1.1))).leftTerm
          (forestToFun G q hq).2
  /-- Forest geometric identity: source quotient right term = quotient forest's right term. -/
  forest_quotient_eq : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G)
    (hq : q ∈ forestCarryingDomFinset G),
    (D.supply G).rightTerm q.1
      = (D.supply ((forestToFun G q hq).1.1.contractWithStars (D.starOf G (forestToFun G q hq).1.1))).rightTerm
          (forestToFun G q hq).2
  -- shared
  /-- Every carrier forest is a proper forest (body-96; gives `outer_nonempty`). -/
  carrier_isProperForest : ∀ (G : ResolvedFeynmanGraph) (A : ResolvedAdmissibleSubgraph G),
    A ∈ D.carrier G → A.IsProperForest
  /-- A representative graph for each generator. -/
  rep : ResolvedHopfGen → ResolvedFeynmanGraph
  /-- The representative is connected-divergent. -/
  repCD : ∀ x : ResolvedHopfGen, (rep x).forget.toClass.IsConnectedDivergent
  /-- The representative's generator IS `x`. -/
  rep_gen : ∀ x : ResolvedHopfGen, x = (rep x).toResolvedHopfGen (repCD x)

/-- **R-6c-body-101 — body-98's class supply from the combined map data** (BOTH class equalities proved). -/
def ResolvedForestBlockMapData.toForestBlockClassSupply
    (S : ResolvedForestBlockMapData D) : ResolvedForestBlockClassSupply D where
  isForestImage := fun {G} A B => S.isForestImage A B
  forest_class_block := fun G => by
    rw [show (∑ A ∈ (D.supply G).forestCarrier,
          ∑ p ∈ (forestChoiceCarrier A).filter (fun p => isForestCarryingChoice A p),
            D.resolvedSplitChoiceTerm (⟨A, p⟩ : ResolvedCoassocSplitChoice D G))
        = ∑ q ∈ forestCarryingDomFinset (D := D) G,
            D.resolvedSplitChoiceTerm (⟨q.1, q.2⟩ : ResolvedCoassocSplitChoice D G) from by
        rw [forestCarryingDomFinset, Finset.sum_sigma']; rfl]
    rw [show (∑ A ∈ (D.supply G).forestCarrier,
          ∑ B ∈ ((D.supply (A.1.contractWithStars (D.starOf G A.1))).forestCarrier).filter
              (fun B => S.isForestImage A B),
            (D.supply G).leftTerm A ⊗ₜ[ℚ]
              ((D.supply (A.1.contractWithStars (D.starOf G A.1))).leftTerm B
                ⊗ₜ[ℚ] (D.supply (A.1.contractWithStars (D.starOf G A.1))).rightTerm B))
        = ∑ r ∈ forestCarryingCodFinset (D := D) (fun {G} A B => S.isForestImage A B) G,
            (D.supply G).leftTerm r.1 ⊗ₜ[ℚ]
              ((D.supply (r.1.1.contractWithStars (D.starOf G r.1.1))).leftTerm r.2
                ⊗ₜ[ℚ] (D.supply (r.1.1.contractWithStars (D.starOf G r.1.1))).rightTerm r.2) from by
        rw [forestCarryingCodFinset, Finset.sum_sigma']; rfl]
    exact Finset.sum_bij' (S.forestToFun G) (S.forestInvFun G) (S.forestToFun_mem G) (S.forestInvFun_mem G)
      (S.forestLeft_inv G) (S.forestRight_inv G)
      (fun q hq => resolved_splitChoice_summand_agree_of_factor_eqs q.1 q.2 (S.forestToFun G q hq).1
        (S.forestToFun G q hq).2 (S.forest_left_eq G q hq) (S.forest_right_eq G q hq)
        (S.forest_quotient_eq G q hq))
  mixed_class_block := fun G => by
    rw [show (∑ A ∈ (D.supply G).forestCarrier,
          ∑ p ∈ (forestChoiceCarrier A).filter (fun p => ¬ isForestCarryingChoice A p),
            D.resolvedSplitChoiceTerm (⟨A, p⟩ : ResolvedCoassocSplitChoice D G))
        = ∑ q ∈ mixedDomFinset (D := D) G,
            D.resolvedSplitChoiceTerm (⟨q.1, q.2⟩ : ResolvedCoassocSplitChoice D G) from by
        rw [mixedDomFinset, Finset.sum_sigma']; rfl]
    rw [show (∑ A ∈ (D.supply G).forestCarrier,
          ∑ B ∈ ((D.supply (A.1.contractWithStars (D.starOf G A.1))).forestCarrier).filter
              (fun B => ¬ S.isForestImage A B),
            (D.supply G).leftTerm A ⊗ₜ[ℚ]
              ((D.supply (A.1.contractWithStars (D.starOf G A.1))).leftTerm B
                ⊗ₜ[ℚ] (D.supply (A.1.contractWithStars (D.starOf G A.1))).rightTerm B))
        = ∑ r ∈ mixedCodFinset (D := D) (fun {G} A B => S.isForestImage A B) G,
            (D.supply G).leftTerm r.1 ⊗ₜ[ℚ]
              ((D.supply (r.1.1.contractWithStars (D.starOf G r.1.1))).leftTerm r.2
                ⊗ₜ[ℚ] (D.supply (r.1.1.contractWithStars (D.starOf G r.1.1))).rightTerm r.2) from by
        rw [mixedCodFinset, Finset.sum_sigma']; rfl]
    exact Finset.sum_bij' (S.mixedToFun G) (S.mixedInvFun G) (S.mixedToFun_mem G) (S.mixedInvFun_mem G)
      (S.mixedLeft_inv G) (S.mixedRight_inv G)
      (fun q hq => resolved_splitChoice_summand_agree_of_factor_eqs q.1 q.2 (S.mixedToFun G q hq).1
        (S.mixedToFun G q hq).2 (S.mixed_left_eq G q hq) (S.mixed_right_eq G q hq)
        (S.mixed_quot_eq G q hq))
  carrier_isProperForest := S.carrier_isProperForest
  rep := S.rep
  repCD := S.repCD
  rep_gen := S.rep_gen

/-- **R-6c-body-101 — `coassoc_gen` from the combined map data** (via body-98/96/95/94/93/92/91/90/88). -/
theorem ResolvedForestBlockMapData.coassoc_gen
    (S : ResolvedForestBlockMapData D) (x : ResolvedHopfGen) :
    D.coassocLeft (MvPolynomial.X x) = D.coassocRight (MvPolynomial.X x) :=
  S.toForestBlockClassSupply.coassoc_gen x

end GaugeGeometry.QFT.Combinatorial
