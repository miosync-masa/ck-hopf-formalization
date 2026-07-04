import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestBlockBijection

/-!
# R-6c-body-98 — forest_block two-class split: mixed-boundary + forest-carrying (partition is FREE)

Ninety-eighth genuine-body step, splitting the monolithic `forest_block` (body-97) into the two flat classes —
`ForestChoice` (≥ 1 component picks a real sub-forest) and `MixedBoundary` (only left/right primitives) — so that
`toFun`/`invFun`/`summand_agree` can be attacked one class at a time.  The split is a pure `Finset` partition on
both sides, so the ADAPTER is fully proved here; the genuine content is the two per-class sum equalities.

## The domain predicate and the free partition

`isForestCarryingChoice A p := ∃ γ hγ b, p γ hγ = Sum.inr b` — some component of `p` picks an actual forest
index.  Its negation is `MixedBoundary` (every component is a left/right primitive `Sum.inl _`).  The domain
`forestChoiceCarrier A` partitions as `filter isForestCarryingChoice ⊔ filter ¬isForestCarryingChoice` — a FREE
partition (`Finset.sum_filter_add_sum_filter_not`), no membership proof needed.  This is the resolved analogue of
the flat disjoint union `forestComponentForestChoiceSigmaIndex ⊔ forestComponentMixedBoundaryChoiceSigmaIndex`.

## The codomain classification (fielded)

The codomain (`Σ A, quotient forests B`) splits by a fielded predicate `isForestImage A B` — which quotient
forests are hit by the forest-carrying class vs the mixed-boundary class.  Any predicate works for the ADAPTER
(the content is entirely in the two per-class equalities matching it); the natural choice tracks whether `B`
arises from promoted components (forest-carrying) or from right-selected primitive components (mixed).

## The two class equalities (the genuine content, now separately attackable)

* `forest_class_block`: `∑_A ∑_{p : isForestCarrying} splitTerm ⟨A, p⟩ = ∑_A ∑_{B : isForestImage} leftTerm A ⊗
  (leftTerm B ⊗ rightTerm B)` — the forest-carrying bijection (flat
  `forestComponentForestChoiceToQuotientForestSigma`);
* `mixed_class_block`: the same with `¬isForestCarrying` / `¬isForestImage` — the mixed-boundary bijection (flat
  `forestComponentMixedBoundaryToQuotientForestSigma`).

## The reduction (PROVED)

`.toForestCarrierProperSupply` proves body-96's `forest_block` by partitioning BOTH sides
(`Finset.sum_filter_add_sum_filter_not` per `A`, `Finset.sum_add_distrib`) and applying the two class
equalities.  `.coassoc_gen` chains body-96/95/94/93/92/91/90/88.  (This bypasses body-97's monolithic
`sum_bij'` phrasing — body-97 remains a valid single-bijection alternative.)

Per the HALT: the partition IS proved (free); the two class equalities are NOT proved (they are the fields);
`isForestImage` is fielded; no per-class map, no star/retarget.

Landed:

* `isForestCarryingChoice` — the domain class predicate (`MixedBoundary = ¬` this);
* `ResolvedForestBlockClassSupply D` — `isForestImage` + the two class equalities + `carrier_isProperForest` +
  representative lift;
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

/-- **R-6c-body-98 — the domain class predicate.**  A component choice is *forest-carrying* when some component
picks an actual forest index (`Sum.inr`).  Its negation is the *mixed-boundary* class (every component a
left/right primitive `Sum.inl _`). -/
def isForestCarryingChoice {G : ResolvedFeynmanGraph}
    (A : {A : ResolvedAdmissibleSubgraph G // A ∈ D.carrier G})
    (p : ∀ γ ∈ A.1.elements.attach, Bool ⊕ (D.supply (γ.1.toResolvedFeynmanGraph)).ForestIdx) : Prop :=
  ∃ γ, ∃ (hγ : γ ∈ A.1.elements.attach), ∃ b, p γ hγ = Sum.inr b

/-- **R-6c-body-98 — the forest-block class supply.**  A codomain classification `isForestImage` plus the two
per-class sum equalities (forest-carrying and mixed-boundary), with `carrier_isProperForest` (body-96) and a
representative lift.  The domain partition is free; the content is the two class equalities. -/
structure ResolvedForestBlockClassSupply (D : ResolvedCoproductProperForestData) where
  /-- Which quotient forests `B` are hit by the forest-carrying class (fielded classification). -/
  isForestImage : ∀ {G : ResolvedFeynmanGraph} (A : {A : ResolvedAdmissibleSubgraph G // A ∈ D.carrier G}),
    (D.supply (A.1.contractWithStars (D.starOf G A.1))).ForestIdx → Prop
  /-- The FOREST-CARRYING bijection: forest-carrying choices ↔ forest-image quotient forests. -/
  forest_class_block : ∀ (G : ResolvedFeynmanGraph),
      (∑ A ∈ (D.supply G).forestCarrier,
          ∑ p ∈ (forestChoiceCarrier A).filter (fun p => isForestCarryingChoice A p),
            D.resolvedSplitChoiceTerm (⟨A, p⟩ : ResolvedCoassocSplitChoice D G))
        = ∑ A ∈ (D.supply G).forestCarrier,
            ∑ B ∈ ((D.supply (A.1.contractWithStars (D.starOf G A.1))).forestCarrier).filter
                (fun B => isForestImage A B),
              (D.supply G).leftTerm A ⊗ₜ[ℚ]
                ((D.supply (A.1.contractWithStars (D.starOf G A.1))).leftTerm B
                  ⊗ₜ[ℚ] (D.supply (A.1.contractWithStars (D.starOf G A.1))).rightTerm B)
  /-- The MIXED-BOUNDARY bijection: mixed-boundary choices ↔ non-forest-image quotient forests. -/
  mixed_class_block : ∀ (G : ResolvedFeynmanGraph),
      (∑ A ∈ (D.supply G).forestCarrier,
          ∑ p ∈ (forestChoiceCarrier A).filter (fun p => ¬ isForestCarryingChoice A p),
            D.resolvedSplitChoiceTerm (⟨A, p⟩ : ResolvedCoassocSplitChoice D G))
        = ∑ A ∈ (D.supply G).forestCarrier,
            ∑ B ∈ ((D.supply (A.1.contractWithStars (D.starOf G A.1))).forestCarrier).filter
                (fun B => ¬ isForestImage A B),
              (D.supply G).leftTerm A ⊗ₜ[ℚ]
                ((D.supply (A.1.contractWithStars (D.starOf G A.1))).leftTerm B
                  ⊗ₜ[ℚ] (D.supply (A.1.contractWithStars (D.starOf G A.1))).rightTerm B)
  /-- Every carrier forest is a proper forest (body-96; gives `outer_nonempty`). -/
  carrier_isProperForest : ∀ (G : ResolvedFeynmanGraph) (A : ResolvedAdmissibleSubgraph G),
    A ∈ D.carrier G → A.IsProperForest
  /-- A representative graph for each generator. -/
  rep : ResolvedHopfGen → ResolvedFeynmanGraph
  /-- The representative is connected-divergent. -/
  repCD : ∀ x : ResolvedHopfGen, (rep x).forget.toClass.IsConnectedDivergent
  /-- The representative's generator IS `x`. -/
  rep_gen : ∀ x : ResolvedHopfGen, x = (rep x).toResolvedHopfGen (repCD x)

/-- **R-6c-body-98 — body-96's proper-forest supply from the two-class split.**  Partition both sides of
`forest_block` by the class predicate and apply the two class equalities. -/
def ResolvedForestBlockClassSupply.toForestCarrierProperSupply
    (S : ResolvedForestBlockClassSupply D) : ResolvedForestCarrierProperSupply D where
  forest_block := fun G => by
    have hL : (∑ A ∈ (D.supply G).forestCarrier,
          ∑ p ∈ forestChoiceCarrier A, D.resolvedSplitChoiceTerm (⟨A, p⟩ : ResolvedCoassocSplitChoice D G))
        = (∑ A ∈ (D.supply G).forestCarrier,
            ∑ p ∈ (forestChoiceCarrier A).filter (fun p => isForestCarryingChoice A p),
              D.resolvedSplitChoiceTerm (⟨A, p⟩ : ResolvedCoassocSplitChoice D G))
          + (∑ A ∈ (D.supply G).forestCarrier,
            ∑ p ∈ (forestChoiceCarrier A).filter (fun p => ¬ isForestCarryingChoice A p),
              D.resolvedSplitChoiceTerm (⟨A, p⟩ : ResolvedCoassocSplitChoice D G)) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun A _ =>
        (Finset.sum_filter_add_sum_filter_not (forestChoiceCarrier A) _ _).symm)
    have hR : (∑ A ∈ (D.supply G).forestCarrier,
          ∑ B ∈ (D.supply (A.1.contractWithStars (D.starOf G A.1))).forestCarrier,
            (D.supply G).leftTerm A ⊗ₜ[ℚ]
              ((D.supply (A.1.contractWithStars (D.starOf G A.1))).leftTerm B
                ⊗ₜ[ℚ] (D.supply (A.1.contractWithStars (D.starOf G A.1))).rightTerm B))
        = (∑ A ∈ (D.supply G).forestCarrier,
            ∑ B ∈ ((D.supply (A.1.contractWithStars (D.starOf G A.1))).forestCarrier).filter
                (fun B => S.isForestImage A B),
              (D.supply G).leftTerm A ⊗ₜ[ℚ]
                ((D.supply (A.1.contractWithStars (D.starOf G A.1))).leftTerm B
                  ⊗ₜ[ℚ] (D.supply (A.1.contractWithStars (D.starOf G A.1))).rightTerm B))
          + (∑ A ∈ (D.supply G).forestCarrier,
            ∑ B ∈ ((D.supply (A.1.contractWithStars (D.starOf G A.1))).forestCarrier).filter
                (fun B => ¬ S.isForestImage A B),
              (D.supply G).leftTerm A ⊗ₜ[ℚ]
                ((D.supply (A.1.contractWithStars (D.starOf G A.1))).leftTerm B
                  ⊗ₜ[ℚ] (D.supply (A.1.contractWithStars (D.starOf G A.1))).rightTerm B)) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun A _ =>
        (Finset.sum_filter_add_sum_filter_not _ _ _).symm)
    rw [hL, hR, S.forest_class_block, S.mixed_class_block]
  carrier_isProperForest := S.carrier_isProperForest
  rep := S.rep
  repCD := S.repCD
  rep_gen := S.rep_gen

/-- **R-6c-body-98 — `coassoc_gen` from the two-class split** (via body-96/95/94/93/92/91/90/88). -/
theorem ResolvedForestBlockClassSupply.coassoc_gen
    (S : ResolvedForestBlockClassSupply D) (x : ResolvedHopfGen) :
    D.coassocLeft (MvPolynomial.X x) = D.coassocRight (MvPolynomial.X x) :=
  S.toForestCarrierProperSupply.coassoc_gen x

end GaugeGeometry.QFT.Combinatorial
