import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocNestedMatchingProof

/-!
# R-6c-body-94 — forest_core index classification: the forest block is exactly `piCarrier \ {p_R, p_L}`

Ninety-fourth genuine-body step, the index anatomy of `forest_core` (body-93's single boundary-free leaf).  The
right-hand full component-choice sum `∑_A ∑_{p ∈ piCarrier A} splitTerm ⟨A, p⟩` is partitioned into the two pure
primitives (`p_R = all-right`, `p_L = all-left`, already matched by body-65/93) plus the FOREST-CARRYING block
`piCarrier A \ {p_R, p_L}`, and that block is fielded as the genuine nested-forest bijection onto the quotient
forests `B`.

## The classification (the key question, answered)

The forest block's domain is EXACTLY `piCarrier A \ {p_R, p_L}` — the two pure-primitive extremes and nothing
finer.  Every non-extreme choice (whether "mixed boundary": some components left-primitive, some right-primitive,
no forest; or "forest-carrying": at least one component picks an actual sub-forest) lands in the forest block.
This matches the flat `Coassoc` anatomy, where `forestComponentChoiceSigma` (the analogue of `∑_A ∑_p`) is split
into `forestComponentMixedBoundaryChoiceSigmaIndex` (mixed boundary) and `forestComponentForestChoiceSigmaIndex`
(forest choice) — both of which map onto quotient-forest pairs `⟨A, B⟩`
(`forestComponentChoiceSigmaTerm_eq_quotientForestSigmaTerm_of_factorization`, `Coassoc` 27348).  The pure
all-right / all-left are the two boundary extremes, already peeled off in resolved bodies 65/93.

## The flat bijection mixes the outer forest (documented, downstream)

Crucially, the flat `⟨A', p⟩ ↦ ⟨A, B⟩` bijection is NOT outer-preserving: for a mixed-boundary choice, the
LEFT-selected components (`forestComponentChoiceLeftSubgraph`) ENLARGE the outer forest to `A ⊇ A'`, and the
right-selected / forest components form the quotient forest `B` of `A.contractWithStars`.  So `forest_block` is
stated as an equality of DOUBLE sums (`∑_A ∑_{forest choices}` = `∑_A ∑_B`), with the outer-mixing reindex
internal to it — exactly the genuine content deferred to the next body.  (The pure primitives `p_R, p_L` are
outer-preserving, which is why they factor out cleanly first.)

## The scaffold

`forestChoiceCarrier A := piCarrier A |>.filter (· ≠ p_R ∧ · ≠ p_L)` — the forest block's index.
`ResolvedForestCoreClassificationSupply` fields the per-`A` `choice_partition` (`∑_p = p_R + p_L + ∑_{forest
choices}`, the pure-primitive extraction) and the total `forest_block` (`∑_A ∑_{forest choices} = ∑_A ∑_B`, the
genuine bijection with internal outer-mixing).  `.toNestedForestCoreSupply` combines them (via `sum_add_distrib`
+ `sum_congr`) to recover body-93's `forest_core`; `.coassoc_gen` chains body-93/92/91/90/88.

Per the HALT: the forest bijection is NOT proved (it is `forest_block`); the pure primitives are NOT re-proved
(body-65/93); the classification is fixed (`piCarrier \ {p_R, p_L}`, the two extremes); no quotient-forest union
construction, no outer-mixing detail, no star/retarget.

Landed:

* `forestChoiceCarrier` — the forest-block index `piCarrier \ {p_R, p_L}`;
* `ResolvedForestCoreClassificationSupply D` — `choice_partition` + `forest_block` + representative lift;
* `.toNestedForestCoreSupply` / `.coassoc_gen` — to body-93/92/91/90/88.

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

/-- **R-6c-body-94 — the forest-block index.**  The component choices that are neither all-right (`p_R`) nor
all-left (`p_L`) primitive — the domain onto which the quotient forests `B` are matched.  Every non-extreme
choice (mixed-boundary or forest-carrying) lives here. -/
noncomputable def forestChoiceCarrier {G : ResolvedFeynmanGraph}
    (A : {A : ResolvedAdmissibleSubgraph G // A ∈ D.carrier G}) :=
  ((A.1.elements.attach).pi (fun γ => D.localChoiceCarrier (γ.1.toResolvedFeynmanGraph))).filter
    (fun p => p ≠ (fun _ _ => Sum.inl false) ∧ p ≠ (fun _ _ => Sum.inl true))

/-- **R-6c-body-94 — the forest-core classification supply.**  `choice_partition`: the full per-`A`
component-choice sum is the two pure primitives plus the forest block.  `forest_block`: the forest block equals
the quotient-forest double sum (the genuine nested-forest bijection, with internal outer-mixing).  Plus a
representative lift. -/
structure ResolvedForestCoreClassificationSupply (D : ResolvedCoproductProperForestData) where
  /-- The pure-primitive extraction: `∑_p splitTerm = splitTerm p_R + splitTerm p_L + ∑_{forest choices}`. -/
  choice_partition : ∀ (G : ResolvedFeynmanGraph)
      (A : {A : ResolvedAdmissibleSubgraph G // A ∈ D.carrier G}),
      A ∈ (D.supply G).forestCarrier →
      (∑ p ∈ (A.1.elements.attach).pi (fun γ => D.localChoiceCarrier (γ.1.toResolvedFeynmanGraph)),
          D.resolvedSplitChoiceTerm (⟨A, p⟩ : ResolvedCoassocSplitChoice D G))
        = D.resolvedSplitChoiceTerm (⟨A, fun _ _ => Sum.inl false⟩ : ResolvedCoassocSplitChoice D G)
          + D.resolvedSplitChoiceTerm (⟨A, fun _ _ => Sum.inl true⟩ : ResolvedCoassocSplitChoice D G)
          + ∑ p ∈ forestChoiceCarrier A,
              D.resolvedSplitChoiceTerm (⟨A, p⟩ : ResolvedCoassocSplitChoice D G)
  /-- The genuine nested-forest bijection: the forest block = the quotient-forest double sum. -/
  forest_block : ∀ (G : ResolvedFeynmanGraph),
      (∑ A ∈ (D.supply G).forestCarrier,
          ∑ p ∈ forestChoiceCarrier A,
            D.resolvedSplitChoiceTerm (⟨A, p⟩ : ResolvedCoassocSplitChoice D G))
        = ∑ A ∈ (D.supply G).forestCarrier,
            ∑ B ∈ (D.supply (A.1.contractWithStars (D.starOf G A.1))).forestCarrier,
              (D.supply G).leftTerm A ⊗ₜ[ℚ]
                ((D.supply (A.1.contractWithStars (D.starOf G A.1))).leftTerm B
                  ⊗ₜ[ℚ] (D.supply (A.1.contractWithStars (D.starOf G A.1))).rightTerm B)
  /-- A representative graph for each generator. -/
  rep : ResolvedHopfGen → ResolvedFeynmanGraph
  /-- The representative is connected-divergent. -/
  repCD : ∀ x : ResolvedHopfGen, (rep x).forget.toClass.IsConnectedDivergent
  /-- The representative's generator IS `x`. -/
  rep_gen : ∀ x : ResolvedHopfGen, x = (rep x).toResolvedHopfGen (repCD x)

/-- **R-6c-body-94 — body-93's `forest_core` from the classification.**  Combine the pure-primitive extraction
(`choice_partition`) with the forest bijection (`forest_block`). -/
def ResolvedForestCoreClassificationSupply.toNestedForestCoreSupply
    (S : ResolvedForestCoreClassificationSupply D) : ResolvedNestedForestCoreSupply D where
  forest_core := fun G => by
    rw [← S.forest_block G, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun A hA => (S.choice_partition G A hA).symm)
  rep := S.rep
  repCD := S.repCD
  rep_gen := S.rep_gen

/-- **R-6c-body-94 — `coassoc_gen` from the classification** (via body-93/92/91/90/88). -/
theorem ResolvedForestCoreClassificationSupply.coassoc_gen
    (S : ResolvedForestCoreClassificationSupply D) (x : ResolvedHopfGen) :
    D.coassocLeft (MvPolynomial.X x) = D.coassocRight (MvPolynomial.X x) :=
  S.toNestedForestCoreSupply.coassoc_gen x

end GaugeGeometry.QFT.Combinatorial
