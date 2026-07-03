import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestCoreIndex

/-!
# R-6c-body-95 — pure-primitive choice partition: `choice_partition` PROVED, only `forest_block` remains

Ninety-fifth genuine-body step, discharging body-94's mechanical `choice_partition` — the pure-primitive
extraction `∑_{p ∈ piCarrier A} f p = f p_R + f p_L + ∑_{p ∈ forestChoiceCarrier A} f p`.  This peels the last
non-genuine obligation off the forest core; the sole remaining coassoc leaf is now `forest_block` (the
nested-forest bijection with outer-mixing).

## The proof

`sum_extract_two` — a generic `Finset` lemma: for distinct `a, b ∈ s`, `∑_s f = f a + f b + ∑_{s.filter (· ≠ a
∧ · ≠ b)} f` (two `Finset.add_sum_erase` + `(s.erase a).erase b = s.filter (· ≠ a ∧ · ≠ b)`).  Applied with
`a = p_R = fun _ _ => Sum.inl false`, `b = p_L = fun _ _ => Sum.inl true`, `f p = splitTerm ⟨A, p⟩`, it IS
`choice_partition` (the filter is exactly `forestChoiceCarrier A`).  The three side conditions:

* `p_R ∈ piCarrier A` / `p_L ∈ piCarrier A` — `Finset.mem_pi` + `Finset.inl_mem_disjSum` (`Sum.inl _` is always
  in `(univ : Finset Bool).disjSum forestCarrier = localChoiceCarrier`);
* `p_R ≠ p_L` — from `A.elements.Nonempty`: pick a component `γ`, apply both functions at `γ`, get `Sum.inl
  false = Sum.inl true`, contradiction.

## The nonemptiness obligation

`p_R ≠ p_L` needs `A.elements.Nonempty` (≥ 1 component).  As body-1 (`ResolvedConnectedDivergentNonemptySupply`)
established, even vertex-nonemptiness of a connected-divergent subgraph is NOT derivable from the abstract
`DivergenceMeasure` — so element-nonemptiness of a carrier forest is fielded here as `outer_nonempty` (the same
measure-level flavour; wireable from `cd_nonempty` at the call site).

## The scaffold

`ResolvedForestBlockSupply` bundles `outer_nonempty` + the genuine `forest_block` + a representative lift, and
`.toForestCoreClassificationSupply` discharges `choice_partition` via `pure_choice_partition`, recovering
body-94's classification supply; `.coassoc_gen` chains body-94/93/92/91/90/88.

Per the HALT: `choice_partition` IS proved; `forest_block` is NOT (it is the field); `outer_nonempty` is fielded
(measure-level, per body-1); no forest bijection, no outer-mixing, no star/retarget.

Landed:

* `sum_extract_two` — the generic two-element `Finset` sum extraction (PROVED);
* `resolved_allRight_mem_piCarrier` / `resolved_allLeft_mem_piCarrier` / `resolved_allRight_ne_allLeft` — the
  three side conditions (PROVED);
* `pure_choice_partition` — body-94's `choice_partition` at one `A` (PROVED, from `A.elements.Nonempty`);
* `ResolvedForestBlockSupply D` — `outer_nonempty` + `forest_block` + representative lift;
* `.toForestCoreClassificationSupply` / `.coassoc_gen` — to body-94/93/92/91/90/88.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

/-- **R-6c-body-95 — generic two-element extraction.**  For distinct `a, b ∈ s`, the sum splits off `f a` and
`f b` from the `(· ≠ a ∧ · ≠ b)`-filtered remainder. -/
theorem sum_extract_two {M : Type*} [AddCommMonoid M] {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → M) {a b : α} (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) :
    ∑ x ∈ s, f x = f a + f b + ∑ x ∈ s.filter (fun x => x ≠ a ∧ x ≠ b), f x := by
  have hset : (s.erase a).erase b = s.filter (fun x => x ≠ a ∧ x ≠ b) := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_filter]
    tauto
  rw [← Finset.add_sum_erase s f ha,
    ← Finset.add_sum_erase (s.erase a) f (Finset.mem_erase.mpr ⟨hab.symm, hb⟩),
    ← add_assoc, hset]

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

set_option linter.unusedSectionVars false

/-- **R-6c-body-95 — `p_R` is a valid component choice.**  The all-right primitive choice is in `piCarrier A`. -/
theorem resolved_allRight_mem_piCarrier
    (A : {A : ResolvedAdmissibleSubgraph G // A ∈ D.carrier G}) :
    (fun _ _ => Sum.inl false : (γ : {x // x ∈ A.1.elements}) → γ ∈ A.1.elements.attach →
        Bool ⊕ (D.supply (γ.1.toResolvedFeynmanGraph)).ForestIdx)
      ∈ (A.1.elements.attach).pi (fun γ => D.localChoiceCarrier (γ.1.toResolvedFeynmanGraph)) := by
  rw [Finset.mem_pi]
  exact fun γ hγ => Finset.inl_mem_disjSum.mpr (Finset.mem_univ false)

/-- **R-6c-body-95 — `p_L` is a valid component choice.**  The all-left primitive choice is in `piCarrier A`. -/
theorem resolved_allLeft_mem_piCarrier
    (A : {A : ResolvedAdmissibleSubgraph G // A ∈ D.carrier G}) :
    (fun _ _ => Sum.inl true : (γ : {x // x ∈ A.1.elements}) → γ ∈ A.1.elements.attach →
        Bool ⊕ (D.supply (γ.1.toResolvedFeynmanGraph)).ForestIdx)
      ∈ (A.1.elements.attach).pi (fun γ => D.localChoiceCarrier (γ.1.toResolvedFeynmanGraph)) := by
  rw [Finset.mem_pi]
  exact fun γ hγ => Finset.inl_mem_disjSum.mpr (Finset.mem_univ true)

/-- **R-6c-body-95 — the two pure primitives are distinct** (given a component).  From `A.elements.Nonempty`. -/
theorem resolved_allRight_ne_allLeft
    (A : {A : ResolvedAdmissibleSubgraph G // A ∈ D.carrier G})
    (hne : A.1.elements.Nonempty) :
    (fun _ _ => Sum.inl false : (γ : {x // x ∈ A.1.elements}) → γ ∈ A.1.elements.attach →
        Bool ⊕ (D.supply (γ.1.toResolvedFeynmanGraph)).ForestIdx)
      ≠ (fun _ _ => Sum.inl true) := by
  obtain ⟨v, hv⟩ := hne
  intro h
  have hfalse := congrFun (congrFun h ⟨v, hv⟩) (Finset.mem_attach _ _)
  simp only [Sum.inl.injEq] at hfalse
  exact absurd hfalse Bool.false_ne_true

/-- **R-6c-body-95 — the pure-primitive choice partition** (body-94's `choice_partition` at one `A`).  The full
component-choice sum is the two pure primitives plus the forest block, given `A` has a component. -/
theorem pure_choice_partition
    (A : {A : ResolvedAdmissibleSubgraph G // A ∈ D.carrier G})
    (hne : A.1.elements.Nonempty) :
    (∑ p ∈ (A.1.elements.attach).pi (fun γ => D.localChoiceCarrier (γ.1.toResolvedFeynmanGraph)),
        D.resolvedSplitChoiceTerm (⟨A, p⟩ : ResolvedCoassocSplitChoice D G))
      = D.resolvedSplitChoiceTerm (⟨A, fun _ _ => Sum.inl false⟩ : ResolvedCoassocSplitChoice D G)
        + D.resolvedSplitChoiceTerm (⟨A, fun _ _ => Sum.inl true⟩ : ResolvedCoassocSplitChoice D G)
        + ∑ p ∈ forestChoiceCarrier A,
            D.resolvedSplitChoiceTerm (⟨A, p⟩ : ResolvedCoassocSplitChoice D G) :=
  sum_extract_two _ (fun p => D.resolvedSplitChoiceTerm (⟨A, p⟩ : ResolvedCoassocSplitChoice D G))
    (resolved_allRight_mem_piCarrier A) (resolved_allLeft_mem_piCarrier A)
    (resolved_allRight_ne_allLeft A hne)

/-- **R-6c-body-95 — the forest-block-only supply.**  `outer_nonempty` (each carrier forest has a component,
fielded per body-1) + the genuine `forest_block` (the nested-forest bijection) + a representative lift.  The
`choice_partition` is now PROVED, so this is strictly less than body-94's supply. -/
structure ResolvedForestBlockSupply (D : ResolvedCoproductProperForestData) where
  /-- Every carrier forest has at least one component (fielded, measure-level per body-1). -/
  outer_nonempty : ∀ (G : ResolvedFeynmanGraph)
    (A : {A : ResolvedAdmissibleSubgraph G // A ∈ D.carrier G}),
    A ∈ (D.supply G).forestCarrier → A.1.elements.Nonempty
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

/-- **R-6c-body-95 — body-94's classification supply from the forest block** (with `choice_partition` proved). -/
def ResolvedForestBlockSupply.toForestCoreClassificationSupply
    (S : ResolvedForestBlockSupply D) : ResolvedForestCoreClassificationSupply D where
  choice_partition := fun G A hA => pure_choice_partition A (S.outer_nonempty G A hA)
  forest_block := S.forest_block
  rep := S.rep
  repCD := S.repCD
  rep_gen := S.rep_gen

/-- **R-6c-body-95 — `coassoc_gen` from the forest block** (via body-94/93/92/91/90/88). -/
theorem ResolvedForestBlockSupply.coassoc_gen
    (S : ResolvedForestBlockSupply D) (x : ResolvedHopfGen) :
    D.coassocLeft (MvPolynomial.X x) = D.coassocRight (MvPolynomial.X x) :=
  S.toForestCoreClassificationSupply.coassoc_gen x

end GaugeGeometry.QFT.Combinatorial
