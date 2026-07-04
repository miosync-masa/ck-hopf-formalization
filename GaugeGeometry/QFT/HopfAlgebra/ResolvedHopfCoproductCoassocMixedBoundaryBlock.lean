import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestBlockClasses

/-!
# R-6c-body-99 — mixed-boundary block: split-term tensor factorization PROVED, map fielded

Ninety-ninth genuine-body step, attacking the lighter of body-98's two class equalities: `mixed_class_block`
(primitive-only choices).  The full tensor-algebra backbone is PROVED here — every split term factors as a pure
tensor `(∏ leftFactor) ⊗ ((∏ rightFactor) ⊗ rightTerm A)` — reducing the mixed bijection's `summand_agree` to
three purely GEOMETRIC identities (`∏ leftFactor = leftTerm A`, `∏ rightFactor = leftTerm B`, `rightTerm A' =
rightTerm B`), which are fielded (the FullQuotient outer-mixing map).

## The split-term factorization (PROVED, reusable for BOTH classes)

Every `localChoiceTerm` is a pure tensor: `Sum.inl true ↦ X ⊗ 1`, `Sum.inl false ↦ 1 ⊗ X`, `Sum.inr B ↦ leftTerm
B ⊗ rightTerm B`.  So with `localLeftFactor` / `localRightFactor` the two tensor legs,
`localChoiceTerm_factor` gives `localChoiceTerm c = localLeftFactor c ⊗ localRightFactor c`, and (via
`prod_tmul_factor`, valid in the COMMUTATIVE tensor ring) `resolved_splitChoiceTerm_factor`:

```text
splitTerm ⟨A, p⟩ = (∏_γ localLeftFactor (p γ)) ⊗ ((∏_γ localRightFactor (p γ)) ⊗ rightTerm A)
```

This holds for ANY `p` (mixed OR forest-carrying) — it is the algebraic backbone of both class bijections.

## The summand agreement, reduced to geometry (PROVED)

`resolved_mixed_summand_agree`: given `∏ localLeftFactor = leftTerm A`, `∏ localRightFactor = leftTerm B`,
`rightTerm A' = rightTerm B`, the summand agrees: `splitTerm ⟨A', p⟩ = leftTerm A ⊗ (leftTerm B ⊗ rightTerm B)`.
So the mixed bijection's `summand_agree` is now three geometric identities — no tensor algebra left.

## The fielded map (FullQuotient outer-mixing)

`ResolvedMixedBoundaryMapSupply` fields the `Finset.sum_bij'` data between the mixed domain `Σ A', {p :
forestChoiceCarrier A', ¬forest-carrying}` and the non-forest-image codomain `Σ A, {B : ¬isForestImage}`
(`mixedToFun`, `mixedInvFun`, the `maps_to`s, the two inverse laws) plus the three geometric identities.  The
outer-mixing (`A ⊇ A'`: left-selected components enlarge `A'` to `A`, right-selected primitives become `B`) is
free in the codomain's separate `Σ`-component — the resolved port of flat
`forestComponentMixedBoundaryToQuotientForestSigma`.  `forest_class_block` and `isForestImage` are still fielded
(forest-carrying is body-100).

## The reduction (mixed_class_block PROVED from the fielded map)

`.toForestBlockClassSupply` flattens both filtered double sums (`Finset.sum_sigma'`) and applies
`Finset.sum_bij'` with the fielded map, discharging the per-term condition by `resolved_mixed_summand_agree` —
`mixed_class_block` is PROVED modulo the map + three geometric identities.  `.coassoc_gen` chains
body-98/96/95/94/93/92/91/90/88.

Per the HALT: the split-term factorization + summand reduction ARE proved; the map / inverse laws / geometric
identities are fielded (FullQuotient); `forest_class_block` is untouched (body-100); no star/retarget detail.

Landed:

* `localLeftFactor` / `localRightFactor` / `localChoiceTerm_factor` / `prod_tmul_factor` /
  `resolved_splitChoiceTerm_factor` — the split-term tensor factorization (PROVED);
* `resolved_mixed_summand_agree` — `summand_agree` from the three geometric identities (PROVED);
* `ResolvedMixedBoundaryMapSupply D` — the mixed bijection map + geometric identities + `isForestImage` +
  `forest_class_block` + `carrier_isProperForest` + representative lift;
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

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- **R-6c-body-99 — the left tensor leg of `localChoiceTerm`.**  `Sum.inl true ↦ X`, `Sum.inl false ↦ 1`,
`Sum.inr B ↦ leftTerm B`. -/
noncomputable def localLeftFactor (γG : ResolvedFeynmanGraph)
    (hCD : γG.forget.toClass.IsConnectedDivergent) :
    (Bool ⊕ (D.supply γG).ForestIdx) → ResolvedHopfH :=
  Sum.elim (fun b => bif b then MvPolynomial.X (γG.toResolvedHopfGen hCD) else (1 : ResolvedHopfH))
    (fun B => (D.supply γG).leftTerm B)

/-- **R-6c-body-99 — the right tensor leg of `localChoiceTerm`.**  `Sum.inl true ↦ 1`, `Sum.inl false ↦ X`,
`Sum.inr B ↦ rightTerm B`. -/
noncomputable def localRightFactor (γG : ResolvedFeynmanGraph)
    (hCD : γG.forget.toClass.IsConnectedDivergent) :
    (Bool ⊕ (D.supply γG).ForestIdx) → ResolvedHopfH :=
  Sum.elim (fun b => bif b then (1 : ResolvedHopfH) else MvPolynomial.X (γG.toResolvedHopfGen hCD))
    (fun B => (D.supply γG).rightTerm B)

/-- **R-6c-body-99 — `localChoiceTerm` is a pure tensor.** -/
theorem localChoiceTerm_factor (γG : ResolvedFeynmanGraph)
    (hCD : γG.forget.toClass.IsConnectedDivergent) (c : Bool ⊕ (D.supply γG).ForestIdx) :
    D.localChoiceTerm γG hCD c
      = localLeftFactor (D := D) γG hCD c ⊗ₜ[ℚ] localRightFactor (D := D) γG hCD c := by
  cases c with
  | inl b => cases b <;> rfl
  | inr B => rfl

/-- **R-6c-body-99 — product of pure tensors factors** (valid in the commutative tensor ring). -/
theorem prod_tmul_factor {ι : Type*} (s : Finset ι) (f g : ι → ResolvedHopfH) :
    (∏ x ∈ s, (f x ⊗ₜ[ℚ] g x)) = (∏ x ∈ s, f x) ⊗ₜ[ℚ] (∏ x ∈ s, g x) := by
  classical
  induction s using Finset.induction with
  | empty => exact Algebra.TensorProduct.one_def
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.prod_insert ha, ih,
      Algebra.TensorProduct.tmul_mul_tmul]

/-- **R-6c-body-99 — the split-term tensor factorization** (for ANY choice `p`).  `splitTerm ⟨A, p⟩ = (∏
localLeftFactor) ⊗ ((∏ localRightFactor) ⊗ rightTerm A)`.  The algebraic backbone of BOTH class bijections. -/
theorem resolved_splitChoiceTerm_factor
    (A : {A : ResolvedAdmissibleSubgraph G // A ∈ D.carrier G})
    (p : ∀ γ ∈ A.1.elements.attach, Bool ⊕ (D.supply (γ.1.toResolvedFeynmanGraph)).ForestIdx) :
    D.resolvedSplitChoiceTerm (⟨A, p⟩ : ResolvedCoassocSplitChoice D G)
      = (∏ γ ∈ (A.1.elements.attach).attach,
            localLeftFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD A.1 γ.1) (p γ.1 γ.2))
        ⊗ₜ[ℚ]
          ((∏ γ ∈ (A.1.elements.attach).attach,
              localRightFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD A.1 γ.1) (p γ.1 γ.2))
            ⊗ₜ[ℚ] (D.supply G).rightTerm A) := by
  unfold ResolvedCoproductProperForestData.resolvedSplitChoiceTerm
  rw [Finset.prod_congr rfl (fun γ _ =>
      localChoiceTerm_factor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD A.1 γ.1) (p γ.1 γ.2)),
    prod_tmul_factor, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe, Algebra.TensorProduct.assoc_tmul]

/-- **R-6c-body-99 — the summand agreement from three geometric identities** (PROVED).  Reduces the mixed
bijection's `summand_agree` to `∏ leftFactor = leftTerm A`, `∏ rightFactor = leftTerm B`, `rightTerm A' =
rightTerm B`. -/
theorem resolved_mixed_summand_agree
    (A' : {A : ResolvedAdmissibleSubgraph G // A ∈ D.carrier G})
    (p : ∀ γ ∈ A'.1.elements.attach, Bool ⊕ (D.supply (γ.1.toResolvedFeynmanGraph)).ForestIdx)
    (A : {A : ResolvedAdmissibleSubgraph G // A ∈ D.carrier G})
    (B : (D.supply (A.1.contractWithStars (D.starOf G A.1))).ForestIdx)
    (hL : (∏ γ ∈ (A'.1.elements.attach).attach,
            localLeftFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD A'.1 γ.1) (p γ.1 γ.2))
          = (D.supply G).leftTerm A)
    (hR : (∏ γ ∈ (A'.1.elements.attach).attach,
            localRightFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD A'.1 γ.1) (p γ.1 γ.2))
          = (D.supply (A.1.contractWithStars (D.starOf G A.1))).leftTerm B)
    (hQ : (D.supply G).rightTerm A'
          = (D.supply (A.1.contractWithStars (D.starOf G A.1))).rightTerm B) :
    D.resolvedSplitChoiceTerm (⟨A', p⟩ : ResolvedCoassocSplitChoice D G)
      = (D.supply G).leftTerm A ⊗ₜ[ℚ]
          ((D.supply (A.1.contractWithStars (D.starOf G A.1))).leftTerm B
            ⊗ₜ[ℚ] (D.supply (A.1.contractWithStars (D.starOf G A.1))).rightTerm B) := by
  rw [resolved_splitChoiceTerm_factor A' p, hL, hR, hQ]

/-- **R-6c-body-99 — the mixed domain carrier.**  `Σ A', {p : forestChoiceCarrier A', not forest-carrying}`. -/
noncomputable def mixedDomFinset (G : ResolvedFeynmanGraph) : Finset (ForestBlockDomType D G) :=
  ((D.carrier G).attach).sigma
    (fun A => (forestChoiceCarrier A).filter (fun p => ¬ isForestCarryingChoice A p))

/-- **R-6c-body-99 — the mixed codomain carrier.**  `Σ A, {B : not forest-image}`. -/
noncomputable def mixedCodFinset
    (isForestImage : ∀ {G : ResolvedFeynmanGraph} (A : {A : ResolvedAdmissibleSubgraph G // A ∈ D.carrier G}),
      (D.supply (A.1.contractWithStars (D.starOf G A.1))).ForestIdx → Prop)
    (G : ResolvedFeynmanGraph) : Finset (ForestBlockCodType D G) :=
  ((D.carrier G).attach).sigma
    (fun A => ((D.supply (A.1.contractWithStars (D.starOf G A.1))).forestCarrier).filter
      (fun B => ¬ isForestImage A B))

/-- **R-6c-body-99 — the mixed-boundary map supply.**  The `Finset.sum_bij'` data for the mixed-boundary
bijection (map, inverse, `maps_to`s, inverse laws) plus the three geometric identities reducing `summand_agree`,
with `isForestImage` / `forest_class_block` (forest-carrying deferred to body-100), `carrier_isProperForest`, and
a representative lift. -/
structure ResolvedMixedBoundaryMapSupply (D : ResolvedCoproductProperForestData) where
  /-- Which quotient forests `B` are hit by the forest-carrying class (fielded classification). -/
  isForestImage : ∀ {G : ResolvedFeynmanGraph} (A : {A : ResolvedAdmissibleSubgraph G // A ∈ D.carrier G}),
    (D.supply (A.1.contractWithStars (D.starOf G A.1))).ForestIdx → Prop
  /-- The forest-carrying bijection (deferred to body-100). -/
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
  /-- The mixed-boundary map `(A', p) ↦ (A, B)` (outer-mixing). -/
  mixedToFun : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G),
    q ∈ mixedDomFinset G → ForestBlockCodType D G
  /-- The inverse `(A, B) ↦ (A', p)`. -/
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
  /-- Geometric identity: the left-factor product is the target outer's left term. -/
  mixed_left_eq : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G) (hq : q ∈ mixedDomFinset G),
    (∏ γ ∈ (q.1.1.elements.attach).attach,
        localLeftFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2))
      = (D.supply G).leftTerm (mixedToFun G q hq).1
  /-- Geometric identity: the right-factor product is the quotient forest's left term. -/
  mixed_right_eq : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G) (hq : q ∈ mixedDomFinset G),
    (∏ γ ∈ (q.1.1.elements.attach).attach,
        localRightFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2))
      = (D.supply ((mixedToFun G q hq).1.1.contractWithStars (D.starOf G (mixedToFun G q hq).1.1))).leftTerm
          (mixedToFun G q hq).2
  /-- Geometric identity: the source quotient right term is the quotient forest's right term. -/
  mixed_quot_eq : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G) (hq : q ∈ mixedDomFinset G),
    (D.supply G).rightTerm q.1
      = (D.supply ((mixedToFun G q hq).1.1.contractWithStars (D.starOf G (mixedToFun G q hq).1.1))).rightTerm
          (mixedToFun G q hq).2
  /-- Every carrier forest is a proper forest (body-96; gives `outer_nonempty`). -/
  carrier_isProperForest : ∀ (G : ResolvedFeynmanGraph) (A : ResolvedAdmissibleSubgraph G),
    A ∈ D.carrier G → A.IsProperForest
  /-- A representative graph for each generator. -/
  rep : ResolvedHopfGen → ResolvedFeynmanGraph
  /-- The representative is connected-divergent. -/
  repCD : ∀ x : ResolvedHopfGen, (rep x).forget.toClass.IsConnectedDivergent
  /-- The representative's generator IS `x`. -/
  rep_gen : ∀ x : ResolvedHopfGen, x = (rep x).toResolvedHopfGen (repCD x)

/-- **R-6c-body-99 — body-98's class supply from the mixed map** (mixed_class_block PROVED). -/
def ResolvedMixedBoundaryMapSupply.toForestBlockClassSupply
    (S : ResolvedMixedBoundaryMapSupply D) : ResolvedForestBlockClassSupply D where
  isForestImage := fun {G} A B => S.isForestImage A B
  forest_class_block := S.forest_class_block
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
      (fun q hq => resolved_mixed_summand_agree q.1 q.2 (S.mixedToFun G q hq).1 (S.mixedToFun G q hq).2
        (S.mixed_left_eq G q hq) (S.mixed_right_eq G q hq) (S.mixed_quot_eq G q hq))
  carrier_isProperForest := S.carrier_isProperForest
  rep := S.rep
  repCD := S.repCD
  rep_gen := S.rep_gen

/-- **R-6c-body-99 — `coassoc_gen` from the mixed map** (via body-98/96/95/94/93/92/91/90/88). -/
theorem ResolvedMixedBoundaryMapSupply.coassoc_gen
    (S : ResolvedMixedBoundaryMapSupply D) (x : ResolvedHopfGen) :
    D.coassocLeft (MvPolynomial.X x) = D.coassocRight (MvPolynomial.X x) :=
  S.toForestBlockClassSupply.coassoc_gen x

end GaugeGeometry.QFT.Combinatorial
