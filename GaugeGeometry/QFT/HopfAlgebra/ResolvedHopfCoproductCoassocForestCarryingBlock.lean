import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocMixedBoundaryBlock

/-!
# R-6c-body-100 — forest-carrying block: same factorization template, only geometry left

Hundredth genuine-body step, reducing body-98's heavier class equality `forest_class_block` to the SAME shape as
the mixed one (body-99): a `Finset.sum_bij'` over the forest-carrying domain, with `summand_agree` discharged by
the general split-term factorization.  Because `resolved_splitChoiceTerm_factor` (body-99) holds for ANY choice
`p`, the tensor algebra is already done — the forest-carrying summand agreement reduces to the SAME three
geometric identities as the mixed one.  Both classes now have identical structure; only the FullQuotient
outer-mixing maps and their `left/right/quotient` identities remain.

## The generic summand agreement

`resolved_splitChoice_summand_agree_of_factor_eqs` is the class-agnostic form of body-99's
`resolved_mixed_summand_agree` (they are definitionally the same theorem, both routed through
`resolved_splitChoiceTerm_factor`): given `∏ leftFactor = leftTerm A`, `∏ rightFactor = leftTerm B`, `rightTerm
A' = rightTerm B`, the summand agrees.  Used verbatim for the forest-carrying class.

## The fielded forest-carrying map (FullQuotient, heavier)

`ResolvedForestCarryingMapSupply` fields the `Finset.sum_bij'` data between the forest-carrying domain `Σ A', {p
: forestChoiceCarrier A', forest-carrying}` and the forest-image codomain `Σ A, {B : isForestImage}`
(`forestToFun`, `forestInvFun`, `maps_to`s, inverse laws) plus the three geometric identities.  The extra weight
over the mixed case is entirely in the MAP (a component's forest choice `Sum.inr B_γ` is promoted into the
quotient forest `B` — flat `forestQuotientForestSigmaForestCover*`, `Coassoc` 16635+), NOT in the summand
algebra, which is identical.  `mixed_class_block` and `isForestImage` are still fielded (mixed is body-99).

## The reduction (forest_class_block PROVED from the fielded map)

`.toForestBlockClassSupply` flattens both filtered double sums and applies `Finset.sum_bij'` with the fielded
map, discharging the per-term condition by `resolved_splitChoice_summand_agree_of_factor_eqs`.
`.coassoc_gen` chains body-98/96/95/94/93/92/91/90/88.

Per the HALT: the factorization template is reused (no new tensor algebra); the forest-carrying map / inverse
laws / geometric identities are fielded (FullQuotient, heavier); `mixed_class_block` is untouched (body-99); no
star/retarget detail.

Landed:

* `resolved_splitChoice_summand_agree_of_factor_eqs` — the class-agnostic summand agreement (PROVED);
* `forestCarryingDomFinset` / `forestCarryingCodFinset` — the forest-carrying filtered carriers;
* `ResolvedForestCarryingMapSupply D` — the forest-carrying bijection map + geometric identities +
  `isForestImage` + `mixed_class_block` + `carrier_isProperForest` + representative lift;
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

/-- **R-6c-body-100 — the class-agnostic summand agreement** (PROVED).  For ANY choice `p`, given the three
geometric factor identities the summand agrees.  The class-neutral name for body-99's
`resolved_mixed_summand_agree` (same theorem, routed through the general `resolved_splitChoiceTerm_factor`). -/
theorem resolved_splitChoice_summand_agree_of_factor_eqs
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
            ⊗ₜ[ℚ] (D.supply (A.1.contractWithStars (D.starOf G A.1))).rightTerm B) :=
  resolved_mixed_summand_agree A' p A B hL hR hQ

/-- **R-6c-body-100 — the forest-carrying domain carrier.**  `Σ A', {p : forestChoiceCarrier A',
forest-carrying}`. -/
noncomputable def forestCarryingDomFinset (G : ResolvedFeynmanGraph) : Finset (ForestBlockDomType D G) :=
  ((D.carrier G).attach).sigma
    (fun A => (forestChoiceCarrier A).filter (fun p => isForestCarryingChoice A p))

/-- **R-6c-body-100 — the forest-carrying codomain carrier.**  `Σ A, {B : forest-image}`. -/
noncomputable def forestCarryingCodFinset
    (isForestImage : ∀ {G : ResolvedFeynmanGraph} (A : {A : ResolvedAdmissibleSubgraph G // A ∈ D.carrier G}),
      (D.supply (A.1.contractWithStars (D.starOf G A.1))).ForestIdx → Prop)
    (G : ResolvedFeynmanGraph) : Finset (ForestBlockCodType D G) :=
  ((D.carrier G).attach).sigma
    (fun A => ((D.supply (A.1.contractWithStars (D.starOf G A.1))).forestCarrier).filter
      (fun B => isForestImage A B))

/-- **R-6c-body-100 — the forest-carrying map supply.**  The `Finset.sum_bij'` data for the forest-carrying
bijection (map, inverse, `maps_to`s, inverse laws) plus the three geometric identities, with `isForestImage` /
`mixed_class_block` (mixed is body-99), `carrier_isProperForest`, and a representative lift. -/
structure ResolvedForestCarryingMapSupply (D : ResolvedCoproductProperForestData) where
  /-- Which quotient forests `B` are hit by the forest-carrying class (fielded classification). -/
  isForestImage : ∀ {G : ResolvedFeynmanGraph} (A : {A : ResolvedAdmissibleSubgraph G // A ∈ D.carrier G}),
    (D.supply (A.1.contractWithStars (D.starOf G A.1))).ForestIdx → Prop
  /-- The mixed-boundary bijection (deferred to body-99). -/
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
  /-- The forest-carrying map `(A', p) ↦ (A, B)` (outer-mixing; promotes forest choices into `B`). -/
  forestToFun : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G),
    q ∈ forestCarryingDomFinset G → ForestBlockCodType D G
  /-- The inverse `(A, B) ↦ (A', p)`. -/
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
  /-- Geometric identity: the left-factor product is the target outer's left term. -/
  forest_left_eq : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G)
    (hq : q ∈ forestCarryingDomFinset G),
    (∏ γ ∈ (q.1.1.elements.attach).attach,
        localLeftFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2))
      = (D.supply G).leftTerm (forestToFun G q hq).1
  /-- Geometric identity: the right-factor product is the quotient forest's left term. -/
  forest_right_eq : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G)
    (hq : q ∈ forestCarryingDomFinset G),
    (∏ γ ∈ (q.1.1.elements.attach).attach,
        localRightFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2))
      = (D.supply ((forestToFun G q hq).1.1.contractWithStars (D.starOf G (forestToFun G q hq).1.1))).leftTerm
          (forestToFun G q hq).2
  /-- Geometric identity: the source quotient right term is the quotient forest's right term. -/
  forest_quotient_eq : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G)
    (hq : q ∈ forestCarryingDomFinset G),
    (D.supply G).rightTerm q.1
      = (D.supply ((forestToFun G q hq).1.1.contractWithStars (D.starOf G (forestToFun G q hq).1.1))).rightTerm
          (forestToFun G q hq).2
  /-- Every carrier forest is a proper forest (body-96; gives `outer_nonempty`). -/
  carrier_isProperForest : ∀ (G : ResolvedFeynmanGraph) (A : ResolvedAdmissibleSubgraph G),
    A ∈ D.carrier G → A.IsProperForest
  /-- A representative graph for each generator. -/
  rep : ResolvedHopfGen → ResolvedFeynmanGraph
  /-- The representative is connected-divergent. -/
  repCD : ∀ x : ResolvedHopfGen, (rep x).forget.toClass.IsConnectedDivergent
  /-- The representative's generator IS `x`. -/
  rep_gen : ∀ x : ResolvedHopfGen, x = (rep x).toResolvedHopfGen (repCD x)

/-- **R-6c-body-100 — body-98's class supply from the forest-carrying map** (forest_class_block PROVED). -/
def ResolvedForestCarryingMapSupply.toForestBlockClassSupply
    (S : ResolvedForestCarryingMapSupply D) : ResolvedForestBlockClassSupply D where
  isForestImage := fun {G} A B => S.isForestImage A B
  mixed_class_block := S.mixed_class_block
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
  carrier_isProperForest := S.carrier_isProperForest
  rep := S.rep
  repCD := S.repCD
  rep_gen := S.rep_gen

/-- **R-6c-body-100 — `coassoc_gen` from the forest-carrying map** (via body-98/96/95/94/93/92/91/90/88). -/
theorem ResolvedForestCarryingMapSupply.coassoc_gen
    (S : ResolvedForestCarryingMapSupply D) (x : ResolvedHopfGen) :
    D.coassocLeft (MvPolynomial.X x) = D.coassocRight (MvPolynomial.X x) :=
  S.toForestBlockClassSupply.coassoc_gen x

end GaugeGeometry.QFT.Combinatorial
