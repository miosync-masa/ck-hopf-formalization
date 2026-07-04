import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocLocalLeftFactorProduct
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocQuotientForestTermFactors
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestCarryingBlock

/-!
# R-6c-body-127 — summand-agreement factor bundle: the four factor products + `quot_eq` → the summand agreement

Hundred-and-twenty-seventh genuine-body step, the CAPSTONE of the summand-agreement PRODUCT side.  Bodies
119–126 closed each of the four factor products and the two survival/remnant transports; body-108/109/111 assembled
the left / right / quotient identities from those parts; body-100 turns the three identities into the summand
agreement.  This body bundles the whole chain into ONE per-split-choice theorem and ONE supply structure, so the
entire summand-agreement side is now a single object.

## The per-`q` assembler (PROVED)

`resolved_summand_agree_of_factor_parts`: for a selected-outer image supply `S`, a split choice `q`, the quotient
forest index `B` and its `rightSurvivor ⊔ remnant` decomposition, plus the four factor products, the two
disjointnesses, and the contract-twice `quot_eq` (`hQ`),

```text
D.resolvedSplitChoiceTerm q
  = leftTerm (selectedOuterOf q) ⊗ (leftTerm B ⊗ rightTerm B)
```

by chaining `resolved_selectedOuter_left_factor_eq_of_parts` (body-108, → the left identity `hL`),
`resolved_quotientForest_right_factor_eq_of_parts` (body-109, → the right identity `hR`) and the supplied `hQ`
into `resolved_splitChoice_summand_agree_of_factor_eqs` (body-100).  Every hypothesis is a factor product / union /
disjointness / generator identity discharged by an earlier body:

| hypothesis | discharged by |
|---|---|
| `left_primitive_factor` | body-119 (`left_primitive_factor_concrete`, unconditional) |
| `promoted_factor` | body-122 (`promoted_factor_of_hPD`, given `hPD`) |
| `hLdisj` | body-116/124 (`leftHDisj`, nonemptiness) |
| `right_primitive_factor` | body-120+125 (`ResolvedRightPrimitiveSurvivalTransportSupply.right_primitive_factor`) |
| `remnant_factor` | body-123+126 (`ResolvedRemnantTransportSupply.remnant_factor`) |
| `hcross` / `union_eq` / `hRdisj` | body-115 (the quotient `rightSurvivor ⊔ remnant` decomposition) |
| `hQ` | body-111 (`resolved_quot_eq_from_contract_geometry`) |

## The bundle

`ResolvedSummandFactorBundle D` consolidates the selected-outer supply and the per-`q` parts into one structure;
`.summand_agree q` is the assembler applied.  So the summand-agreement PRODUCT side is represented by a single
supply, and the residual coassoc content is purely the map wiring (`quotient_mem` / backward / `maps_to` /
inverse laws / contract-twice geometry) and the base providers (carrier proper, measure leaf, survivor/remnant
`Inj`/`Gen`).

The bundle fields the four factor products (rather than embedding the body-125/126 transport supplies directly)
because those supplies produce their forests over `q.selectedOuterContractGraph` (the concrete-promote quotient
graph) while the assembler consumes them over `(selectedOuterOf q).1.contractWithStars …`; identifying the two is
the forward-map coherence (`imageSupply` = the concrete selected supply), a map-wiring obligation the HALT keeps
out of the summand-agreement side.  So the transports slot in exactly once that single coherence is supplied.

Per the HALT: the assembler is summand-agreement only; the parts are consolidated into one bundle; no backward
map / inverse law / `quotient_mem` is filled.

Landed:

* `resolved_summand_agree_of_factor_parts` — the per-`q` summand agreement from the parts (PROVED);
* `ResolvedSummandFactorBundle D` — the bundle of the selected supply + per-`q` factor parts;
* `.summand_agree` — the summand agreement, per split choice.

Toolkit body (like body-125/126), one consolidating supply.  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-127 — the per-`q` summand agreement from the factor parts.**  Chains the left (body-108), right
(body-109) and quotient (`hQ`, body-111) identities into the body-100 summand agreement.  Every hypothesis is a
factor product / union / disjointness / generator identity discharged by bodies 119/122/125/126/115/111. -/
theorem resolved_summand_agree_of_factor_parts
    (S : ResolvedCoassocSelectedOuterImageSupply D G) (q : ForestBlockDomType D G)
    (B : (D.supply ((S.selectedOuterOf q).1.contractWithStars
        (D.starOf G (S.selectedOuterOf q).1))).ForestIdx)
    (rightSurvivor remnant : ResolvedAdmissibleSubgraph ((S.selectedOuterOf q).1.contractWithStars
        (D.starOf G (S.selectedOuterOf q).1)))
    (hcross : ∀ γ ∈ rightSurvivor.elements, ∀ δ ∈ remnant.elements, γ ≠ δ → γ.Disjoint δ)
    (union_eq : B.1 = rightSurvivor.union remnant hcross)
    (hRdisj : Disjoint rightSurvivor.elements remnant.elements)
    (left_primitive_factor :
      (∏ γ ∈ (q.1.1.elements.attach).attach.filter (fun γ => ¬ (q.2 γ.1 γ.2).isRight),
          localLeftFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2))
        = resolvedForestLeftTerm (S.leftSelection.leftOf q))
    (promoted_factor :
      (∏ γ ∈ (q.1.1.elements.attach).attach.filter (fun γ => (q.2 γ.1 γ.2).isRight),
          localLeftFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2))
        = resolvedForestLeftTerm (S.promotedOf q))
    (hLdisj : Disjoint (S.leftSelection.leftOf q).elements (S.promotedOf q).elements)
    (right_primitive_factor :
      (∏ γ ∈ (q.1.1.elements.attach).attach.filter (fun γ => ¬ (q.2 γ.1 γ.2).isRight),
          localRightFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2))
        = resolvedForestLeftTerm rightSurvivor)
    (remnant_factor :
      (∏ γ ∈ (q.1.1.elements.attach).attach.filter (fun γ => (q.2 γ.1 γ.2).isRight),
          localRightFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2))
        = resolvedForestLeftTerm remnant)
    (hQ : (D.supply G).rightTerm q.1
        = (D.supply ((S.selectedOuterOf q).1.contractWithStars
            (D.starOf G (S.selectedOuterOf q).1))).rightTerm B) :
    D.resolvedSplitChoiceTerm (q : ResolvedCoassocSplitChoice D G)
      = (D.supply G).leftTerm (S.selectedOuterOf q) ⊗ₜ[ℚ]
          ((D.supply ((S.selectedOuterOf q).1.contractWithStars
              (D.starOf G (S.selectedOuterOf q).1))).leftTerm B
            ⊗ₜ[ℚ] (D.supply ((S.selectedOuterOf q).1.contractWithStars
              (D.starOf G (S.selectedOuterOf q).1))).rightTerm B) :=
  resolved_splitChoice_summand_agree_of_factor_eqs q.1 q.2 (S.selectedOuterOf q) B
    (resolved_selectedOuter_left_factor_eq_of_parts S q left_primitive_factor promoted_factor hLdisj)
    (resolved_quotientForest_right_factor_eq_of_parts q _ B rightSurvivor remnant hcross union_eq
      hRdisj right_primitive_factor remnant_factor)
    hQ

/-- **R-6c-body-127 — the summand-agreement factor bundle.**  One structure holding the selected-outer image
supply and, per split choice, the quotient forest with its `rightSurvivor ⊔ remnant` decomposition, the four
factor products, the two disjointnesses, and the contract-twice `quot_eq`.  `.summand_agree` produces the body-100
summand agreement for every split choice. -/
structure ResolvedSummandFactorBundle (D : ResolvedCoproductProperForestData) where
  /-- The selected-outer image supply (`selectedOuterOf` = the codomain outer forest). -/
  selected : ∀ {G : ResolvedFeynmanGraph}, ResolvedCoassocSelectedOuterImageSupply D G
  /-- The quotient forest index over the contract graph (the codomain quotient `B`). -/
  quotientForest : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G),
    (D.supply ((selected.selectedOuterOf q).1.contractWithStars
      (D.starOf G (selected.selectedOuterOf q).1))).ForestIdx
  /-- The right-survivor half of the quotient forest (body-125). -/
  rightSurvivor : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G),
    ResolvedAdmissibleSubgraph ((selected.selectedOuterOf q).1.contractWithStars
      (D.starOf G (selected.selectedOuterOf q).1))
  /-- The remnant half of the quotient forest (body-126). -/
  remnant : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G),
    ResolvedAdmissibleSubgraph ((selected.selectedOuterOf q).1.contractWithStars
      (D.starOf G (selected.selectedOuterOf q).1))
  /-- The survivor/remnant cross-disjointness (body-115). -/
  hcross : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G),
    ∀ γ ∈ (rightSurvivor q).elements, ∀ δ ∈ (remnant q).elements, γ ≠ δ → γ.Disjoint δ
  /-- The quotient forest is the survivor ⊔ remnant union (body-115). -/
  union_eq : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G),
    (quotientForest q).1 = (rightSurvivor q).union (remnant q) (hcross q)
  /-- The survivor/remnant `Finset`-disjointness (body-115). -/
  hRdisj : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G),
    Disjoint (rightSurvivor q).elements (remnant q).elements
  /-- The left-primitive factor product (body-119). -/
  left_primitive_factor : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G),
    (∏ γ ∈ (q.1.1.elements.attach).attach.filter (fun γ => ¬ (q.2 γ.1 γ.2).isRight),
        localLeftFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2))
      = resolvedForestLeftTerm (selected.leftSelection.leftOf q)
  /-- The promoted factor product (body-122, given `hPD`). -/
  promoted_factor : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G),
    (∏ γ ∈ (q.1.1.elements.attach).attach.filter (fun γ => (q.2 γ.1 γ.2).isRight),
        localLeftFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2))
      = resolvedForestLeftTerm (selected.promotedOf q)
  /-- The left / promoted disjointness (body-116). -/
  hLdisj : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G),
    Disjoint (selected.leftSelection.leftOf q).elements (selected.promotedOf q).elements
  /-- The right-primitive factor product (body-125). -/
  right_primitive_factor : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G),
    (∏ γ ∈ (q.1.1.elements.attach).attach.filter (fun γ => ¬ (q.2 γ.1 γ.2).isRight),
        localRightFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2))
      = resolvedForestLeftTerm (rightSurvivor q)
  /-- The remnant factor product (body-126). -/
  remnant_factor : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G),
    (∏ γ ∈ (q.1.1.elements.attach).attach.filter (fun γ => (q.2 γ.1 γ.2).isRight),
        localRightFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2))
      = resolvedForestLeftTerm (remnant q)
  /-- The contract-twice quotient generator identity (`quot_eq`, body-111). -/
  quot_eq : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G),
    (D.supply G).rightTerm q.1
      = (D.supply ((selected.selectedOuterOf q).1.contractWithStars
          (D.starOf G (selected.selectedOuterOf q).1))).rightTerm (quotientForest q)

/-- **R-6c-body-127 — the summand agreement from the bundle.**  For every split choice, the resolved split-choice
term equals `leftTerm(selectedOuterOf) ⊗ (leftTerm B ⊗ rightTerm B)` — the summand-agreement PRODUCT side, now a
single supply. -/
theorem ResolvedSummandFactorBundle.summand_agree (F : ResolvedSummandFactorBundle D)
    (q : ForestBlockDomType D G) :
    D.resolvedSplitChoiceTerm (q : ResolvedCoassocSplitChoice D G)
      = (D.supply G).leftTerm (F.selected.selectedOuterOf q) ⊗ₜ[ℚ]
          ((D.supply ((F.selected.selectedOuterOf q).1.contractWithStars
              (D.starOf G (F.selected.selectedOuterOf q).1))).leftTerm (F.quotientForest q)
            ⊗ₜ[ℚ] (D.supply ((F.selected.selectedOuterOf q).1.contractWithStars
              (D.starOf G (F.selected.selectedOuterOf q).1))).rightTerm (F.quotientForest q)) :=
  resolved_summand_agree_of_factor_parts F.selected q (F.quotientForest q) (F.rightSurvivor q)
    (F.remnant q) (F.hcross q) (F.union_eq q) (F.hRdisj q) (F.left_primitive_factor q)
    (F.promoted_factor q) (F.hLdisj q) (F.right_primitive_factor q) (F.remnant_factor q) (F.quot_eq q)

end GaugeGeometry.QFT.Combinatorial
