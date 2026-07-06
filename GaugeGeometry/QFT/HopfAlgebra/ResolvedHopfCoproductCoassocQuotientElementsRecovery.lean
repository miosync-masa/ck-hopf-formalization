import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForwardQuotientHEqScout
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRegionConstructionFromSector

/-!
# R-6c-body-204 — quotient elements recovery: `quotient_elements_heq` from survivor/remnant element identities

Two-hundred-and-fourth genuine-body step, reducing body-203's element `HEq` `quotient_elements_heq` to the two
survivor/remnant element identities.  The recovered quotient forest's components are the survivor ⊔ remnant union,
and `B`'s components split by the star into `rightDomain ∪ forestDomain`; matching the two halves reduces the leaf
to `(rightSurvivorForest recovered).elements = rightDomain z` and `(remnantForest recovered).elements = forestDomain
z` — the two genuinely fresh survivor/remnant identities.

## The membership-union transport helper (PROVED)

`heq_of_membership_split` is the instance-agnostic assembler: two Finsets each characterised as a two-part
membership union, over outers related by a subgraph equality, with the two parts `HEq`, are themselves `HEq`.
Working at the membership level (`∀ x, x ∈ Q ↔ x ∈ surv ∨ x ∈ rem`) sidesteps the `Finset` `∪` `DecidableEq`
instance diamond; `cases` the outer equality (abstract bound variables), `cases eq_of_heq` the two part `HEq`s,
then `Finset.ext`.

## The reduction (PROVED)

`ResolvedQuotientElementsRecoverySupply D S Region` fields the reused `selectedOuter_partition` (the ambient
transport) and the two fresh identities `survivor_elements_heq` / `remnant_elements_heq`.  Then
`.quotient_elements_heq` is **proved**:

* the left membership union is `union_eq` (body-129) + `union_elements` + `Finset.mem_union` (via `convert` +
  `Subsingleton.elim` on the instance);
* the right membership union is the star `filter` split (`rightDomain` / `forestDomain` are the
  star-avoiding / star-touching filters of `z.2.1.elements`);
* `heq_of_membership_split` glues them with the two survivor/remnant `HEq`s.

`.toForwardQuotientHEqDecompositionSupply` produces body-203's supply — so the forward-quotient `HEq` reduces,
through bodies 204 → 203 → 165, to the two survivor/remnant identities.

## What remains (the fresh residual, body-205+)

`survivor_elements_heq : (rightSurvivorForest recovered).elements = rightDomain z` (the survivor half, the dual of
the backward-choice tag agreement, expected lighter) and `remnant_elements_heq : (remnantForest recovered).elements
= forestDomain z` (the remnant half, the de-contraction).  These rest on the survivor/remnant transport kernels
(bodies 125/126) composed with the region `componentToRight` / `componentToForest` images — the dual of the
backward-choice `forest_choiceAt_eq` engine.

Per the HALT: the survivor/remnant identities' bodies are not entered; only the union split + membership assembly is
proved; `componentToRight` / `componentToForest` inverses are untouched.

Landed:

* `heq_of_membership_split` — the instance-agnostic membership-union `HEq` assembler (PROVED);
* `ResolvedQuotientElementsRecoverySupply D S Region` — the ambient transport + the two survivor/remnant identities;
* `.quotient_elements_heq` — body-203's leaf (PROVED from the two identities);
* `.toForwardQuotientHEqDecompositionSupply` — body-203's supply.

Toolkit body (like body-181).  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-204 — the membership-union `HEq` assembler.**  Two Finsets, each a two-part membership union, over
outers related by a subgraph equality, with the two parts `HEq`, are `HEq`.  Membership-level to sidestep the `∪`
`DecidableEq` instance diamond. -/
theorem heq_of_membership_split {G : ResolvedFeynmanGraph} {A₁ A₂ : ResolvedAdmissibleSubgraph G}
    (houter : A₁ = A₂)
    {Q : Finset (ResolvedFeynmanSubgraph (A₁.contractWithStars (D.starOf G A₁)))}
    {Z : Finset (ResolvedFeynmanSubgraph (A₂.contractWithStars (D.starOf G A₂)))}
    {surv rem : Finset (ResolvedFeynmanSubgraph (A₁.contractWithStars (D.starOf G A₁)))}
    {rightDom forestDom : Finset (ResolvedFeynmanSubgraph (A₂.contractWithStars (D.starOf G A₂)))}
    (hQ : ∀ x, x ∈ Q ↔ x ∈ surv ∨ x ∈ rem)
    (hZ : ∀ x, x ∈ Z ↔ x ∈ rightDom ∨ x ∈ forestDom)
    (hs : HEq surv rightDom) (hr : HEq rem forestDom) :
    HEq Q Z := by
  cases houter
  cases eq_of_heq hs
  cases eq_of_heq hr
  apply heq_of_eq
  ext x
  rw [hQ x, hZ x]

/-- **R-6c-body-204 — the quotient elements recovery supply.**  The reused ambient transport
`selectedOuter_partition` and the two fresh survivor/remnant element identities. -/
structure ResolvedQuotientElementsRecoverySupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) (Region : ResolvedRegionChoiceRoundTripSupply D S) where
  /-- Body-162/190: the recovered selected outer has exactly `A`'s components (the ambient transport). -/
  selectedOuter_partition : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    ((S.Forward.imageSupply G).selectedOuterOf
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).1.elements
      = z.1.1.elements
  /-- Survivor half: the recovered right-survivor forest's components are `B`'s star-avoiding survivors. -/
  survivor_elements_heq : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    HEq (S.Survivor.survivor.rightSurvivorForest
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).elements
      (rightDomain z)
  /-- Remnant half: the recovered remnant forest's components are `B`'s star-touching remnants. -/
  remnant_elements_heq : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    HEq (S.Remnant.remnant.remnantForest
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).elements
      (forestDomain z)

namespace ResolvedQuotientElementsRecoverySupply

variable {S : ResolvedConcreteSummandBundleSupply D} {Region : ResolvedRegionChoiceRoundTripSupply D S}

/-- **R-6c-body-204 — body-203's `quotient_elements_heq` from the survivor/remnant identities.** -/
theorem quotient_elements_heq (F : ResolvedQuotientElementsRecoverySupply D S Region)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) :
    HEq (S.quotientForest
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).1.elements
      z.2.1.elements := by
  set q : ResolvedCoassocSplitChoice D G := ⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ with hq
  refine heq_of_membership_split
    (ResolvedAdmissibleSubgraph.ext_elements (F.selectedOuter_partition z))
    (Q := (S.quotientForest q).1.elements) (Z := z.2.1.elements)
    (surv := (S.Survivor.survivor.rightSurvivorForest q).elements)
    (rem := (S.Remnant.remnant.remnantForest q).elements)
    (rightDom := rightDomain z) (forestDom := forestDomain z)
    ?_ ?_ (F.survivor_elements_heq z) (F.remnant_elements_heq z)
  · intro x
    rw [S.union_eq q, ResolvedAdmissibleSubgraph.union_elements]
    convert Finset.mem_union using 2
  · intro x
    simp only [rightDomain, forestDomain, Finset.mem_filter]
    tauto

/-- **R-6c-body-204 — body-203's forward-quotient HEq decomposition supply.** -/
def toForwardQuotientHEqDecompositionSupply (F : ResolvedQuotientElementsRecoverySupply D S Region) :
    ResolvedForwardQuotientHEqDecompositionSupply D S Region where
  selectedOuter_partition := fun {G} z => F.selectedOuter_partition z
  quotient_elements_heq := fun {G} z => F.quotient_elements_heq z

end ResolvedQuotientElementsRecoverySupply

end GaugeGeometry.QFT.Combinatorial
