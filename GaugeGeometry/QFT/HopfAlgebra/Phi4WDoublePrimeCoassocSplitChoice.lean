import GaugeGeometry.QFT.HopfAlgebra.Phi4WDoublePrimeCoassocLocalChoice

/-!
# QFT-R1-body-595 — live inner-forest consumers + filtered split-choice index

Body-594 expanded the forest-left aggregate resolved coproduct into a sum over **global component
choices** `p` (a local choice per component), with every inner ambient the **boundary-completed**
`γ.boundaryCompletedResolvedGraph`.  This body bridges that ALGEBRAIC index to a GEOMETRY index — a
filtered split-choice carrier — whose victory condition is that the split-choice TYPE itself keeps every
non-trivial inner forest as a LIVE W″ member on the boundary-completed ambient.

The two non-negotiables:

* the inner ambient is ALWAYS `γ.boundaryCompletedResolvedGraph` (via body-594's `phi4LocalChoiceCarrier`,
  whose forest part is indexed by `{B // B ∈ (index γ.boundaryCompletedResolvedGraph).carrier}` — the live
  carrier membership `B.2` for free); NEVER `γ.toResolvedFeynmanGraph`;
* `B.2` (the live membership) is never dismantled into independent leaf hypotheses — `B` itself stays the
  owner, and the consumers are DERIVED from `B.2` via body-593's leaf supply.

## Contents

* Step 1 — live inner-forest consumers `phi4Inner_isProperForest` / `phi4Inner_component_vertices_nonempty`
  / `phi4Inner_component_internalEdges_card_pos` / `phi4Inner_contract_isConnectedDivergentFor`, each
  proved by `phi4WDoublePrimeCoassocLeafSupply.<thm> B.2` on the inner ambient
  `γ.boundaryCompletedResolvedGraph`.
* Step 2 — `phi4GlobalChoiceCarrier` / `phi4ChoicePR` / `phi4ChoicePL` / `phi4ForestChoiceCarrier`, plus the
  membership / distinctness / filter-iff lemmas.
* Step 3 — `Phi4ResolvedCoassocSplitChoice` / `Phi4FilteredCoassocSplitChoice` (the two split-choice
  structures; the `Sum.inr B` inside `choice` carries the live inner membership).
* Step 4 — `phi4_pure_choice_partition` (generic-weight pure-choice partition, with `A.elements.Nonempty`
  DERIVED from body-593's `carrier_isProperForest`, NOT fielded as a measure-level obligation).

The KEY improvement over the old abstract `pure_choice_partition`: that one FIELDED `outer_nonempty` (a
measure-level obligation, body-1); here `A.elements.Nonempty` is DERIVED from `carrier_isProperForest hA`
(body-593).  No `outer_nonempty` field, no measure leaf.

Per the HALT: no selectedOuter / promote / quotient geometry / old `ResolvedCoassocSplitChoice` / forest
bijection; no Measure / E old supply (`outer_nonempty` is DERIVED); no raw `γ.toResolvedFeynmanGraph` (inner
ambient fixed to `boundaryCompletedResolvedGraph`); `B.2` never dismantled; no alpha / contract-twice /
coassoc; two new `structure`s max (Step 3), zero `class` / `instance`; zero forbidden divergence classes;
no `sorry`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct
open scoped Classical

/-! ## Step 1 — live inner-forest consumers (from body-593 + `B.2`, no leaf decomposition)

`B` ranges over the boundary-completed inner carrier
`↥(phi4WDoublePrimeCanonicalSupply.index γ.boundaryCompletedResolvedGraph).carrier`; `B.1` is the inner
forest and `B.2` is its live carrier membership.  Every consumer is issued by feeding `B.2` to body-593's
leaf supply — `B` stays the owner, nothing is decomposed. -/

/-- **body-595 (Step 1) — the live inner forest is a proper forest.**  Directly from body-593's
`carrier_isProperForest B.2`. -/
theorem phi4Inner_isProperForest {G : ResolvedFeynmanGraph} (γ : ResolvedFeynmanSubgraph G)
    (B : {B : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily
        γ.boundaryCompletedResolvedGraph //
        B ∈ @ResolvedProperForestFiniteIndex.carrier phi4DivergenceMeasureFamily
          γ.boundaryCompletedResolvedGraph
          (phi4WDoublePrimeCanonicalSupply.index γ.boundaryCompletedResolvedGraph)}) :
    @ResolvedAdmissibleSubgraph.IsProperForest phi4DivergenceMeasureFamily
      γ.boundaryCompletedResolvedGraph B.1 :=
  phi4WDoublePrimeCoassocLeafSupply.carrier_isProperForest B.2

/-- **body-595 (Step 1) — every inner component is vertex-nonempty.**  From body-593's
`component_vertices_nonempty B.2` (an `IsProperForest` conjunct), on the boundary-completed ambient. -/
theorem phi4Inner_component_vertices_nonempty {G : ResolvedFeynmanGraph} (γ : ResolvedFeynmanSubgraph G)
    (B : {B : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily
        γ.boundaryCompletedResolvedGraph //
        B ∈ @ResolvedProperForestFiniteIndex.carrier phi4DivergenceMeasureFamily
          γ.boundaryCompletedResolvedGraph
          (phi4WDoublePrimeCanonicalSupply.index γ.boundaryCompletedResolvedGraph)})
    {δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph}
    (hδ : δ ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily
      γ.boundaryCompletedResolvedGraph B.1) :
    δ.vertices.Nonempty :=
  phi4WDoublePrimeCoassocLeafSupply.component_vertices_nonempty B.2 hδ

/-- **body-595 (Step 1) — every inner component carries a positive internal edge.**  From body-593's
`component_internalEdges_card_pos B.2` (an `IsProperForest` conjunct), on the boundary-completed ambient. -/
theorem phi4Inner_component_internalEdges_card_pos {G : ResolvedFeynmanGraph}
    (γ : ResolvedFeynmanSubgraph G)
    (B : {B : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily
        γ.boundaryCompletedResolvedGraph //
        B ∈ @ResolvedProperForestFiniteIndex.carrier phi4DivergenceMeasureFamily
          γ.boundaryCompletedResolvedGraph
          (phi4WDoublePrimeCanonicalSupply.index γ.boundaryCompletedResolvedGraph)})
    {δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph}
    (hδ : δ ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily
      γ.boundaryCompletedResolvedGraph B.1) :
    0 < δ.internalEdges.card :=
  phi4WDoublePrimeCoassocLeafSupply.component_internalEdges_card_pos B.2 hδ

/-- **body-595 (Step 1) — the inner forest's canonical-star contraction is family-connected-divergent.**
From body-593's `contract_isConnectedDivergentFor B.2` (the carrier's own `hCD`), on the boundary-completed
ambient. -/
theorem phi4Inner_contract_isConnectedDivergentFor {G : ResolvedFeynmanGraph}
    (γ : ResolvedFeynmanSubgraph G)
    (B : {B : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily
        γ.boundaryCompletedResolvedGraph //
        B ∈ @ResolvedProperForestFiniteIndex.carrier phi4DivergenceMeasureFamily
          γ.boundaryCompletedResolvedGraph
          (phi4WDoublePrimeCanonicalSupply.index γ.boundaryCompletedResolvedGraph)}) :
    ResolvedFeynmanGraphClass.IsConnectedDivergentFor phi4DivergenceMeasureFamily
      phi4PermInvariantDivergenceMeasureFamily
      (@ResolvedAdmissibleSubgraph.contractWithStars phi4DivergenceMeasureFamily
        γ.boundaryCompletedResolvedGraph B.1
        (phi4WDoublePrimeCanonicalSupply.starOf γ.boundaryCompletedResolvedGraph B.1)).toResolvedClass :=
  phi4WDoublePrimeCoassocLeafSupply.contract_isConnectedDivergentFor B.2

/-! ## Step 2 — global + filtered choice carriers -/

/-- **body-595 (Step 2) — the global component-choice carrier.**  A choice of a `phi4LocalChoiceCarrier`
element per component of the outer forest `A` (inner ambient boundary-completed for each component). -/
noncomputable def phi4GlobalChoiceCarrier {G : ResolvedFeynmanGraph}
    (A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G) :=
  (@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G A).attach.pi
    (fun γ => phi4LocalChoiceCarrier γ.1)

/-- **body-595 (Step 2) — the all-right pure primitive choice.**  `Sum.inl false` at every component. -/
noncomputable def phi4ChoicePR {G : ResolvedFeynmanGraph}
    (A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G) :
    (γ : {x // x ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G A}) →
      γ ∈ (@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G A).attach →
        Bool ⊕ (phi4WDoublePrimeCanonicalSupply.summandSupply γ.1.boundaryCompletedResolvedGraph).ForestIdx :=
  fun _ _ => Sum.inl false

/-- **body-595 (Step 2) — the all-left pure primitive choice.**  `Sum.inl true` at every component. -/
noncomputable def phi4ChoicePL {G : ResolvedFeynmanGraph}
    (A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G) :
    (γ : {x // x ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G A}) →
      γ ∈ (@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G A).attach →
        Bool ⊕ (phi4WDoublePrimeCanonicalSupply.summandSupply γ.1.boundaryCompletedResolvedGraph).ForestIdx :=
  fun _ _ => Sum.inl true

/-- **body-595 (Step 2) — the forest (non-pure) split-choice carrier.**  The global choices with the two
pure primitives filtered out — every remaining choice has at least one live inner-forest (`Sum.inr B`) leg. -/
noncomputable def phi4ForestChoiceCarrier {G : ResolvedFeynmanGraph}
    (A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G) :=
  (phi4GlobalChoiceCarrier A).filter (fun p => p ≠ phi4ChoicePR A ∧ p ≠ phi4ChoicePL A)

/-- **body-595 (Step 2) — `phi4ChoicePR` is a valid global choice.** -/
theorem phi4ChoicePR_mem_global {G : ResolvedFeynmanGraph}
    (A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G) :
    phi4ChoicePR A ∈ phi4GlobalChoiceCarrier A := by
  unfold phi4GlobalChoiceCarrier
  rw [Finset.mem_pi]
  exact fun γ hγ => Finset.inl_mem_disjSum.mpr (Finset.mem_univ false)

/-- **body-595 (Step 2) — `phi4ChoicePL` is a valid global choice.** -/
theorem phi4ChoicePL_mem_global {G : ResolvedFeynmanGraph}
    (A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G) :
    phi4ChoicePL A ∈ phi4GlobalChoiceCarrier A := by
  unfold phi4GlobalChoiceCarrier
  rw [Finset.mem_pi]
  exact fun γ hγ => Finset.inl_mem_disjSum.mpr (Finset.mem_univ true)

/-- **body-595 (Step 2) — the two pure primitives are distinct** (given the outer forest has a
component). -/
theorem phi4ChoicePR_ne_PL {G : ResolvedFeynmanGraph}
    (A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G)
    (hne : (@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G A).Nonempty) :
    phi4ChoicePR A ≠ phi4ChoicePL A := by
  obtain ⟨v, hv⟩ := hne
  intro h
  have hfalse := congrFun (congrFun h ⟨v, hv⟩) (Finset.mem_attach _ _)
  simp only [phi4ChoicePR, phi4ChoicePL, Sum.inl.injEq] at hfalse
  exact absurd hfalse Bool.false_ne_true

/-- **body-595 (Step 2) — the forest-choice membership iff.** -/
theorem mem_phi4ForestChoiceCarrier {G : ResolvedFeynmanGraph}
    (A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G)
    {p : (γ : {x // x ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G A}) →
        γ ∈ (@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G A).attach →
          Bool ⊕
            (phi4WDoublePrimeCanonicalSupply.summandSupply γ.1.boundaryCompletedResolvedGraph).ForestIdx} :
    p ∈ phi4ForestChoiceCarrier A ↔
      p ∈ phi4GlobalChoiceCarrier A ∧ p ≠ phi4ChoicePR A ∧ p ≠ phi4ChoicePL A := by
  unfold phi4ForestChoiceCarrier
  exact Finset.mem_filter

/-! ## Step 3 — split-choice types (the live inner membership travels inside the TYPE) -/

/-- **body-595 (Step 3) — a resolved coassoc split choice.**  A live outer W″ forest `outer` (with its
liveness `outer_mem`) together with a global component choice.  Each `Sum.inr B` leg of `choice` has type
`{B // B ∈ (index γ.boundaryCompletedResolvedGraph).carrier}` (via `phi4LocalChoiceCarrier`), so the split-
choice TYPE itself carries the LIVE inner membership on the boundary-completed ambient. -/
structure Phi4ResolvedCoassocSplitChoice (G : ResolvedFeynmanGraph) where
  /-- The outer W″ forest. -/
  outer : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G
  /-- The outer forest is a live W″ carrier member (retains `outer.elements.Nonempty` via body-593). -/
  outer_mem : outer ∈ @ResolvedProperForestFiniteIndex.carrier phi4DivergenceMeasureFamily G
    (phi4WDoublePrimeCanonicalSupply.index G)
  /-- A global component choice: per component, a `phi4LocalChoiceCarrier` element on the boundary-completed
  inner ambient (its `Sum.inr` leg is a live inner carrier member). -/
  choice : (γ : {x // x ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G outer}) →
    γ ∈ (@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G outer).attach →
      Bool ⊕ (phi4WDoublePrimeCanonicalSupply.summandSupply γ.1.boundaryCompletedResolvedGraph).ForestIdx
  /-- The choice is a valid global choice. -/
  choice_mem : choice ∈ phi4GlobalChoiceCarrier outer

/-- **body-595 (Step 3) — a filtered (forest, non-pure) resolved coassoc split choice.**  A split choice
whose global choice is not one of the two pure primitives — so at least one component is a LIVE inner
forest `Sum.inr B` on the boundary-completed ambient. -/
structure Phi4FilteredCoassocSplitChoice (G : ResolvedFeynmanGraph) extends
    Phi4ResolvedCoassocSplitChoice G where
  /-- The choice avoids both pure primitives (lives in the forest-choice carrier). -/
  choice_filtered : toPhi4ResolvedCoassocSplitChoice.choice ∈
    phi4ForestChoiceCarrier toPhi4ResolvedCoassocSplitChoice.outer

/-! ## Step 4 — pure-choice partition (generic weight; `outer_nonempty` DERIVED, not fielded) -/

/-- **body-595 (Step 4) — the pure-choice partition of the global choice sum.**  The full component-choice
sum splits off the two pure primitives (`phi4ChoicePR` / `phi4ChoicePL`) from the forest block, for any
`AddCommMonoid`-valued weight `f`.

KEY IMPROVEMENT over the old abstract `pure_choice_partition`: the nonemptiness `A.elements.Nonempty` is
DERIVED here from body-593's `carrier_isProperForest hA` (an `IsProperForest` conjunct), NOT fielded as a
measure-level `outer_nonempty` obligation.  No measure leaf. -/
theorem phi4_pure_choice_partition {M : Type*} [AddCommMonoid M] {G : ResolvedFeynmanGraph}
    (A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G)
    (hA : A ∈ @ResolvedProperForestFiniteIndex.carrier phi4DivergenceMeasureFamily G
      (phi4WDoublePrimeCanonicalSupply.index G))
    (f : ((γ : {x // x ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G A}) →
        γ ∈ (@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G A).attach →
          Bool ⊕
            (phi4WDoublePrimeCanonicalSupply.summandSupply γ.1.boundaryCompletedResolvedGraph).ForestIdx) →
        M) :
    ∑ p ∈ phi4GlobalChoiceCarrier A, f p
      = f (phi4ChoicePR A) + f (phi4ChoicePL A) + ∑ p ∈ phi4ForestChoiceCarrier A, f p := by
  have hpf : @ResolvedAdmissibleSubgraph.IsProperForest phi4DivergenceMeasureFamily G A :=
    phi4WDoublePrimeCoassocLeafSupply.carrier_isProperForest hA
  have hne : (@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G A).Nonempty :=
    @ResolvedAdmissibleSubgraph.isNonempty_of_isProperForest phi4DivergenceMeasureFamily G A hpf
  exact sum_extract_two _ f (phi4ChoicePR_mem_global A) (phi4ChoicePL_mem_global A)
    (phi4ChoicePR_ne_PL A hne)

end GaugeGeometry.QFT.Combinatorial
