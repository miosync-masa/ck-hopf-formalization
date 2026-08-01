import GaugeGeometry.QFT.HopfAlgebra.Phi4StableSummandAgreement

/-!
# QFT-R1-body-641 — the STABLE finite-sum OWNERSHIP audit (finite index + the sole remaining obligation)

Body-640 delivered the pointwise `stableForestBlockForward_summand_agree` on the STABLE carrier.  A finite
sum-of-terms identity (a `Finset.sum_bij` over the stable split-choice index and the raw inverse codomain)
would finish the stable coassociativity assembly — BUT the old whole-forest-block `Equiv`
(`phi4WTriplePrime_forestBlockEquiv`, body-623) CANNOT be reused as the bijection witness: its SOURCE is the
old `Phi4EdgeCompleteFilteredCoassocSplitChoice G`, whose per-component inner forest lives over the naive
`γ.boundaryCompletedResolvedGraph`, while the stable source `StablePhi4MixedSplitChoice G hSt` carries its
inner forest as `StableLocalForestIdx γ` over the ZERO-re-encode `stableLocalBoundaryCompletedGraph γ`.
Body-625's class-level ID-profile no-go GUARANTEES these two completions differ, so the two source types are
NOT defeq and NO `cast` / `HEq` / graph-data transport can bridge them.

This body therefore completes the finite-index OWNERSHIP **without fabricating a sum**: it packages the stable
finite carriers, emits a GENUINE (type-packaging) `Equiv` between the explicit finite source index and the
stable mixed split-choice, proves the stable forward map LANDS in the explicit finite target, restates
body-640's summand agreement in the finite-index context, records the old-`Equiv` incompatibility as a TYPE
AUDIT, and fixes the SOLE remaining obligation to a single named `Function.Bijective stableForestBlockForward`.

## Steps
* **Step 1 — local finite carrier.**  `stablePhi4LocalChoiceCarrier hSt γ : Finset (Bool ⊕ StableLocalForestIdx γ)`,
  the disjoint sum of `Finset.univ` (the two primitive `Bool` legs) with the `.attach` of the live W‴ inner
  forest index over the STABLE completion `stableLocalBoundaryCompletedGraph γ`.
* **Step 2 — global / mixed carrier.**  `stablePhi4GlobalChoiceCarrier` (the full component-choice function
  space via `Finset.pi`), the pure-RIGHT `stablePhi4ChoicePR` and pure-LEFT `stablePhi4ChoicePL` filters, and
  `stablePhi4MixedChoiceCarrier` = the global carrier with the all-RIGHT and all-LEFT choices filtered out
  (multiplicity-exact, no dedup — the filter predicate is exactly the not-all-RIGHT ∧ not-all-LEFT owned by
  `StablePhi4MixedSplitChoice`).
* **Step 3 — explicit finite source + the source `Equiv` (packaging only).**  `StablePhi4MixedChoiceFiniteIndex`
  (a Σ over `↥(phi4WTriplePrimeIndex G)` of the mixed carrier) and the GENUINE `Equiv`
  `stablePhi4MixedChoiceFiniteIndexEquiv : StablePhi4MixedChoiceFiniteIndex G hSt ≃ StablePhi4MixedSplitChoice G hSt`
  — pure bundle/unbundle of `outer` + `outer_mem` + `choice` + the not-all-LEFT / not-all-RIGHT witnesses.
  ZERO new geometry.
* **Step 4 — explicit finite target + finite forward anchor.**  `stablePhi4InverseCodomainCarrier` (a
  `Finset.sigma` enumerating `Phi4WTriplePrimeInverseCodomain G`), the landing lemma
  `stableForestBlockForward_mem_inverseCodomainCarrier`, and the pointwise anchor
  `stableFiniteForward_summand_agree` (= body-640's `stableForestBlockForward_summand_agree`, restated here).
* **Step 5 — compatibility verdict + the sole remaining obligation.**  A TYPE AUDIT (docstring + `#check`-shaped
  comment, NOT a consumed term) that `phi4WTriplePrime_forestBlockEquiv` is INAPPLICABLE to the stable finite
  source, hence `sum_bij` is LEFT UNASSERTED and the remaining obligation is fixed to the single named `Prop`
  `StablePhi4ForestBlockForwardBijective G hSt := Function.Bijective stableForestBlockForward`.

## Compatibility verdict (Step 5, TYPE AUDIT — no term consumed)
The old body-623 whole-forest-block equivalence has type
```
phi4WTriplePrime_forestBlockEquiv :
  Phi4EdgeCompleteFilteredCoassocSplitChoice G ≃ Phi4WTriplePrimeInverseCodomain G
```
Its domain `Phi4EdgeCompleteFilteredCoassocSplitChoice G` is the OLD split choice (inner forests over
`γ.boundaryCompletedResolvedGraph`).  The stable finite source is `StablePhi4MixedSplitChoice G hSt`
(inner forests `StableLocalForestIdx γ` over `stableLocalBoundaryCompletedGraph γ`).  Body-625's no-go
proves these completions carry different boundary-ID profiles, so the two domains are NOT defeq: the old
`Equiv` cannot be `.toFun`/`.symm`-applied nor cast onto the stable source.  Therefore the finite `sum_bij`
is NOT emitted here; the bijectivity of `stableForestBlockForward` is fixed as the single named obligation
`StablePhi4ForestBlockForwardBijective` for the next body (NOT proved here).

## HALT / red lines
Body-625's no-go, bodies 629-640, the old carrier, and every existing file are UNEDITED.  ZERO consumption of
`phi4WTriplePrime_forestBlockEquiv` as a term (docstring / `#check`-audit only); ZERO old/stable choice adapter;
ZERO `cast` / `HEq` / graph-data transport `▸` (Prop-membership `▸` only); ZERO orbit quotient / `toFinset` /
dedup; NO `Finset.sum_bij` / sum equality / alpha / coassoc; the `Function.Bijective stableForestBlockForward`
obligation is a `def` Prop, NOT proved.  ZERO new `class` / permanent `instance` (one file-local `local
instance` for the φ⁴ family; `StablePhi4MixedChoiceFiniteIndex` is a Σ-`def`, the source `Equiv` is a `def`);
ZERO forbidden divergence class in any declaration TYPE; ZERO `sorry` / `admit` / `native_decide`.  Axiom-clean
(`propext`, `Classical.choice`, `Quot.sound`).
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct
open scoped Classical

open ResolvedFeynmanSubgraph

variable {G : ResolvedFeynmanGraph}

/-- The concrete φ⁴ divergence measure family, registered file-locally (providable instance, NO forbidden
class). -/
noncomputable local instance instPhi4DivergenceMeasureFamily641 : (H : FeynmanGraph) → DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

/-! ## Step 1 — the local finite choice carrier -/

/-- **body-641 (Step 1) — the local finite choice carrier.**  Over one outer component `γ`, the finite set of
per-component stable choices: the two primitive `Bool` legs (`Finset.univ`) disjointly summed with the `.attach`
of the live W‴ inner-forest index over the STABLE completion `stableLocalBoundaryCompletedGraph γ` (NOT the
naive `γ.boundaryCompletedResolvedGraph`).  Multiplicity-exact — no dedup. -/
noncomputable def stablePhi4LocalChoiceCarrier (hSt : StableResolvedBoundaryIds G)
    (γ : ResolvedFeynmanSubgraph G) : Finset (Bool ⊕ StableLocalForestIdx γ) :=
  Finset.univ.disjSum (phi4WTriplePrimeIndex (stableLocalBoundaryCompletedGraph γ)).attach

/-! ## Step 2 — the global / mixed choice carriers -/

/-- **body-641 (Step 2) — the per-outer component-choice function type** (exactly
`StablePhi4ResolvedSplitChoice.choice`'s codomain): a dependent function assigning each outer component `γ` a
local stable choice `Bool ⊕ StableLocalForestIdx γ.1`. -/
abbrev StablePhi4ComponentChoice (A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G) : Type :=
  (γ : {x // x ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G A}) →
    γ ∈ (@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G A).attach →
      Bool ⊕ StableLocalForestIdx γ.1

/-- **body-641 (Step 2) — the global choice carrier.**  The FULL component-choice function space over an outer
forest `A`, enumerated with `Finset.pi`: each component independently ranges over its local finite carrier.
Multiplicity-exact — the `.attach` product structure is preserved. -/
noncomputable def stablePhi4GlobalChoiceCarrier (hSt : StableResolvedBoundaryIds G)
    (A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G) :
    Finset (StablePhi4ComponentChoice A) :=
  (@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G A).attach.pi
    (fun γ => stablePhi4LocalChoiceCarrier hSt γ.1)

/-- **body-641 (Step 2) — every component-choice function lands in the global carrier** (the local carriers
cover their whole `Bool ⊕ StableLocalForestIdx` fibre). -/
theorem stablePhi4_mem_globalChoiceCarrier (hSt : StableResolvedBoundaryIds G)
    (A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G)
    (c : StablePhi4ComponentChoice A) :
    c ∈ stablePhi4GlobalChoiceCarrier hSt A := by
  unfold stablePhi4GlobalChoiceCarrier
  refine Finset.mem_pi.mpr (fun γ hγ => ?_)
  unfold stablePhi4LocalChoiceCarrier
  rcases c γ hγ with b | B
  · exact Finset.inl_mem_disjSum.mpr (Finset.mem_univ b)
  · exact Finset.inr_mem_disjSum.mpr (Finset.mem_attach _ B)

/-- **body-641 (Step 2) — the pure-RIGHT choices** (`PR`): the all-`Sum.inl false` component choices of the
global carrier — filtered OUT of the mixed carrier. -/
noncomputable def stablePhi4ChoicePR (hSt : StableResolvedBoundaryIds G)
    (A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G) :
    Finset (StablePhi4ComponentChoice A) :=
  (stablePhi4GlobalChoiceCarrier hSt A).filter (fun c => ∀ a hatt, c a hatt = Sum.inl false)

/-- **body-641 (Step 2) — the pure-LEFT choices** (`PL`): the all-`Sum.inl true` component choices of the
global carrier — filtered OUT of the mixed carrier. -/
noncomputable def stablePhi4ChoicePL (hSt : StableResolvedBoundaryIds G)
    (A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G) :
    Finset (StablePhi4ComponentChoice A) :=
  (stablePhi4GlobalChoiceCarrier hSt A).filter (fun c => ∀ a hatt, c a hatt = Sum.inl true)

/-- **body-641 (Step 2) — the mixed choice carrier.**  The global carrier with the pure-RIGHT (`PR`) and
pure-LEFT (`PL`) choices removed: exactly the not-all-RIGHT ∧ not-all-LEFT region owned by
`StablePhi4MixedSplitChoice` (base `choice_nontrivial` ∧ the subtype not-all-LEFT).  Multiplicity-exact — no
dedup. -/
noncomputable def stablePhi4MixedChoiceCarrier (hSt : StableResolvedBoundaryIds G)
    (A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G) :
    Finset (StablePhi4ComponentChoice A) :=
  (stablePhi4GlobalChoiceCarrier hSt A).filter
    (fun c => (∃ a hatt, c a hatt ≠ Sum.inl false) ∧ (∃ a hatt, c a hatt ≠ Sum.inl true))

/-- **body-641 (Step 2) — membership in the mixed carrier** is exactly the not-all-RIGHT ∧ not-all-LEFT
witnesses (global membership is automatic). -/
theorem mem_stablePhi4MixedChoiceCarrier {hSt : StableResolvedBoundaryIds G}
    {A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G}
    {c : StablePhi4ComponentChoice A} :
    c ∈ stablePhi4MixedChoiceCarrier hSt A ↔
      (∃ a hatt, c a hatt ≠ Sum.inl false) ∧ (∃ a hatt, c a hatt ≠ Sum.inl true) := by
  unfold stablePhi4MixedChoiceCarrier
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨stablePhi4_mem_globalChoiceCarrier hSt A c, h⟩⟩

/-! ## Step 3 — the explicit finite source + the source `Equiv` (packaging only) -/

/-- **body-641 (Step 3) — the explicit finite source index.**  A Σ over the outer W‴ index `↥(phi4WTriplePrimeIndex G)`
of the per-outer mixed choice carrier.  A `def` / Σ-abbrev (NOT a structure). -/
def StablePhi4MixedChoiceFiniteIndex (G : ResolvedFeynmanGraph) (hSt : StableResolvedBoundaryIds G) : Type :=
  Σ A : ↥(phi4WTriplePrimeIndex G), {p // p ∈ stablePhi4MixedChoiceCarrier hSt A.1}

/-- **body-641 (Step 3, HEADLINE) — the source `Equiv` (TYPE PACKAGING ONLY).**  The explicit finite source
index `StablePhi4MixedChoiceFiniteIndex G hSt` is genuinely equivalent to the stable mixed split choice
`StablePhi4MixedSplitChoice G hSt`: `toFun` bundles the Σ's outer forest + membership + component-choice
function into a `StablePhi4ResolvedSplitChoice`, reading the not-all-RIGHT witness as `choice_nontrivial` and
the not-all-LEFT witness as the mixed subtype property; `invFun` unbundles them back.  ZERO new geometry — the
inverse laws are `rfl` (structure η + proof irrelevance on the finite-membership / existential witnesses). -/
noncomputable def stablePhi4MixedChoiceFiniteIndexEquiv (hSt : StableResolvedBoundaryIds G) :
    StablePhi4MixedChoiceFiniteIndex G hSt ≃ StablePhi4MixedSplitChoice G hSt where
  toFun := fun x =>
    ⟨{ outer := x.1.1
       outer_mem := x.1.2
       choice := x.2.1
       choice_nontrivial := (mem_stablePhi4MixedChoiceCarrier.mp x.2.2).1 },
      (mem_stablePhi4MixedChoiceCarrier.mp x.2.2).2⟩
  invFun := fun s =>
    ⟨⟨s.1.outer, s.1.outer_mem⟩,
      ⟨s.1.choice, mem_stablePhi4MixedChoiceCarrier.mpr ⟨s.1.choice_nontrivial, s.2⟩⟩⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-! ## Step 4 — the explicit finite target + finite forward anchor -/

/-- **body-641 (Step 4) — the explicit finite target index.**  A `Finset.sigma` enumerating the RAW inverse
codomain `Phi4WTriplePrimeInverseCodomain G`: the `.attach` of the outer W‴ index, and for each outer forest
`A` the `.attach` of the inner W‴ index over `A.contractWithStars (starOf G A)`. -/
noncomputable def stablePhi4InverseCodomainCarrier (G : ResolvedFeynmanGraph) :
    Finset (Phi4WTriplePrimeInverseCodomain G) :=
  (phi4WTriplePrimeIndex G).attach.sigma
    (fun A => (phi4WTriplePrimeIndex
      (A.1.contractWithStars (phi4WTriplePrimeCanonicalSupply.starOf G A.1))).attach)

/-- **body-641 (Step 4) — the stable forward map LANDS in the explicit finite target.**  Both index levels are
full `.attach`s, so the forward package is a member by `Finset.mem_attach` twice. -/
theorem stableForestBlockForward_mem_inverseCodomainCarrier {hSt : StableResolvedBoundaryIds G}
    (s : StablePhi4MixedSplitChoice G hSt) :
    stableForestBlockForward s ∈ stablePhi4InverseCodomainCarrier G := by
  unfold stablePhi4InverseCodomainCarrier
  exact Finset.mem_sigma.mpr ⟨Finset.mem_attach _ _, Finset.mem_attach _ _⟩

/-- **body-641 (Step 4) — the finite-index pointwise summand agreement.**  Body-640's
`stableForestBlockForward_summand_agree` restated in the finite-index context: the stable split-choice branch
weight IS the stable quotient-triple weight at the stable forward package.  Read directly — NO new geometry. -/
theorem stableFiniteForward_summand_agree {hSt : StableResolvedBoundaryIds G}
    (s : StablePhi4MixedSplitChoice G hSt) :
    stableSplitChoiceTerm s.1 = stableQuotientTripleTerm hSt (stableForestBlockForward s) :=
  stableForestBlockForward_summand_agree s

/-! ## Step 5 — the compatibility verdict + the sole remaining obligation -/

-- COMPATIBILITY AUDIT (TYPE ONLY — no term consumed).  The old body-623 equivalence
--   `#check @phi4WTriplePrime_forestBlockEquiv`
--     : Phi4EdgeCompleteFilteredCoassocSplitChoice G ≃ Phi4WTriplePrimeInverseCodomain G
-- has SOURCE `Phi4EdgeCompleteFilteredCoassocSplitChoice G` (inner forests over the naive
-- `γ.boundaryCompletedResolvedGraph`), which is NOT defeq to the stable finite source
-- `StablePhi4MixedSplitChoice G hSt` (inner forests `StableLocalForestIdx γ` over
-- `stableLocalBoundaryCompletedGraph γ`) — body-625's ID-profile no-go.  Hence the old `Equiv` is INAPPLICABLE
-- here (no `.toFun`/`.symm`/`cast`), the `sum_bij` is LEFT UNASSERTED, and the remaining obligation is the
-- single named `Prop` below (a `def`, NOT proved in this body).

/-- **body-641 (Step 5, the SOLE remaining obligation) — the stable forward map is bijective.**  The named
`Prop` fixing the one open goal for the next body: `stableForestBlockForward` is a bijection from the stable
mixed split choice onto the raw inverse codomain.  A `def` Prop — NOT proved here (and NOT dischargeable via the
old body-623 `Equiv`, whose source is not defeq to the stable source). -/
def StablePhi4ForestBlockForwardBijective (G : ResolvedFeynmanGraph)
    (hSt : StableResolvedBoundaryIds G) : Prop :=
  Function.Bijective
    (stableForestBlockForward : StablePhi4MixedSplitChoice G hSt → Phi4WTriplePrimeInverseCodomain G)

end GaugeGeometry.QFT.Combinatorial
