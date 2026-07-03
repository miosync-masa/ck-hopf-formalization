import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocDirectBoundaryTail

/-!
# R-6c-body-90 — boundary_tail_step scout: the coassoc is a DIRECT nested-forest bijection (no induction)

Ninetieth genuine-body step, scouting the induction STEP `boundary_tail_step` (body-89) against the flat
coassoc template.  The finding: the flat CK/Zimmermann forest argument is a DIRECT finite bijection — NO
induction on graph size.  So `boundary_tail_step` needs no IH; the genuine content is a single nested-forest
`Finset.sum_bij`.  body-89's induction scaffold is superfluous (harmless).

## The flat argument is direct (bijection-based, no induction)

The flat coassoc (`Coassoc`) proves the generator identity `(Δ ⊗ 1) Δ(X g) = (1 ⊗ Δ) Δ(X g)` by a DIRECT
finite chain (no `termination_by` / well-founded recursion):

* `coassoc_forest_LHS_eq` / `coassoc_forest_RHS_eq` — expand each side into FIVE named terms.  With
  `forestTermA/B/D` the primitives, `forestTermC = ∑_A A ⊗ ([Γ/A] ⊗ 1)` (= branch boundary `assoc(forestSum ⊗
  1)`), `forestTermE = ∑_A assoc(Δ(A) ⊗ [Γ/A])` (= `coassocLeftTail`), `forestTermE2 = ∑_A 1 ⊗ (A ⊗ [Γ/A])` (=
  image boundary `1 ⊗ forestSum`), `forestTermF = ∑_A A ⊗ Δ([Γ/A])` (= `coassocRightTail`);
* `coassoc_forest_main_terms_of_core (hCore : forestTermE3 = forestTermF3) : forestTermC + forestTermE =
  forestTermE2 + forestTermF` — the boundaries cancel (`abel`), reducing to the CORE `forestTermE3 =
  forestTermF3`;
* the core `forestTermE3 = forestTermF3` = `forestTermEComponentGenerators = forestTermFQuotientGenerators`,
  matched by a `Finset.sum_bij` (flat `forestComponentChoiceSigmaTerm_eq_quotientForestSigmaTerm_of_factorization`)
  — the classical NESTED-FOREST bijection: each LHS component choice `(A, p)` ↔ a unique RHS quotient-forest
  pair `(outer A, inner quotient forest B)`.  NO recursion.

## Consequence for `boundary_tail_step`

`boundary_tail_eq` (body-88, `= regroupImageSum = regroupBranchSum`) is EXACTLY the forest core `forestTermC +
forestTermE = forestTermE2 + forestTermF` (the primitives `A/B/D` are `coassocPrimitivePart`, already matched by
body-88's `lhs/rhsExpansion`).  Since the flat matching is DIRECT, `boundary_tail_step` (body-89) need NOT use
its induction hypothesis — it can prove the reindex for `G` directly from the nested-forest bijection.  So the
induction scaffold (body-89) is superfluous: the resolved coassoc is a DIRECT bijection.

## The genuine content: one nested-forest `sum_bij`

`ResolvedForestMatchingSupply.forest_matching` fields the reindex directly (the resolved analogue of the flat
core bijection).  Its resolved decomposition is: expand `regroupImageSum` via `coassocRightTail_forestSummand`
(RIGHT: `Δᵣ` on the quotient generator, `coproduct_rightTerm`) and `regroupBranchSum` via
`coassocLeftTail_eq_splitChoiceTermSum` (LEFT: `Δᵣ` on the component product, `coproduct_resolvedForestLeftTerm`),
then match the resulting sums by the `Finset.sum_bij` `(A, component choice) ↔ (A, quotient sub-forest)` — the
genuine remaining leaf (the flat `…_of_factorization` ported to the resolved carrier).

`toDirectBoundaryTailCoassocSupply` connects `forest_matching` straight to body-88's `coassoc_gen`, bypassing
the (superfluous) induction of body-89.

Per the HALT: the nested-forest `sum_bij` is NOT proved (it is `forest_matching`); the direct (non-inductive)
structure is fixed; the flat template (`Coassoc` five-term expansion + `sum_bij` core) is identified; no
star-allocation / retarget detail is entered.

Landed:

* `ResolvedForestMatchingSupply D` — the direct nested-forest matching reindex (`forest_matching`);
* `.toDirectBoundaryTailCoassocSupply` / `.coassoc_gen` — `coassoc_gen`, DIRECT (no induction).

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData}

set_option linter.unusedSectionVars false

/-- **R-6c-body-90 — the direct nested-forest matching reindex.**  The forest core `regroupImageSum x =
regroupBranchSum x` on every generator — the resolved analogue of the flat `forestTermC + forestTermE =
forestTermE2 + forestTermF`, proved by the nested-forest `Finset.sum_bij` (component choice ↔ quotient
sub-forest), DIRECTLY (no induction, body-89 superfluous). -/
structure ResolvedForestMatchingSupply (D : ResolvedCoproductProperForestData) where
  /-- The reindex, matched by the nested-forest bijection (the genuine CK content). -/
  forest_matching : ∀ x : ResolvedHopfGen, D.regroupImageSum x = D.regroupBranchSum x

/-- **R-6c-body-90 — to body-88's direct supply** (bypassing body-89's induction). -/
def ResolvedForestMatchingSupply.toDirectBoundaryTailCoassocSupply
    (S : ResolvedForestMatchingSupply D) : ResolvedDirectBoundaryTailCoassocSupply D where
  boundary_tail_eq := S.forest_matching

/-- **R-6c-body-90 — `coassoc_gen` from the direct forest matching** (no induction). -/
theorem ResolvedForestMatchingSupply.coassoc_gen
    (S : ResolvedForestMatchingSupply D) (x : ResolvedHopfGen) :
    D.coassocLeft (MvPolynomial.X x) = D.coassocRight (MvPolynomial.X x) :=
  S.toDirectBoundaryTailCoassocSupply.coassoc_gen x

end GaugeGeometry.QFT.Combinatorial
