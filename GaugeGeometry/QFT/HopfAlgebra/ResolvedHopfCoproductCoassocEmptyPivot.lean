import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocOutputBoundaryCovers

/-!
# R-6c-body-84 — the empty-forest pivot: Case A (∅ excluded), OUTPUT boundaries are cover-external

Eighty-fourth genuine-body step, resolving the `∅`-pivot that bodies 78–83 hinged on.  A carrier scout settles
it: the empty forest is EXCLUDED from `D.carrier G`, so both OUTPUT boundaries are cover-external — Case A.

## The classification (Case A, confirmed)

* `D.carrier` is an abstract field with only `hCD` (`ResolvedHopfCoproductSupply`), so nonemptiness is not forced
  by the type;
* BUT the canonical carrier (`ResolvedPayloadModel` / `ResolvedUniquePayloadModel`) is
  `properDisjointAdmissibleDivergentSubgraphs.filter (0 < ·.complementEdges.card)`, and `IsProperForest` requires
  `0 < complementEdges.card` — which EXCLUDES the empty forest (`ResolvedSubGraph.IsProperForest`);
* `ResolvedAdmissibleSubgraph.elements` CAN be `∅` (no nonemptiness field), and `contractWithStars ∅ = G` (empty
  contraction is the whole graph, `rightTerm ∅ = X_G`), but the empty forest is never PUT in the carrier.

So `∅ ∉ D.carrier G`, and `selectedOuterOf : SplitChoice → {A // A ∈ carrier}` (via `selectedOuter_mem`) NEVER
returns the empty forest.

## The consequence: OUTPUT boundaries are cover-external

The all-right-primitive split term is `resolvedSplitChoiceTerm ⟨A, p₀⟩ = 1 ⊗ (leftTerm A ⊗ rightTerm A)`
(body-65, PROVED) — outer slot `1 = leftTerm ∅`.  Under `term_eq` this would need `selectedOuter ⟨A, p₀⟩ = ∅`;
but `∅ ∉ carrier`, so NO carrier forest has `leftTerm = 1`.  Hence the all-right-primitives cannot be `term_eq`
/ cover images with the proper carrier — the IMAGE boundary `1 ⊗ forestSum G = ∑_A splitTerm ⟨A, p₀⟩` (body-70)
is COVER-EXTERNAL, exactly as the BRANCH boundary `assoc(forestSum G ⊗ 1)` is (body-70, not any split term).
Both OUTPUT boundaries live OUTSIDE the split-choice cover:

* IMAGE: `1 ⊗ forestSum G` (`= ∑_A resolvedSplitChoiceTerm ⟨A, allRightPrimitive⟩`, body-70);
* BRANCH: `assoc(forestSum G ⊗ 1)` (`= ∑_A leftTerm A ⊗ (rightTerm A ⊗ 1)`, body-70).

`resolved_output_boundaries_external` bundles both.

## What this settles for OUTPUT

Case A ⇒ the split-choice cover `∑ cover` carries only the TAILS (no boundary): both boundaries are the
primitive-outer parts, handled OUTSIDE the cover.  So:

* body-78's "boundary-IN on both sides at the sum level" is INCORRECT — it put the `∅`-fiber boundary inside the
  cover, but `∅ ∉ carrier` means there is no `∅`-fiber;
* body-80/81/82/83's IMAGE `isBoundaryOuter`/`∅`-fiber machinery has no `∅` outer to attach to (the boundary set
  is empty in the carrier), so `strict_summand_cover` should hold for ALL carrier outers (all nonempty) and the
  boundary is a SEPARATE additive term, matching body-76/77's tails-only branch form;
* the coassociativity `regroupImageSum = regroupBranchSum` is `image_boundary + image_tail = branch_boundary +
  branch_tail`; the cover `∑ cover` equals the base-outer fibered LEFT tails `∑_A coassocLeftTail A =
  coassocLeftTail(forestSum)` (body-76, provable via the definition + `coassocLeftTail_eq_splitChoiceTermSum`),
  and the two boundaries plus the identification of `∑ cover` with the image tails is the genuine coassoc content.

So the canonical OUTPUT form is the TAILS-ONLY cover (body-76/77) plus the two cover-external primitive-outer
boundaries — NOT body-78's boundary-IN reconciliation.  The IMAGE per-`A` `strict_summand_cover` (body-80)
stands for all (nonempty) carrier outers; the `∅`-fiber bodies (81/82/83) are vacuous under Case A and are
superseded.

Per the HALT, this is a classification (no re-wiring); the boundary structure is proved (body-70 bundle); the
carrier fact is from the canonical model, not re-derived here.

Landed:

* `resolved_output_boundaries_external` — the two OUTPUT boundaries in split-term / primitive-outer form
  (body-70 bundle), the cover-external primitives under Case A.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

set_option linter.unusedSectionVars false

/-- **R-6c-body-84 — the two OUTPUT boundaries (cover-external, Case A).**  The IMAGE boundary `1 ⊗ forestSum G`
is the all-right-primitive split-term sum; the BRANCH boundary `assoc(forestSum G ⊗ 1)` is the primitive-outer
sum.  Under Case A (`∅ ∉ carrier`) both live OUTSIDE the split-choice cover. -/
theorem resolved_output_boundaries_external :
    ((1 : ResolvedHopfH) ⊗ₜ[ℚ] (D.supply G).sum
        = ∑ A ∈ (D.supply G).forestCarrier,
            D.resolvedSplitChoiceTerm (⟨A, fun _ _ => Sum.inl false⟩ : ResolvedCoassocSplitChoice D G))
      ∧ ((Algebra.TensorProduct.assoc ℚ ℚ ℚ ResolvedHopfH ResolvedHopfH ResolvedHopfH).toAlgHom
            ((D.supply G).sum ⊗ₜ[ℚ] (1 : ResolvedHopfH))
          = ∑ A ∈ (D.supply G).forestCarrier,
              (D.supply G).leftTerm A ⊗ₜ[ℚ] ((D.supply G).rightTerm A ⊗ₜ[ℚ] (1 : ResolvedHopfH))) :=
  ⟨resolved_image_boundary_eq_allRightPrimitive_sum, resolved_branch_boundary_eq_primitive_outer⟩

end GaugeGeometry.QFT.Combinatorial
