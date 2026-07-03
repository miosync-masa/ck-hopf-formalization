import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocImageQuotientCoverBody
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocBranchCoverBody
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocOutputFiberAgreementCapstone

/-!
# R-6c-body-67 — the OUTPUT cover asymmetry map (capstone + consolidation)

Sixty-seventh genuine-body step, a CONSOLIDATION fixing the OUTPUT (outer-forest ↔ splitPhi-cover) reindex in
its final ASYMMETRIC form after bodies 64–66.  The two OUTPUT leaves are structurally different, and that
asymmetry is the honest final shape — recorded here as a docstring map plus one thin capstone from the two
primitive covers to `coassoc_gen`.

## The two OUTPUT leaves — and why they differ

Both sides reindex the outer-forest summand for `A` onto `F`'s split-choice fibers, but the boundary term
`(forest summand A)` gets adjoined on OPPOSITE tensor slots, and only one slot is reachable by a split choice:

**RIGHT / IMAGE** — the boundary IS a split term, so the per-`A` cover closes:
```text
image_cover
  ⇐ all-right-primitive boundary lemma  resolvedSplitChoiceTerm ⟨A, p₀⟩ = 1 ⊗ (leftTerm A ⊗ rightTerm A)  (PROVED, body-65)
  ⇐ coproduct_rightTerm rewrite         (primitive + quot sum) = Δᵣ(rightTerm A)                            (PROVED, body-66)
  ⇐ image_quotient_fiber                boundary + leftTerm A ⊗ Δᵣ(rightTerm A) = selectedOuter=A fibers    (PRIMITIVE)
```
The residue is the second-coproduct de-contraction `leftTerm A ⊗ Δᵣ(rightTerm A)` covered by the
`selectedOuter (imageOf s) = A` fibers — the `right_eq` quotient geometry.

**LEFT / BRANCH** — the boundary is NOT a split term, so no per-`A` pure partition exists:
```text
branch_cover
  ⇐ coassocLeftTail_eq_splitChoiceTermSum  ∑ p ∈ piCarrier A, splitTerm ⟨A,p⟩ = coassocLeftTail A  (PROVED, body-61)
  ⇐ branch_cover / branch_cover_direct     branch summand A = base-outer-A fibers                  (PRIMITIVE)
```
The boundary `leftTerm A ⊗ (rightTerm A ⊗ 1)` puts `1` in the RIGHT tensor slot, which no split-choice term
reaches (every split term has `rightTerm A` there; body-64).  So the LEFT leaf is fielded WHOLE — its boundary
escapes the base-outer fibration.

**The asymmetry, stated once:** the RIGHT boundary is a right-primitive choice (in-fibration); the LEFT boundary
is a left-slot `1` (out-of-fibration).  This is intrinsic to `(1 ⊗ Δᵣ) ∘ Δᵣ` vs `(Δᵣ ⊗ 1) ∘ Δᵣ` and is kept in
the final proof shape — not smoothed away.

## The two OUTPUT primitives

`ResolvedOutputCoverPrimitiveSupply D` carries the representative family plus, per generator:

* `imageQuotient x : ResolvedImageQuotientFiberSupply (grand x)` — the RIGHT second-coproduct de-contraction (body-66);
* `branchDirect x : ResolvedBranchCoverDirectSupply (grand x)` — the LEFT direct base-outer cover (body-64).

Everything else in the OUTPUT chain is PROVED.  So the OUTPUT reindex's primitive leaves are now EXACTLY
`image_quotient_fiber` + `branch_cover_direct`.

## The chain

`toOutputAgreementFamilySupply` threads each primitive through its proved adapters (RIGHT: body-66 → 65 → 62;
LEFT: body-64 → 61) into body-60's `ResolvedOutputAgreementFamilySupply`; `coassoc_gen` is body-60's capstone.

Per the HALT, neither cover proof is entered; adapter + documentation only.

Landed:

* `ResolvedOutputCoverPrimitiveSupply D` — the OUTPUT-reindex supply at its final asymmetric primitives;
* `.toOutputAgreementFamilySupply` / `.coassoc_gen`.

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

/-- **R-6c-body-67 — the OUTPUT-reindex supply at its final asymmetric primitives.**  A representative family
plus, per generator, the RIGHT second-coproduct de-contraction (`imageQuotient`) and the LEFT direct base-outer
cover (`branchDirect`) — the two structurally different OUTPUT leaves after bodies 64–66. -/
structure ResolvedOutputCoverPrimitiveSupply (D : ResolvedCoproductProperForestData) where
  /-- A representative resolved graph for each generator. -/
  repGraph : ResolvedHopfGen → ResolvedFeynmanGraph
  /-- The representative is connected-divergent. -/
  repCD : ∀ x : ResolvedHopfGen, (repGraph x).forget.toClass.IsConnectedDivergent
  /-- The representative's class IS the generator. -/
  rep_eq : ∀ x : ResolvedHopfGen, x = (repGraph x).toResolvedHopfGen (repCD x)
  /-- The per-`G` grand full supply at each representative. -/
  grand : ∀ x : ResolvedHopfGen, ResolvedCoassocGrandFullSupply D (repGraph x)
  /-- The RIGHT second-coproduct de-contraction cover at each representative. -/
  imageQuotient : ∀ x : ResolvedHopfGen, ResolvedImageQuotientFiberSupply (grand x)
  /-- The LEFT direct base-outer cover at each representative. -/
  branchDirect : ∀ x : ResolvedHopfGen, ResolvedBranchCoverDirectSupply (grand x)

/-- **R-6c-body-67 — to body-60's agreement family, via the RIGHT/LEFT adapter chains.**  RIGHT: body-66 → 65 →
62; LEFT: body-64 → 61. -/
def ResolvedOutputCoverPrimitiveSupply.toOutputAgreementFamilySupply
    (S : ResolvedOutputCoverPrimitiveSupply D) : ResolvedOutputAgreementFamilySupply D where
  repGraph := S.repGraph
  repCD := S.repCD
  rep_eq := S.rep_eq
  grand := S.grand
  imageAgree := fun x =>
    (S.imageQuotient x).toImageQuotientCoverSupply.toImageFiberCoverSupply.toImageFiberAgreementSupply
  branchAgree := fun x =>
    (S.branchDirect x).toBranchFiberCoverSupply.toBranchFiberAgreementSupply

/-- **R-6c-body-67 — the OUTPUT cover asymmetry capstone.**  From the representative family and the two
asymmetric primitive covers, `Δᵣ`-coassociativity on every generator.  The OUTPUT reindex is now fully proved
except `image_quotient_fiber` (RIGHT) + `branch_cover_direct` (LEFT). -/
theorem ResolvedOutputCoverPrimitiveSupply.coassoc_gen
    (S : ResolvedOutputCoverPrimitiveSupply D) (x : ResolvedHopfGen) :
    D.coassocLeft (MvPolynomial.X x) = D.coassocRight (MvPolynomial.X x) :=
  S.toOutputAgreementFamilySupply.coassoc_gen x

end GaugeGeometry.QFT.Combinatorial
