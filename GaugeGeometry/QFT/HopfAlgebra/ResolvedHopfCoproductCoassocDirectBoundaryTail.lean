import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRegroup
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassoc

/-!
# R-6c-body-88 — the A2-direct coassoc path: `coassoc_gen` from the boundary+tail reindex, no σ-cover

Eighty-eighth genuine-body step, fixing the A2-direct path mandated by body-84–87: `coassoc_gen` follows
DIRECTLY from the regroup reindex `regroupImageSum = regroupBranchSum`, bypassing the σ-cover common-cover
route (unsatisfiable for the canonical carrier, body-87).

## The reduction (existing, non-circular)

The regroup bookkeeping (`…CoassocRegroup`) already gives, for every generator `x`:

* `lhsExpansion : coassocLeft (X x) = coassocPrimitivePart x + regroupBranchSum x` (PROVED);
* `rhsExpansion : coassocRight (X x) = coassocPrimitivePart x + regroupImageSum x` (PROVED);
* `ResolvedCoproductH58Compatibility.ofRegroup (reindex : ∀ x, regroupImageSum x = regroupBranchSum x)` →
  `.coassoc_gen x : coassocLeft (X x) = coassocRight (X x)` (`rw [lhsExpansion, rhsExpansion, reindex]`).

So `coassoc_gen ⇐ reindex` with the SAME `coassocPrimitivePart` on both sides — NOT circular; the reindex is
the genuine content.  By definition `regroupImageSum x = 1 ⊗ forestSum(x.1) + coassocRightTail(forestSum(x.1))`
and `regroupBranchSum x = assoc(forestSum(x.1) ⊗ 1) + coassocLeftTail(forestSum(x.1))`, so the reindex IS the
boundary+tail identity

```text
1 ⊗ forestSum + coassocRightTail(forestSum)  =  assoc(forestSum ⊗ 1) + coassocLeftTail(forestSum).
```

## Why A2-direct (not the σ-cover)

Body-87 established that the σ-cover common-cover route — proving the reindex via `regroupImageSum = ∑ cover =
regroupBranchSum` — is UNSATISFIABLE for the canonical proper-forest carrier: the boundary `1 ⊗ forestSum`
(slot `1`) is not a cover image-weight (`∅ ∉ carrier`, so every image weight has slot `leftTerm(nonempty) ≠ 1`).
So the reindex must be proven WITHOUT a common cover value.  `ResolvedDirectBoundaryTailCoassocSupply` fields the
reindex directly and produces `coassoc_gen` — the whole R-6c collapsing to this single genuine reindex (as the
`ofRegroup` docstring already notes), now on the A2-direct footing.

## The remaining content

`boundary_tail_eq` (= the reindex) is the genuine coassociativity of `Δᵣ` on the forest sum.  It is NOT
trivially provable (it is equivalent to `coassoc_gen`); the honest routes are:

* induction over subgraph complexity (the standard CK / Zimmermann forest argument), reducing `Δᵣ`-coassoc on
  `X_G` to `Δᵣ`-coassoc on the strictly smaller quotient/component generators; or
* a direct algebraic argument on `coassocRightTail = id ⊗ Δᵣ` vs `coassocLeftTail = assoc ∘ (Δᵣ ⊗ id)` using the
  recursive structure of the resolved coproduct.

Either way the σ-cover superstructure (bodies 36–87 OUTPUT / support-9 image_agreement) is superseded for the
canonical carrier: the coassoc content is exactly `boundary_tail_eq`, fielded here, to be proven by induction.

Per the HALT: `boundary_tail_eq` is NOT proved (it is the genuine reindex); the reduction to `coassoc_gen` is via
the existing `ofRegroup`; no unsatisfiable σ-cover agreement is reused.

Landed:

* `ResolvedDirectBoundaryTailCoassocSupply D` — the boundary+tail reindex (`boundary_tail_eq`);
* `.coassoc_gen` — `Δᵣ`-coassociativity on every generator, via `ofRegroup`.

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

/-- **R-6c-body-88 — the A2-direct boundary+tail reindex** (the single genuine coassoc content).  For every
generator `x`, `regroupImageSum x = regroupBranchSum x` — i.e. `1 ⊗ forestSum + coassocRightTail(forestSum) =
assoc(forestSum ⊗ 1) + coassocLeftTail(forestSum)`.  This is `Δᵣ`-coassociativity on the forest sum, to be
proven by induction (NOT via the σ-cover, unsatisfiable for the canonical carrier, body-87). -/
structure ResolvedDirectBoundaryTailCoassocSupply (D : ResolvedCoproductProperForestData) where
  /-- The regroup reindex `regroupImageSum x = regroupBranchSum x` (the boundary+tail identity). -/
  boundary_tail_eq : ∀ x : ResolvedHopfGen, D.regroupImageSum x = D.regroupBranchSum x

/-- **R-6c-body-88 — `coassoc_gen` from the boundary+tail reindex** (A2-direct, no σ-cover).  Via the existing
`ofRegroup` (the proved `lhs/rhsExpansion` + primitive matching). -/
theorem ResolvedDirectBoundaryTailCoassocSupply.coassoc_gen
    (S : ResolvedDirectBoundaryTailCoassocSupply D) (x : ResolvedHopfGen) :
    D.coassocLeft (MvPolynomial.X x) = D.coassocRight (MvPolynomial.X x) :=
  (ResolvedCoproductH58Compatibility.ofRegroup (D := D) S.boundary_tail_eq).coassoc_gen x

end GaugeGeometry.QFT.Combinatorial
