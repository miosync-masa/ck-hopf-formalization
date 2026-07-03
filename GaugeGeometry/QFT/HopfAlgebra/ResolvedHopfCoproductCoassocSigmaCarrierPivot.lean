import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocEmptyPivot

/-!
# R-6c-body-86 — coassoc σ-cover carrier pivot: A2 (single `D.carrier`), the boundary/term_eq mismatch

Eighty-sixth genuine-body step, deciding A1 vs A2 by the TYPES.  The verdict is A2: the coassoc σ-cover uses the
SAME `D.carrier G` as the coproduct — there is no extended carrier admitting the empty selected outer.  This
exposes a genuine carrier/`term_eq` mismatch and settles that the common-cover chain (body-38/54) does not reach
`coassoc_gen` for the canonical (proper-forest) carrier.

## A2, by the types (PROVED)

* `ResolvedCoassocSplitChoice D G = Σ A : {A // A ∈ D.carrier G}, …` — the split choice's base is `s.1.1 ∈
  D.carrier G` (`s.1.2`);
* `ResolvedCoassocQuotientImage.selectedOuter : {A // A ∈ D.carrier G}` — the image's selected outer is
  `z.selectedOuter.1 ∈ D.carrier G` (`z.selectedOuter.2`, `resolved_selectedOuter_mem_carrier` below).

Both are in the SAME `D.carrier G`.  There is NO separate/extended carrier for the coassoc reindex.  So **A2**:
`selectedOuter ∈ D.carrier G` always, and under Case A (`∅ ∉ D.carrier G`, body-84) `selectedOuter ≠ ∅`.

## The consequence: the carrier / `term_eq` mismatch

Two requirements now collide on the SINGLE `D.carrier`:

* the COPRODUCT needs `∅ ∉ carrier` — else `leftTerm ∅ ⊗ rightTerm ∅ = 1 ⊗ X_G` would sit in `(D.supply G).sum`
  (the forest sum) double-counting the primitive `1 ⊗ X_G` (the canonical carrier is proper forests, body-84);
* `term_eq` at the all-right-primitive `⟨A, p₀⟩` needs `∅ ∈ carrier`: `resolvedSplitChoiceTerm ⟨A, p₀⟩ = 1 ⊗
  (leftTerm A ⊗ rightTerm A)` (body-65, slot `1 = leftTerm ∅`), while `imageWeight = leftTerm(selectedOuter) ⊗
  strictSummandTerm` (concrete) forces `leftTerm(selectedOuter ⟨A, p₀⟩) = 1`, i.e. `selectedOuter = ∅` — which by
  A2 must be a carrier forest.

So with the canonical proper-forest carrier, **`term_eq` is UNSATISFIABLE at the all-right-primitive split
choices** (`1 ⊗ (·)` cannot equal `leftTerm(nonempty carrier) ⊗ (·)`).  A single `D.carrier` cannot serve both
the coproduct (`∅ ∉`) and the coassoc `term_eq` (`∅ ∈`).

## Verdict and path

**A2 holds; the common-cover route is invalid for the canonical carrier.**  The body-38/54 chain proves
`coassoc_gen` from `regroupImageSum = ∑ cover = regroupBranchSum`, which needs the boundaries inside `∑ cover`,
i.e. the all-right-primitives to be `term_eq`/cover images — impossible with `∅ ∉ carrier`.  So the OUTPUT
must NOT bridge through a common cover value.  The correct route is **A2-direct**: prove `regroupImageSum =
regroupBranchSum` as the algebraic boundary + tail identity —

```text
1 ⊗ forestSum + coassocRightTail(forestSum)  =  assoc(forestSum ⊗ 1) + coassocLeftTail(forestSum)
```

— where the two cover-external boundaries (body-84) and the two tail sums are related by the coassociativity of
`Δᵣ` on the outer forest, NOT by identifying both with `∑ cover`.  Equivalently, `term_eq` / the split-choice
domain must EXCLUDE the degenerate all-right-primitive choices (so `∑ cover` is genuinely the proper-forest
tails).

This retires the A1 (extended-carrier / boundary-IN) option: bodies 78/80–83's boundary-IN machinery is
semantically over-strong for the canonical carrier.  bodies 76/77/85's tails-only branch form is on the A2 path.

Per the HALT, no coassoc proof is repaired; only the carrier classification is fixed (A2, by the types); the
`term_eq` degeneracy is recorded, not resolved.

Landed:

* `resolved_selectedOuter_mem_carrier` — the image's `selectedOuter` is a `D.carrier` forest (the A2 type fact).

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

/-- **R-6c-body-86 — the image's selected outer is a `D.carrier` forest (A2).**  The coassoc σ-cover's
`selectedOuter` lives in the SAME `D.carrier G` as the coproduct — no extended carrier.  So under Case A
(`∅ ∉ D.carrier G`) the selected outer is never empty. -/
theorem resolved_selectedOuter_mem_carrier (z : ResolvedCoassocQuotientImage D G) :
    z.selectedOuter.1 ∈ D.carrier G :=
  z.selectedOuter.2

end GaugeGeometry.QFT.Combinatorial
