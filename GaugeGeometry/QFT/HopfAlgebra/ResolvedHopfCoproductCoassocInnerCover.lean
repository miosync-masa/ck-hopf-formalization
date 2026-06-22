import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRegroup

/-!
# R-6c-2d-4b-1 — the inner σ-cover bridge (connecting the last field to the reindex spine)

After `ofRegroup` (R-6c-2d-4a), the *entire* resolved coassociativity reduces to one field:
`regroupImageSum x = regroupBranchSum x`.  This file fixes the **bridge** from that field to the
generic cover reindex spine `ResolvedH58TermReindex.reindex` (R-6c-2a): a per-generator datum carrying
a `ResolvedH58TermReindex` together with the two **agreements** identifying its image- and branch-side
sums with `regroupImageSum`/`regroupBranchSum`.

Given such data for every `x`, the last field is discharged by chaining the two agreements through the
cover sum_bij, and `ofInnerCoassocSigmaCover` assembles the full
`ResolvedCoproductH58Compatibility` (hence `coassoc_gen`).  So R-6c now collapses to constructing one
`ResolvedInnerCoassocSigmaCoverData D x` per generator — i.e. the genuine geometry:

* a finite cover layer + resolved-`ResolvedHopfH3` weights (the de-contraction σ-cover), and
* the two agreements: `regroupImageSum x = termReindex.imageSum` (the **image** side, fed by the right
  inner expansion R-6c-2d-3) and `termReindex.branchSum = regroupBranchSum x` (the **branch** side,
  fed by the left product-of-sums / component-choice expansion R-6c-2d-2b).

Landed:

* `ResolvedInnerCoassocSigmaCoverData D x` — the bridge datum (`termReindex` + `image_agreement` +
  `branch_agreement`);
* `ResolvedInnerCoassocSigmaCoverData.reindex_eq` — the last field `regroupImageSum x =
  regroupBranchSum x`, by chaining the agreements through `termReindex.reindex`;
* `ResolvedCoproductH58Compatibility.ofInnerCoassocSigmaCover` — the constructor: a per-generator
  family of bridge data yields the full compatibility.

No facade, no flat term, no `forgetHopf`, no flat splitPhi.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

/-- **R-6c-2d-4b-1 — the inner σ-cover bridge datum.**  For one generator `x`, a resolved-term cover
reindex (`ResolvedH58TermReindex`) whose image- and branch-side sums are identified with the regrouped
`regroupImageSum`/`regroupBranchSum`.  The two agreements are the genuine geometry (image side =
R-6c-2d-3 right inner expansion; branch side = R-6c-2d-2b left product-of-sums); the cover sum_bij
itself is the facade-free spine (R-6c-2a). -/
structure ResolvedInnerCoassocSigmaCoverData (D : ResolvedCoproductProperForestData)
    (x : ResolvedHopfGen) where
  /-- The resolved-term cover reindex (image carrier = forest ⊔ mixed, weights in `ResolvedHopfH3`). -/
  termReindex : ResolvedH58TermReindex
  /-- The image-side identification (fed by the right inner expansion). -/
  image_agreement : D.regroupImageSum x = termReindex.imageSum
  /-- The branch-side identification (fed by the left component-choice expansion). -/
  branch_agreement : termReindex.branchSum = D.regroupBranchSum x

/-- The last coassociativity field, from a bridge datum: `regroupImageSum x = regroupBranchSum x`, by
chaining the two agreements through the cover sum_bij `termReindex.reindex`. -/
theorem ResolvedInnerCoassocSigmaCoverData.reindex_eq {D : ResolvedCoproductProperForestData}
    {x : ResolvedHopfGen} (S : ResolvedInnerCoassocSigmaCoverData D x) :
    D.regroupImageSum x = D.regroupBranchSum x := by
  rw [S.image_agreement, S.termReindex.reindex, S.branch_agreement]

/-- **R-6c-2d-4b-1 — the inner-σ-cover constructor.**  A per-generator family of bridge data yields
the full `ResolvedCoproductH58Compatibility` (via `ofRegroup`), hence `coassoc_gen`.  This collapses
all of resolved coassociativity to: construct one `ResolvedInnerCoassocSigmaCoverData D x` per
generator. -/
noncomputable def ResolvedCoproductH58Compatibility.ofInnerCoassocSigmaCover
    {D : ResolvedCoproductProperForestData}
    (S : ∀ x : ResolvedHopfGen, ResolvedInnerCoassocSigmaCoverData D x) :
    ResolvedCoproductH58Compatibility D :=
  ResolvedCoproductH58Compatibility.ofRegroup D (fun x => (S x).reindex_eq)

end GaugeGeometry.QFT.Combinatorial
