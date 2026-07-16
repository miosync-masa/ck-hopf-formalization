import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestParentDomainDefect

/-!
# R-6c-body-307 — codomain-orphan cover audit: the RHS ranges over the MODEL carrier, not all proper forests (scout)

Three-hundred-and-seventh genuine-body step — the codomain-restriction design scout, WIDENED from the region core
(body-306) to the **concrete cover (body-253) and the codomain sum** itself.  The question: does a de-contraction orphan
(a star-touching quotient component `δ` that spans several stars, so has no single parent in `z.1.1.elements` — body-306)
escape into the COVER / RHS SUM, making the concrete cover uninhabitable, or is it confined to a repairable leaf?  This
body reads the RHS sum + the `sum_bij'` totality directly and delivers the three-stage judgment.  It banks ONE honest
stage-1 lemma (`forestBlockCod_mem_gives_only_carrier`) and pins the verdict.  Imports body-306 so the pin stays honest
against the source.

## The three load-bearing facts (read directly from source)

1. **The RHS is the FULL, unfiltered codomain sum** (ForestBlockBijection.lean:142-151): the forest-block RHS is
   `∑ A ∈ (D.supply G).forestCarrier, ∑ B ∈ (D.supply (A.1.contractWithStars (D.starOf G A.1))).forestCarrier,
   leftTerm A ⊗ (leftTerm B ⊗ rightTerm B)`, rewritten to `∑ r ∈ forestBlockCodFinset G, …` by
   `Finset.sum_sigma'` (`:150`).  No sub-image filter — every `r ∈ forestBlockCodFinset` is a mandatory summand.

2. **`sum_bij'` demands a TOTAL two-sided inverse on `forestBlockCodFinset`** (ForestBlockBijection.lean:152-153):
   `Finset.sum_bij' (S.toFun G) (S.invFun G) …` requires `invFun` defined and `right_inv`-satisfying on ALL of
   `forestBlockCodFinset` (`invFun`/`invFun_mem`/`right_inv`, `:99-112`, all `∀ r ∈ forestBlockCodFinset G`).  The
   domain-filter `FilteredForestBlockDom` (body-245/249) filters the DOMAIN only; the codomain is never filtered.  The
   cover (body-253, `WitnessSplitFilteredValue.lean:57-67, 74-102`) inherits this: `forward_witness`/`witnessSplit_mem`/
   `forestPreimage`/`_forward` are all `∀ z ∈ forestBlockCodFinset G`.  So an orphan `z ∈ forestBlockCodFinset` is a
   mandatory `sum_bij'` target — "restrict to `image fwdMap`" is illegitimate unless `image fwdMap = forestBlockCodFinset`
   is PROVED (and body-306 shows it fails at orphans).

3. **The RHS ranges over the MODEL carrier `D.carrier`, NOT "all proper forests"** — the scout's necessary correction.
   `forestCarrier := (D.carrier H).attach` and `ForestIdx := {A // A ∈ D.carrier H}` (ResolvedHopfCoproductSupply.lean:
   151-152) with `H = A.1.contractWithStars (D.starOf G A.1)`.  `D.carrier : (G) → Finset (ResolvedAdmissibleSubgraph G)`
   is a MODEL PARAMETER (ResolvedHopfCoproductSupply.lean:130), constrained only by `hCD` (contraction CD, `:135`) and
   `mapPerm` equivariance.  So `B ∈` the RHS fiber ⟺ `B ∈ D.carrier H` — a **model choice**, not the full proper-forest
   powerset.  An orphan is a genuine RHS TERM iff the concrete carrier `D.carrier H` CONTAINS it.

## The three-stage judgment

* **Stage 1 — membership restriction (`hz : z ∈ forestBlockCodFinset G`) is INSUFFICIENT.**  `hz` yields ONLY
  `z.2.1 ∈ D.carrier (z.1.1.contractWithStars (D.starOf G z.1.1))` — and even that is already the subtype proof `z.2.2`,
  so `hz` adds NOTHING geometric (banked below as `forestBlockCod_mem_gives_only_carrier`, proved from `z.2.2` with `hz`
  unused).  No de-contractability, no single-parent, no `componentToForest ∈ z.1.1.elements` follows from membership.
  `FilteredForestBlockCod D G := {z // z ∈ forestBlockCodFinset G}` would therefore NOT close floor-297/298.

* **Stage 2 — `codomain_decontractable` as a model datum is the WRONG shape.**  The faithful CK carrier `D.carrier H`
  MUST include multi-star divergent forests: a connected-divergent subgraph of `H = G/A` spanning several `A`-components
  is a genuine CK subdivergence (`hCD` admits it; `IsProperForest`, ResolvedSubGraph.lean:638-643, has NO single-star
  clause).  Excluding them (a `codomain_decontractable` datum forcing every `δ ∈ forestDomain z` to have a single parent
  in `z.1.1.elements`) would DELETE genuine RHS terms — i.e. change the coproduct `Δᵣ` on `H` — so it is not an honest
  supplementary datum.  And `D.carrier` is graph-only (receives `H` with no memory of `A`), so it structurally cannot
  filter on the `A`-relative star-partition anyway.

* **Stage 3 — codomain filtering would BREAK faithfulness.**  Filtering `forestBlockCodFinset` down to the
  single-parent / `image fwdMap` sub-Finset makes the RHS no longer `(id ⊗ Δᵣ) ∘ Δᵣ`; the deleted multi-star `B` terms
  are generally nonzero (`leftTerm A ⊗ (leftTerm B ⊗ rightTerm B)`), so the filtered sum ≠ the true `coassocRight`.  This
  is exactly the trivialization the audit forbids (codomain = `image fwdMap` by fiat, with no proof the discarded terms
  vanish).

## VERDICT — B bounded by C, with the scout's correction: RETIRE the over-typed floor, do NOT restrict the codomain

The scout's flat **C** ("the indexing decomposition is wrong") is OVER-COMMITTED: it read `forestCarrier` as "all proper
forests," but the RHS ranges over the MODEL carrier `D.carrier H` (fact 3).  Real CK coassociativity IS true, so a genuine
total bijection `forestBlockDomFinset ↔ forestBlockCodFinset` EXISTS — it is the outer-MIXING map (`toFun (A', p) = (A, B)`
with `A` a fresh outer generally `⊋ A'`, ForestBlockBijection.lean:96-97): the per-component domain choices assemble into a
multi-star `B` precisely BECAUSE the outer `A` is not preserved.  The apparent "per-component vs multi-star" tension is
resolved by that outer mixing — it is NOT an obstruction to the raw bijection.

What is genuinely FALSE is the intermediate obligation **floor-297** (`forest_parent_mem_value :
componentToForest z δ ∈ z.1.1.elements`, GeometryFloorAssembly.lean:74-76) and its twin **floor-298** — the geometry-floor
reduction (body-299) introduced a per-component source-projection `componentToForest z δ` LANDING IN `z.1.1.elements`, and
that map does not exist at an orphan `z` (body-306).  These floors are the codomain-side analogue of the retired total
`selectedOuter_mem` (body-128): a reduction ARTIFACT over-typed past its live domain, not a fact the actual bijection needs.

Therefore the phase-1b repair is NOT a `FilteredForestBlockCod` codomain migration (stage 1 insufficient), NOT a
`codomain_decontractable` model datum (stage 2 unfaithful), NOT a codomain filter (stage 3 breaks `coassocRight`).  It is:
**retire floor-297/298 and re-target the concrete inhabitant at the RAW outer-mixing `ResolvedForestBlockBijectionSupply`
(`toFun`/`invFun`/`right_inv`, ForestBlockBijection.lean:96-112) DIRECTLY** — the genuine bijection, whose `invFun` reads
`B`'s components as CK subdivergences of `H` (NOT as parents in `z.1.1.elements`), and whose totality on
`forestBlockCodFinset` is exactly what CK coassociativity guarantees.  The geometry-floor layer (body-299) is a valid
implication but a DEAD reduction for the concrete model at this leaf; the outer-mixing bijection is the live target.

## Guards / status

Verdict B (an honest, satisfiable target exists — the raw bijection) bounded by C (the specific geometry-floor leaves 297/
298 are unsatisfiable and must be retired, not repaired in place).  The cover (body-253) is inhabitable, but through the
outer-mixing `invFun`, not through the over-typed `componentToForest ∈ elements` floor.  No codomain restriction; no
faithfulness-breaking filter.

Per the HALT: this is a design-scout judgment pin — one honest stage-1 lemma plus the three-stage verdict; the raw
outer-mixing `invFun` is NOT constructed here (that is the next inhabitant front); no `FilteredForestBlockCod` migration is
performed; no facade, no flat term, no `forgetHopf`.  The import keeps the pin honest against body-306/299.
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

/-- **R-6c-body-307 — stage-1: codomain membership yields ONLY carrier membership of `B`.**  Everything `hz : z ∈
forestBlockCodFinset G` can give about the quotient forest `z.2` is that its underlying subgraph lies in the MODEL carrier
`D.carrier (z.1.1.contractWithStars (D.starOf G z.1.1))` — and even that is already the subtype proof `z.2.2`, so `hz`
adds nothing.  No de-contractability, single-parent, or `componentToForest ∈ z.1.1.elements` follows; a
`FilteredForestBlockCod` migration therefore cannot close floor-297/298. -/
theorem forestBlockCod_mem_gives_only_carrier
    (z : ForestBlockCodType D G) (_hz : z ∈ forestBlockCodFinset (D := D) G) :
    z.2.1 ∈ D.carrier (z.1.1.contractWithStars (D.starOf G z.1.1)) :=
  z.2.2

end GaugeGeometry.QFT.Combinatorial
