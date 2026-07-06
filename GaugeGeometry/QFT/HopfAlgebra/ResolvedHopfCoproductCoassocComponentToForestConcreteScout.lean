import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocPromotedForestRecoveryScout

/-!
# R-6c-body-188 — componentToForest concretization scout: the promote-collapse compatibility

Hundred-and-eighty-eighth genuine-body step, a prerequisite scout for body-186's two inclusions.  The audit found
the *semantic* shape of the deep leaf and reduced it to one crisp compatibility, then proved the per-component
collapse from it.

## The semantic finding (the crux)

For a forest-tagged component `γ` of the recovered outer (`recoverChoice z γ = inr Bᵧ`), the promoted contribution is

```text
promotedComponentElements recovered ⟨γ,_⟩ = (promote γ Bᵧ).elements = { γ.promote δ : δ ∈ Bᵧ.elements }
```

— the **de-contracted sub-pieces of `γ`** (each with vertices `⊆ γ`), *not* `γ` itself.  But `forestRecovered z` is
the set of forest-choice **parents** `γ`.  So `promotedOf recovered = forestRecovered` holds **iff** each promoted
subforest collapses to its parent:

```text
(promote γ Bᵧ).elements = {γ}          — i.e. Bᵧ is the whole-component (trivial one-piece) forest of γ
```

This is the concrete content of the "de-contraction round-trip": the forest tag `Bᵧ` on a *recovered* parent is the
whole component, so promoting it returns exactly `{γ}`.  Nothing in the abstract supplies forces this — it is the
genuinely fresh geometric fact, now named precisely.

## Two prerequisites (fielded) + the collapse (PROVED)

`ResolvedComponentToForestPromoteCompatibility D S Region` fields:

* `forestTag` — the forest index `Bᵧ` of `γ`'s component graph (body-152's `forestTag`, here for the abstract
  `Region`);
* `recoverChoice_forest_eq` — the tag pinning: on a `forestRecovered` component, `recovered.choiceAt γ = inr
  (forestTag z γ h)` (this pins the abstract `Region.recoverChoice` to a concrete `forestTag` on the forest region —
  the identification body-186's abstract setting lacked);
* `promote_collapse` — the collapse: `(promote γ (forestTag z γ h)).elements = {γ}`.

From these, `promotedComponentElements_forestRecovered` is **PROVED**: a forest-recovered parent's promoted
contribution is exactly `{γ}` — `promotedComponentElements_inr` (via the tag pinning) then `promote_collapse`.

## What each inclusion needs (scout deliverable)

* `forestRecovered_subset_promoted` (LIGHT) — `γ ∈ forestRecovered → γ ∈ {γ} = promotedComponentElements ⟨γ,_⟩ ⊆
  promotedElements`.  Needs only the collapse lemma here + `Finset.mem_biUnion`.
* `promoted_subset_forestRecovered` (HEAVY) — a promoted element lies in some `promotedComponentElements ⟨γ',_⟩`; on
  a forest component that set is `{γ'} ⊆ forestRecovered`; on a non-forest (`inl`) component it is `∅`.  Needs the
  collapse **and** the non-forest emptiness (`recoverChoice = inl ⇒ promotedComponentElements = ∅`, immediate from
  the `match`).

So the full `promoted_eq_forestRecovered` reduces to the biUnion collapse over these per-component values — the clean
body-189 path, replacing the two raw inclusions.

Per the HALT: the two inclusions / the biUnion assembly are not proved here; only the per-component collapse is
proved from the fielded compatibility; the semantic finding and the reduction path are recorded.

Landed:

* `ResolvedComponentToForestPromoteCompatibility D S Region` — `forestTag` + tag pinning + `promote_collapse`;
* `.promotedComponentElements_forestRecovered` — a forest parent's promoted contribution is `{γ}` (PROVED).

Scout / toolkit body (like body-186).  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-188 — the componentToForest / promote compatibility.**  The forest tag `Bᵧ` of a recovered forest
parent, the tag pinning (`recoverChoice = inr Bᵧ` on the forest region), and the collapse `(promote γ Bᵧ).elements =
{γ}` — the concrete content that makes `promotedOf recovered = forestRecovered`. -/
structure ResolvedComponentToForestPromoteCompatibility (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) (Region : ResolvedRegionChoiceRoundTripSupply D S) where
  /-- The forest index `Bᵧ` of a recovered forest parent's component graph. -/
  forestTag : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ (Region.Union.unionOuter z).1.elements}),
    γ.1 ∈ (Region.Union.forestRecovered z).elements → (D.supply (γ.1.toResolvedFeynmanGraph)).ForestIdx
  /-- Tag pinning: a forest-recovered component is tagged `inr (forestTag …)` by the recovered choice. -/
  recoverChoice_forest_eq : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ (Region.Union.unionOuter z).1.elements})
    (h : γ.1 ∈ (Region.Union.forestRecovered z).elements),
    ResolvedCoassocSplitChoice.choiceAt
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G) γ
      = Sum.inr (forestTag z γ h)
  /-- Collapse: the promoted (de-contracted) forest of a recovered parent is exactly the parent singleton. -/
  promote_collapse : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ (Region.Union.unionOuter z).1.elements})
    (h : γ.1 ∈ (Region.Union.forestRecovered z).elements),
    (ResolvedAdmissibleSubgraph.promote γ.1 (forestTag z γ h).1).elements = {γ.1}

namespace ResolvedComponentToForestPromoteCompatibility

variable {S : ResolvedConcreteSummandBundleSupply D} {Region : ResolvedRegionChoiceRoundTripSupply D S}

/-- **R-6c-body-188 — a forest parent's promoted contribution is its own singleton.**  Combines the tag pinning and
the collapse: for `γ ∈ forestRecovered z`, `promotedComponentElements recovered ⟨γ,_⟩ = {γ}`. -/
theorem promotedComponentElements_forestRecovered
    (C : ResolvedComponentToForestPromoteCompatibility D S Region)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ (Region.Union.unionOuter z).1.elements})
    (h : γ.1 ∈ (Region.Union.forestRecovered z).elements) :
    ResolvedCoassocSplitChoice.promotedComponentElements
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G) γ
      = {γ.1} := by
  rw [ResolvedCoassocSplitChoice.promotedComponentElements_inr _ (C.recoverChoice_forest_eq z γ h)]
  exact C.promote_collapse z γ h

end ResolvedComponentToForestPromoteCompatibility

end GaugeGeometry.QFT.Combinatorial
