import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightPrimitiveFactorComplete
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestRegion
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocLeftPartition
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocComponentPartition

/-!
# R-6c-body-122 — promoted factor: the third factor product, PROVED via the existing forest-region flattening

Hundred-and-twenty-second genuine-body step, the third factor product `promoted_factor` (the `inr` /
forest-choice side).  Unlike the right-primitive case, there is NO source↔quotient transport: the promoted
sub-forests live in `G` and their generators are intrinsic.  The whole product IS the existing forest-region
flattening `forestPart_eq_promotedOf` (`ForestRegion`), which already does the `Finset.prod_biUnion` over the
promoted components — so `promoted_factor` reduces cleanly to the single pairwise-disjointness hypothesis `hPD`
(a nonemptiness consequence, the sibling of `hLP`).

## The generic single-`attach` reindex (PROVED)

`prod_attach_filter_val`: `∏ γ ∈ t.attach.filter (P ∘ ·.1), f γ.1 = ∏ δ ∈ t.filter P, f δ`
(`Finset.prod_filter` + `Finset.prod_attach` + `Finset.prod_filter`).  This strips the outer `attach` of the
assembly's double-`attach` product down to the single `attach` of `forestComponents`.

## The promoted factor (PROVED given `hPD`)

`promoted_factor_of_hPD`: for a split choice `q`,

```text
∏_{γ : (p γ).isRight} localLeftFactor(p γ) = leftTerm(promotedOf q)
```

by rewriting through `forestPart_eq_promotedOf q hPD` (the existing forest region = promoted forest term) and
bridging the two forms: the filter `(p γ).isRight ↔ isForestChoice γ.1` (both say "the choice is `inr`", via
`choiceAt`) and the summand `localLeftFactor(p γ) = leftFactorOf q γ.1` (`localChoiceLeftFactor` at `choiceAt`).
No drop-out (the `isRight` filter already selects the `inr` components) and no transport (the summand
`localLeftFactor(inr Bᵧ) = leftTerm Bᵧ` is a product of intrinsic component generators, flattened into
`promotedOf` by `forestPart_eq_promotedOf`'s `prod_biUnion`).

## What remains: `hPD`

The sole remaining obligation is `hPD`: the per-parent promoted component sets are pairwise disjoint.  As
`ForestRegion` notes, this holds when the promoted components are nonempty — the same nonemptiness fact
(`ResolvedInputOuterElementNonemptySupply`, body-1 `cd_nonempty`) that discharged `hLP` (body-116) and
`outer_nonempty` (body-96).  So `promoted_factor` is fully reduced to the nonemptiness leaf.

Per the HALT: the promoted flattening is recovered from the existing `forestPart_eq_promotedOf` (proved given
`hPD`); `hPD` is isolated as the nonemptiness leaf; no remnant / quotient transport is entered.

Landed:

* `prod_attach_filter_val` — the generic single-`attach` filtered-product reindex (PROVED);
* `promoted_factor_of_hPD` — the assembly's `promoted_factor` given `hPD` (PROVED, via
  `forestPart_eq_promotedOf`).

Toolkit body (like body-119/120), no new supply.  No facade, no flat term, no `forgetHopf`.
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
set_option linter.unusedSimpArgs false

/-- **R-6c-body-122 — the generic single-`attach` filtered-product reindex.**  Strip the outer `attach` of a
double-`attach` product down to the single `attach` of the filtered set. -/
theorem prod_attach_filter_val {ι M : Type*} [CommMonoid M] (t : Finset ι) (P : ι → Prop)
    [DecidablePred P] (f : ι → M) :
    (∏ γ ∈ t.attach.filter (fun γ => P γ.1), f γ.1) = ∏ δ ∈ t.filter P, f δ := by
  rw [Finset.prod_filter, Finset.prod_attach t (fun δ => if P δ then f δ else 1), ← Finset.prod_filter]

/-- **R-6c-body-122 — the promoted factor** (PROVED given `hPD`).  `∏_{isRight} localLeftFactor =
leftTerm(promotedOf)` — the third of the four factor products, via the existing forest-region flattening
(`forestPart_eq_promotedOf`).  No transport: the promoted sub-forests' generators are intrinsic. -/
theorem promoted_factor_of_hPD (q : ResolvedCoassocSplitChoice D G)
    (hPD : (↑(q.1.1.elements.attach) : Set {x : ResolvedFeynmanSubgraph G // x ∈ q.1.1.elements})
      |>.PairwiseDisjoint q.promotedComponentElements) :
    (∏ γ ∈ (q.1.1.elements.attach).attach.filter (fun γ => (q.2 γ.1 γ.2).isRight),
        localLeftFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2))
      = resolvedForestLeftTerm ((resolvedPromotedOfSupply D G).promotedOf q) := by
  rw [← forestPart_eq_promotedOf q hPD, ResolvedCoassocSplitChoice.forestComponents,
    ← prod_attach_filter_val q.1.1.elements.attach q.isForestChoice (D.leftFactorOf q)]
  apply Finset.prod_congr
  · apply Finset.filter_congr
    intro γ hγ
    simp only [ResolvedCoproductProperForestData.leftFactorOf, ResolvedCoassocSplitChoice.isForestChoice,
      ResolvedCoassocSplitChoice.choiceAt, decide_eq_true_eq, eq_iff_iff]
    constructor
    · intro h; obtain ⟨B, hB⟩ := Sum.isRight_iff.mp h; exact ⟨B, hB⟩
    · rintro ⟨B, hB⟩; rw [hB]; rfl
  · intro γ hγ
    rw [ResolvedCoproductProperForestData.leftFactorOf, ResolvedCoassocSplitChoice.choiceAt]
    rfl

end GaugeGeometry.QFT.Combinatorial
