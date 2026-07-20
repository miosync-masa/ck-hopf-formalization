import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocPromotedStarCoherence
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocInnerStarCoherenceValue
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocComponentFreshStar

/-!
# R-6c-body-446 — cross-ambient strict-star inhabitability AUDIT (usage map + no-go + weaker socket prototype)

Four-hundred-and-forty-sixth genuine-body step — an audit (no migration), the body-403 lesson applied to the two
CROSS-AMBIENT star coherence sockets that survive in body-445's final signature: `StarProm`
(`promoted_star_agrees`) and `InnerStarRaw` (`innerStar_agrees_raw`).  Both demand STRICT star-VALUE equality across
DIFFERENT ambients:

```text
promoted_star_agrees : starOf G (selectedOuterRawOf q) (o.γ.promote b) = starOf o.γ.tRFG o.B b
innerStar_agrees_raw : starOf (Core.parent z δ).tRFG (Core.innerRaw z δ) (toInner … A) = starOf G z.1.1 A.1
```

## 1. Usage map (what each consumer extracts)

* `promoted_star_agrees` — consumed in `ParentInternalEdgesConcrete` (:146) INSIDE a `retargetVertex` computation:
  `starProm.promoted_star_agrees q o (o.B.1.componentAt hv) …` rewrites the star VALUE so the two `contractWithStars`
  retargets agree (→ **contract/retarget-graph equality**, then `starOf_injective` + `starVertices` membership).
* `innerStar_agrees_raw` — consumed in `HardcodedStarSwap` (:114) to SWAP the hardcoded `starOf parent innerRaw` for the
  outer star, so `contractWithStars` (which reads the star) yields the aligned graph (→ **contract-graph equality**).

Verdict on the shape: BOTH are per-star VALUE equalities used only to force a **contracted-or-retargeted-graph
equality**.  That is exactly the body-403 pattern — a class-level equality carried by a per-star value equality.

## 2. Inhabitability under the canonical fresh allocator (`W' .starOf = resolvedComponentFreshStar`)

`resolvedComponentFreshStar G A γ = FeynmanGraph.freshVertex G.vertices + A.elements.toList.idxOf γ` (body-414) — the star
is `freshVertex(ambient) + (index in the forest)`.  So its VALUE has an ambient-dependent BASE (`freshVertex G.vertices`)
and a forest-ordering OFFSET.  Both cross-ambient identities compare stars over an ambient `G` against stars over a
STRICT sub-ambient (a component `o.γ.1` / a parent `Core.parent z δ`), whose `freshVertex` base is generally SMALLER.

**No-go (banked, arithmetic).**  `resolvedComponentFreshStar_ne_of_freshVertex_gap`: whenever the ambient's fresh base
exceeds the sub-ambient's by more than the inner forest size, the two stars land in DISJOINT ranges and cannot be equal.
So the strict cross-ambient equality is NOT a theorem for the fresh allocator, and NOT concrete-choosable while keeping
freshness (the base is forced by the ambient).  This confirms, on `W'`'s actual allocator, the pre-existing verdict
(bodies 349/379/383/398) that a component-identity-based allocator would be needed — the fresh allocator is precisely NOT
that.  **Canonical fresh allocator exists; strict cross-ambient coherence does not.**

## 3. Weakest sufficient interface (prototype, NOT migrated)

Following the body-405–425 alpha route, the faithful replacement is a per-star equality UP TO a correcting permutation
`ρ` (which the downstream can absorb because it only needs the contracted graphs, related by `mapPerm ρ`):

* `ResolvedPromotedStarCorrectingPermSupply` — `ρ q o` with `promoted_star_agrees_upto` (`… = (ρ q o) (starOf o.γ.tRFG …)`);
* `ResolvedInnerStarCorrectingPermSupply` — `ρ z δ` with `innerStar_agrees_upto` (`… = (ρ z δ) (starOf G z.1.1 A.1)`).

These are PROTOTYPES only — banked to fix the socket shape, NOT yet consumed (the strict supplies remain the current
inputs; migrating the consumers to the `mapPerm ρ` graph equality is later work).

## 4. Migration scope (audited, deferred)

The strict-star consumers to retype under `ρ` (all currently take the strict supplies): body-385/386
(`ParentInternalEdgesConcrete` / `ParentExternalLegsConcrete` — promoted), body-351/357/358 (`HardcodedStarSwap` /
remnant round-trip — inner), body-349's `toInnerStarCoherenceSupply`, and finally the adapters body-441/445.  Whether the
concrete `VBuild` / `Concrete` construction can ABSORB `ρ` (so `ρ = 1` on the live domain) is the decisive follow-up: if
so, the correcting-perm interface is discharged there and no strict cross-ambient equality is ever fabricated.

Per the HALT/guards: body-445 stays a valid conditional theorem; NO strict cross-ambient equality is fabricated from
freshness; canonical `Fstar` and cross-ambient `InnerStarRaw` are kept distinct; this body does NOT migrate — only the
usage map, the banked no-go, and the weaker socket prototypes.  NOT the unconditional theorem.  No facade, no flat term,
no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

set_option linter.unusedSectionVars false

/-! ### 2. The banked arithmetic no-go for the canonical fresh allocator. -/

/-- **R-6c-body-446 — the fresh star is at least the ambient fresh base.** -/
theorem resolvedComponentFreshStar_ge (G : ResolvedFeynmanGraph)
    (A : ResolvedAdmissibleSubgraph G) (γ : ResolvedFeynmanSubgraph G) :
    FeynmanGraph.freshVertex G.vertices ≤ resolvedComponentFreshStar G A γ :=
  Nat.le_add_right _ _

/-- **R-6c-body-446 — the fresh star is below the ambient fresh base plus the forest size.** -/
theorem resolvedComponentFreshStar_le (G : ResolvedFeynmanGraph)
    (A : ResolvedAdmissibleSubgraph G) (γ : ResolvedFeynmanSubgraph G) :
    resolvedComponentFreshStar G A γ ≤ FeynmanGraph.freshVertex G.vertices + A.elements.card := by
  unfold resolvedComponentFreshStar
  rw [← Finset.length_toList]
  exact Nat.add_le_add_left List.idxOf_le_length _

/-- **R-6c-body-446 ∎ — the cross-ambient strict-star NO-GO (arithmetic).**  When the ambient's fresh base exceeds the
sub-ambient's by more than the inner forest size, the two fresh stars occupy disjoint ranges — so no strict cross-ambient
star equality can hold for the canonical fresh allocator. -/
theorem resolvedComponentFreshStar_ne_of_freshVertex_gap
    {G G' : ResolvedFeynmanGraph} (A : ResolvedAdmissibleSubgraph G) (A' : ResolvedAdmissibleSubgraph G')
    (γ : ResolvedFeynmanSubgraph G) (γ' : ResolvedFeynmanSubgraph G')
    (hgap : FeynmanGraph.freshVertex G'.vertices + A'.elements.card
      < FeynmanGraph.freshVertex G.vertices) :
    resolvedComponentFreshStar G' A' γ' ≠ resolvedComponentFreshStar G A γ :=
  ne_of_lt (lt_of_le_of_lt (resolvedComponentFreshStar_le G' A' γ')
    (lt_of_lt_of_le hgap (resolvedComponentFreshStar_ge G A γ)))

/-! ### 3. The weakest-sufficient correcting-permutation sockets (prototypes, NOT consumed). -/

variable {D : ResolvedCoproductProperForestData}

/-- **R-6c-body-446 — prototype: promoted-star coherence UP TO a correcting permutation.**  The faithful alpha
replacement of `promoted_star_agrees` (per-star equality modulo `ρ q o`); the downstream absorbs `ρ` at the
contracted-graph level (`mapPerm ρ`).  Prototype only — not yet consumed. -/
structure ResolvedPromotedStarCorrectingPermSupply
    (Fmem : ResolvedSelectedOuterFilteredMemSupply D) (V : ResolvedConcreteSummandValueSupply D) where
  /-- The correcting permutation per promoted occurrence. -/
  ρ : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G),
    ResolvedCoassocSplitChoice.ForestChoiceOccurrence q.1 → Equiv.Perm VertexId
  /-- The promoted star equals the inner star relabeled by `ρ`. -/
  promoted_star_agrees_upto : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (o : ResolvedCoassocSplitChoice.ForestChoiceOccurrence q.1)
    (b : ResolvedFeynmanSubgraph o.γ.1.toResolvedFeynmanGraph) (_hb : b ∈ o.B.1.elements),
    D.starOf G ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf q.1) (o.γ.1.promote b)
      = (ρ q o) (D.starOf o.γ.1.toResolvedFeynmanGraph o.B.1 b)

/-- **R-6c-body-446 — prototype: inner-star coherence UP TO a correcting permutation.**  The faithful alpha replacement
of `innerStar_agrees_raw` (per-star equality modulo `ρ z δ`).  Prototype only — not yet consumed. -/
structure ResolvedInnerStarCorrectingPermSupply
    (Core : ResolvedMultiStarDecontractionValueCoreSupply D) where
  /-- The correcting permutation per de-contraction block. -/
  ρ : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) // x ∈ forestDomain z} →
      Equiv.Perm VertexId
  /-- The parent/inner star equals the outer star relabeled by `ρ`. -/
  innerStar_agrees_upto : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) // x ∈ forestDomain z})
    (A : {x : ResolvedFeynmanSubgraph G // x ∈ touchedOuterComponents z δ.1}),
    D.starOf (Core.parent z δ).toResolvedFeynmanGraph (Core.innerRaw z δ)
        (toInner z δ.1 (Core.legLift z δ) (Core.hE z) (Core.hL z) A)
      = (ρ z δ) (D.starOf G z.1.1 A.1)

end GaugeGeometry.QFT.Combinatorial
