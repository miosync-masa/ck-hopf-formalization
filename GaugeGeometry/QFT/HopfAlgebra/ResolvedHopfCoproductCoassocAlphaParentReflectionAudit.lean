import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaParentOnePI
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocInnerRawM3
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocInnerRawAggregate
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocToInner
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocInnerRawProper
import GaugeGeometry.QFT.HopfAlgebra.ResolvedCoproductIndex
import GaugeGeometry.QFT.HopfAlgebra.Coassoc

/-!
# R-6c-body-553 — divergence-reflection API scope audit + PUBLIC adapter + Parent-FREE premises

Five-hundred-and-fifty-third genuine-body step, a **scope audit + public wrapper**.  It banks (a) a PUBLIC replacement
for the private `Coassoc`-local re-export of the reflection class field, and (b) the *Parent-free* premises needed to
eventually apply that class to the canonical `W″` parent (bodies 554–556).  It does **not** prove `parentDivergent`, does
**not** apply reflection to the parent, and introduces **no** new class/structure/instance and **no** `Parent` supply
inhabitant.

## Step 1 — reflection-API visibility verdict (confirmed via `#check` while developing)

* `admissibleSubgraphQuotientRemainderSubgraph` (`Coassoc.lean:3680`) — **PUBLIC** `noncomputable def`.
* `IsDivergenceReflectedByAdmissibleForestContract` and its field
  `IsDivergenceReflectedByAdmissibleForestContract.remainder_isDivergent_reflect` (`Coassoc.lean:3768`) — **PUBLIC**
  (it is public precisely so the cross-file Hopf assembly can synthesise the forest-cover data from it).
* The resolved remainder-mirror projections and the `forget` projections used below
  (`ResolvedAdmissibleSubgraph.forget_isPairwiseDisjoint` / `forget_hasNonemptyComponents` / `forget_elements` /
  `forget_injOn_elements`, `ResolvedAdmissibleSubgraph.isConnectedDivergent`) — **PUBLIC**.
* Only the thin re-export `admissibleSubgraphQuotientRemainderSubgraph_isDivergent_reflect` (`Coassoc.lean:3783`) and the
  `@[simp]` `admissibleSubgraphQuotientRemainderSubgraph_{vertices,internalEdges,externalLegs}` projections are
  `private` — that private re-export is exactly the wrapper we replace publicly in Step 2.

Verdict line: **reflection API visibility = OPEN** (everything load-bearing is public; only the old thin wrappers were
private).

## Step 2 — public thin adapter (BANKED)

`admissibleSubgraphQuotientRemainder_divergent_reflect` is the PUBLIC replacement of the private
`admissibleSubgraphQuotientRemainderSubgraph_isDivergent_reflect`.  It is **not** a new physics law: its body is a single
application of the existing public class field
`IsDivergenceReflectedByAdmissibleForestContract.remainder_isDivergent_reflect` — arguments in the forest-cover order.

## Step 3 — canonical application owner (recorded alignment; NO reflection applied here)

The eventual application (bodies 554–556) instantiates the reflection field at:

```text
H         := (canonicalLegSaturatedParentForget z δ)          -- the canonical localized `W″` parent's flat `.forget`
A_res     := innerRaw z δ.1 (canonical datum) (canonical hE) (canonical hL)   -- resolved inner forest in the parent
A_flat    := A_res.forget                                     -- flat admissible forest in `H`
γ         := the parent self-subgraph of `H`                  -- so `γ.IsDivergent = parentDivergent`
starOf    := (the flat descent of) `touchedInnerStarTotal …`  -- Residual 1 below
remainder := admissibleSubgraphQuotientRemainderSubgraph A_flat starOf γ  -- intended = `δ.forget`, KNOWN divergent (z.2.1)
```

so the reflection's conclusion `γ.IsDivergent` **is** `parentDivergent`, and its `hRemDiv` is `δ`'s known divergence.
This mapping is recorded only; it is **not** applied in this body.

## Step 4 — Parent-FREE premises for `A_flat = (innerRaw …).forget` (BANKED)

All three are stated over the exact `innerRaw` signature `(z) (δ) (datum) (hE) (hL)` (so the canonical parent obtains
them by supplying the canonical datum), and use only `Measure` / the resolved-`forget` projections / existing
inserted-component CD — **no `Parent`, no `forget` injectivity, no `sourceStar = targetStar`**:

* `legSaturated_innerRawForget_isPairwiseDisjoint` — `(innerRaw …).forget.IsPairwiseDisjoint`, one line
  (`ResolvedAdmissibleSubgraph.forget_isPairwiseDisjoint`; no extra hypothesis).
* `legSaturated_innerRawForget_forestDivergent` — `∀ η ∈ (innerRaw …).forget.elements, η.IsDivergent`, from the resolved
  forest's own `isConnectedDivergent` accessor on each element (`.isDivergent`); no extra hypothesis, no `toInner`
  round-trip needed.
* `legSaturated_innerRawForget_hasNonemptyComponents` — `(innerRaw …).forget.HasNonemptyComponents` **from** the resolved
  component-nonemptiness `h : (innerRaw …).HasNonemptyComponents` (thin transport
  `ResolvedAdmissibleSubgraph.forget_hasNonemptyComponents`).  This is the intended shape (`forget_hasNonemptyComponents
  A_res h`): the resolved `h` is *not* derivable from `IsConnectedDivergent` alone — CD ⇒ `vertices.Nonempty` is a genuine
  supply in this development (see `ComponentNonempty.lean`) — and is discharged in 554+ by
  `(innerRaw_isProperForest P Core z δ).2.1` once a `Core` is in scope.  Kept honest: the supply enters as `h`, not forged.

## Step 5 — star-descent verdict (NAMED residual; NO proof, NO stub def)

The existing `resolvedStarOnForget` is specific to `resolvedComponentFreshStar` and MUST NOT be cast onto
`touchedInnerStarTotal`.  The star the reflection needs is the *flat descent* of `touchedInnerStarTotal` through
`forget`, recovered via `forget_injOn_elements`'s **unique preimage** (GLOBAL `forget` injectivity is FORBIDDEN):

```text
Residual 1 (body-554):  flatTouchedInnerStar      : A_flat.elements → VertexId
                        flatTouchedInnerStar_spec : flatTouchedInnerStar (B.forget) = touchedInnerStarTotal B
                        flatTouchedInnerStar_fresh: A_flat.IsFreshStarAssignment flatTouchedInnerStar
```

Its construction (body-554) must use `forget_injOn_elements` for the unique preimage — recorded, not built here.

## Step 6 — remainder-alignment verdict (SAFE-STOP; NO equality proved)

The final needed identity (conceptually):

```text
Residual 2 (body-555):  admissibleSubgraphQuotientRemainderSubgraph A_flat flatTouchedInnerStar γ = δ.forget
                        (or an equivalent class/data equality)  -- the "remainder = δ" alignment
```

Assets that will feed it (recorded, not consumed here): the resolved `quotientRemainderSubgraph` three projections,
body-548 `recontract548_parent_*`, the `recontract_innerRaw_*` series (body-330), and the resolved-to-flat
retarget/`forget` projections.  The equality is **not** completed in this body.

Then **body-556**: apply the Step-2 adapter with the Step-4 premises + Residual-1 + Residual-2 + `δ`'s known divergence
`⟹ parentDivergent ⟹` (with body-552's `parentCD ↔ parentDivergent`) **`Parent` GONE**, final signature `Measure / E /
rep*`.

## Scoreboard

```text
reflection API visibility           OPEN (all public; only old thin wrappers were private)
public reflection adapter           BANKED (admissibleSubgraphQuotientRemainder_divergent_reflect)
disjoint / component-CD             PARENT-FREE DERIVED  (for A_flat = (innerRaw …).forget; no hypothesis)
nonempty-components                 PARENT-FREE TRANSPORT (resolved h ↦ flat; h from proper-forest supply, 554+)
remaining construction residual
  1. explicit-star descent through forget   (body-554, via forget_injOn_elements)
  2. flat quotient remainder = δ             (body-555)
new physics law                     ZERO
```

Per the HALT/guards: reflection is NOT applied to the parent; NO `parentDivergent` proof; NO `Parent` supply inhabitant;
NO new class/structure/instance (the Step-2 adapter is a `theorem`, the residuals are named in this docstring only —
no stub defs); NO `touchedInnerStarTotal = resolvedComponentFreshStar`; NO global `forget` injectivity; no
round-trip / coassoc; no unconditional claim; old private flat theorems untouched.  No facade, no `sorry`/`admit`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-! ## Step 2 — the PUBLIC thin reflection adapter. -/

/-- **R-6c-body-553 (Step 2) — PUBLIC reverse forest-contraction divergence reflection.**  The public replacement of the
`Coassoc`-local `private` re-export `admissibleSubgraphQuotientRemainderSubgraph_isDivergent_reflect`.  It is **not** a new
physics law: the body is a single application of the existing **public** class field
`IsDivergenceReflectedByAdmissibleForestContract.remainder_isDivergent_reflect`, with the arguments in the order used by
the forest-cover source-subgraph API.  ★NO `Parent`, NO round-trip, NO new obligation.★ -/
theorem admissibleSubgraphQuotientRemainder_divergent_reflect
    [IsDivergenceReflectedByAdmissibleForestContract] {G : FeynmanGraph}
    (A : AdmissibleSubgraph G) (hDisj : A.IsPairwiseDisjoint) (hCompNE : A.HasNonemptyComponents)
    (hForestDiv : ∀ η ∈ A.elements, η.IsDivergent)
    (starOf : FeynmanSubgraph G → VertexId) (hFresh : A.IsFreshStarAssignment starOf)
    (γ : FeynmanSubgraph G)
    (hRemDiv : (admissibleSubgraphQuotientRemainderSubgraph A starOf γ).IsDivergent) :
    γ.IsDivergent :=
  IsDivergenceReflectedByAdmissibleForestContract.remainder_isDivergent_reflect
    A hDisj hCompNE hForestDiv starOf hFresh γ hRemDiv

/-! ## Step 4 — Parent-FREE premises for `A_flat = (innerRaw …).forget`. -/

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}
  (z : ForestBlockCodType D G)
  (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
  (datum : ResolvedTouchedLegLiftDatum z δ)
  (hE : ∀ e ∈ G.internalEdges, e.source ∈ G.vertices ∧ e.target ∈ G.vertices)
  (hL : ∀ ℓ ∈ G.externalLegs, ℓ.attachedTo ∈ G.vertices)

/-- **R-6c-body-553 (Step 4a) — `A_flat = (innerRaw …).forget` is pairwise-disjoint** (Parent-free).  One line:
`forget` preserves the resolved inner forest's pairwise-disjointness.  NO hypothesis, NO `Parent`. -/
theorem legSaturated_innerRawForget_isPairwiseDisjoint :
    (innerRaw z δ datum hE hL).forget.IsPairwiseDisjoint :=
  (innerRaw z δ datum hE hL).forget_isPairwiseDisjoint

/-- **R-6c-body-553 (Step 4b) — every flat forest component of `A_flat` is divergent** (Parent-free).  Each flat element
`η = δ'.forget` for a resolved element `δ'` of `innerRaw`, whose `IsConnectedDivergent` (the resolved forest's own
`isConnectedDivergent` accessor) yields `η.IsDivergent`.  NO hypothesis, NO `toInner` round-trip, NO `Parent`. -/
theorem legSaturated_innerRawForget_forestDivergent :
    ∀ η ∈ (innerRaw z δ datum hE hL).forget.elements, η.IsDivergent := by
  intro η hη
  rw [ResolvedAdmissibleSubgraph.forget_elements] at hη
  obtain ⟨δ', hδ', rfl⟩ := Finset.mem_image.mp hη
  exact ((innerRaw z δ datum hE hL).isConnectedDivergent δ' hδ').isDivergent

/-- **R-6c-body-553 (Step 4c) — `A_flat = (innerRaw …).forget` has nonempty components** (Parent-free transport).  Thin
descent of the resolved componentwise nonemptiness `h` through `forget`.  The resolved `h` is **not** derivable from
`IsConnectedDivergent` alone (CD ⇒ `vertices.Nonempty` is a genuine supply in this development — see
`ComponentNonempty.lean`); it enters honestly as the hypothesis, and is discharged in body-554+ by
`(innerRaw_isProperForest P Core z δ).2.1` once a `Core` is in scope.  ★NO `Parent`, NO forged nonemptiness.★ -/
theorem legSaturated_innerRawForget_hasNonemptyComponents
    (h : (innerRaw z δ datum hE hL).HasNonemptyComponents) :
    (innerRaw z δ datum hE hL).forget.HasNonemptyComponents :=
  (innerRaw z δ datum hE hL).forget_hasNonemptyComponents h

end GaugeGeometry.QFT.Combinatorial
