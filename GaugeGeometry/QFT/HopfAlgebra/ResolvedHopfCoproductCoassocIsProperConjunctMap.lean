import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecoveredOuterNonempty
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocPositiveInternalEdges

/-!
# R-6c-body-243 — `IsProperForest`-conjunct map: bodies 235–242, and the `selectedOuter_mem` domain defect (docs anchor)

Two-hundred-and-forty-third genuine-body step, a documentation anchor (no new geometry).  It fixes the state of the
certificate `isProper` field (the five `IsProperForest` conjuncts) for the two constructed forests, and — the
load-bearing point — records that `selectedOuter_mem`'s *total* statement is **false at the all-right split** and is
fixed by a domain correction, not a stronger proof.  Imports body-241/238 so the map stays type-checked.
Reader-facing narrative: `CK_HOPF_FORMALIZATION_MAP.md` §"R-6c bodies 235–242"; proof-dependency map:
`CK_HOPF_DEPENDENCY_GRAPH.md` §"R-6c bodies 235–242".

## The conjuncts proved (235–241)

```text
236  HasNonemptyComponents (PROVED, generic)  — hasNonemptyComponents_of_cdNonempty, from cd_nonempty (body-1).
238  HasPositiveInternalEdgesComponents (PROVED, generic) — hasPositiveInternalEdgesComponents_of_cdPositive, from a
       NEW measure leaf cd_positiveInternalEdges (237 scout: IsConnectedDivergent does NOT force positive edges —
       IsOnePI's bridge clause is vacuous on 0 edges).
240  IsNonempty transfer infra (PROVED): isNonempty_of_cover / isNonempty_of_membership_iff / union_isNonempty_left/right.
241  Y.IsNonempty on the forward image (PROVED, membership-INDEPENDENT): recoveredOuter_isNonempty, from the domain
       outer's carrier membership + body-168 partition + union_eq; never touches unionOuter.2 (recovered_outer_mem 159).
```

## The `selectedOuter_mem` domain defect (242 — verdict (c) THREADING OBSTRUCTION)

```text
- selectedOuter_mem : ∀ s, selectedOuterRawOf s ∈ D.carrier G is TOTAL and FALSE at s = p_R (all-right split):
  leftOf p_R and promotedOf p_R are both empty ⇒ selectedOuterRawOf p_R = ∅, and ∅ ∉ D.carrier G (canonical).
- The real SUM consumer is indexed over forestChoiceCarrier A = (pi).filter (p ≠ p_R ∧ p ≠ p_L) (ForestCoreIndex.lean:70)
  — every summand carries p ≠ p_R; p_R is NOT a real summand.
- EmptyPivot already relocates the all-right boundary COVER-EXTERNAL (resolved_output_boundaries_external), taking
  ∅ ∉ D.carrier as a canonical-model input; it does not discharge selectedOuter_mem at p_R.
- FIX = domain correction, not a stronger proof: ∀ A, ∀ p ∈ forestChoiceCarrier A, selectedOuterRawOf ⟨A,p⟩ ∈ D.carrier G.
  body-151's mixed_ne_pR does NOT substitute (it excludes p_R only for reconstructed mixed codomain elements).
```

## Status table (certificate `isProper` conjuncts, both constructed forests)

```text
HasNonemptyComponents               X ✅ 236   Y ✅ 236       generic
HasPositiveInternalEdgesComponents  X ✅ 238   Y ✅ 238       generic (new measure leaf cd_positiveInternalEdges)
IsNonempty                          X → 244 (filtered domain) Y ✅ 241 (forward image)
0 < internalEdges.card              depends on IsNonempty (#4) + #2 (per 237)
0 < complementEdges.card            hardest (strict properness), unstarted
```

## Note

The next front is a **filtered-domain `X.IsNonempty` local theorem**
(`selectedOuterRaw_isNonempty_of_mem_forestChoiceCarrier` — body-244): from `p ≠ p_R` a component tagged `inl true`
(→ `leftOf` nonempty) or `inr B` (→ `promotedOf` nonempty via `s.promotedElements`, no `promote_collapse` floor, though
`B`'s properness supplies `B.elements.Nonempty` for the image step) gives `selectedOuterRawOf ⟨A,p⟩` nonempty via
`union_isNonempty` (body-240).  Then a **restricted membership adapter** (body-245) swaps the consumer to the filtered
domain, removing the false total membership field while keeping the total helper functions.  The `p_R` boundary stays
with `EmptyPivot`.  No declarations beyond this docstring anchor; the import keeps the map honest against the source.
No facade, no flat term, no `forgetHopf`.
-/
