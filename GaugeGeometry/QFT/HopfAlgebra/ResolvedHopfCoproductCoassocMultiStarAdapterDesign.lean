import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocLocalizedParentDisjoint

/-!
# R-6c-body-331 — multi-star choice-adapter design: DIRECT re-key, gate set, forestTag_agrees demotion (judgment)

Three-hundred-and-thirty-first genuine-body step — the design scout for wiring the multi-star de-contraction geometry
(localizedParent / innerRaw / M3 / D4, bodies 316-330) into the OLD Region/Tags/choice structure, so that `forestTag`
becomes a CONSTRUCTION and `forward_outer_value` is re-proved via D5+M3 without floor-297.  Verdict: the adapter is a
DIRECT re-key of the existing Region (no structural rebuild), with ONE new carrier gate; `forestTag_agrees` demotes to a
theorem but needs one full-forest round-trip leaf.

## The adapter is a DIRECT re-key (no new Region)

`forestDomain z = z.2.1.elements.filter (¬ Disjoint · (starOfZ z))` (RegionConstructionFromSector.lean:88) is EXACTLY the
star-touching quotient components — the `δ`'s that Front-1 (`localizedParent`/`innerRaw`/M3/D4) ranges over
(`localizedParent_ne`'s `htouch`).  `forestRecovered z .elements = (forestDomain z).attach.image (componentToForest z)`
(RegionConstructionValue.lean:99).  So set:

```text
componentToForest z δ  :=  localizedParentWithTouchedLegs z δ (legLift z δ) hE hL   -- both ResolvedFeynmanSubgraph G
forestTag z γ h        :=  ⟨innerRaw z δ …, innerRaw_mem z δ⟩ : (D.supply (γ.1.toResolvedFeynmanGraph)).ForestIdx
    where δ is the UNIQUE forestDomain witness with componentToForest z δ = γ.1
          (existence: forestRecovered_elements_eq + Finset.mem_image;  uniqueness: D4 localizedParent_ne)
```

`forestTag`'s target `(D.supply (γ.1.toResolvedFeynmanGraph)).ForestIdx = {A // A ∈ D.carrier (γ.1.toResolvedFeynmanGraph)}`
(Supply.lean:151); with `γ.1 = localizedParent δ`, `innerRaw δ : ResolvedAdmissibleSubgraph (localizedParent δ).toResolvedFeynmanGraph`
lands EXACTLY when `innerRaw_mem : innerRaw δ ∈ D.carrier (localizedParent δ).toResolvedFeynmanGraph` holds.

## The complete carrier/CD gate set

```text
innerRaw_mem            innerRaw δ ∈ D.carrier (localizedParent δ).toResolvedFeynmanGraph     ← GENUINELY NEW (ForestIdx landing)
parentCD                (localizedParent δ).forget.IsConnectedDivergent                       = forestComponentCD (RegionConstructionValue:64) = M2b datum (322)
forestComponentDisjoint pairwise-disjoint forest image                                        = D4 localizedParent_pairwiseDisjoint (330)
recovered_raw_mem       recovered outer ∈ D.carrier G                                          unchanged (already in unionOuterValue, Group-3)
[exclusivities]         right_notMem_left / forest_notMem_left / forest_notMem_right           Region closure leaves — SEPARATE front (right/left cross-disjointness)
```
`parentCD` and `forestComponentDisjoint` are DISCHARGED by the existing M2b datum and D4; only `innerRaw_mem` is a new
supply field.  Proposed root (localizedParent/innerRaw/M3 derived, NOT re-fielded):

```lean
structure ResolvedMultiStarDecontractionSupply where
  legLift     : ∀ {G} (z) (δ), ResolvedTouchedLegLiftDatum z δ
  parentCD    : ∀ {G} (z) (δ), (localizedParentWithTouchedLegs z δ (legLift z δ) hE hL).forget.IsConnectedDivergent
  innerRaw_mem : ∀ {G} (z) (δ), innerRaw z δ (legLift z δ) hE hL ∈ D.carrier (localizedParentWithTouchedLegs z δ (legLift z δ) hE hL).toResolvedFeynmanGraph
```
(hE/hL threaded from a payload well-formedness datum.)

## `forestTag_agrees` demotes to a THEOREM — with one full-forest round-trip leaf

`forestTag_agrees` (ForestValueEqValue.lean:100-105) : on `z = fwd q`, `forestTag (fwd q) γ = forestTag_fwd_value q γ`
where `forestTag_fwd_value = (parent_recovered_value) ▸ occurrence.B` (the choiceAt-recovered domain `B`).  With the
constructed `forestTag := ⟨innerRaw δ, innerRaw_mem⟩`, this becomes the geometric identity `innerRaw δ =
(parent_recovered_value) ▸ occurrence.B` as `ForestIdx` VALUES (full `ResolvedAdmissibleSubgraph` + carrier membership).
M3 (`promote_innerRaw_elements`) gives only `.elements`-level equality of the PROMOTED collection; the value-level
`innerRaw δ = occurrence.B` needs a full-forest (not just `.elements`) de-contraction round-trip identifying
`occurrence.B` with the `δ`-induced quotient sub-forest of `γ`.  So `forestTag_agrees` is NO LONGER an opaque datum — it
is a THEOREM modulo this single full-forest round-trip leaf (body-332+ target), a strict improvement over the retired
"opaque field" status (body-295).

## Forward-outer element equality is MECHANICAL (D5 + M3)

`promotedComponentElements s γ = (promote γ.1 B.1).elements` on `inr B` (PromotedOf.lean:54-60) — LITERALLY M3's LHS.
Under the touched choice (`γ.1 = localizedParent δ`, `B.1 = innerRaw δ`): `promotedComponentElements = touchedOuterComponents z δ`
(M3), `promotedElements = (forestDomain z).biUnion (touchedOuterComponents z) = representedForestTouched z`
(RepresentedByTouched.lean:98), and with `leftOf = leftResidualTouched`,
`selectedOuterRawOf.elements = leftResidualTouched z ∪ representedForestTouched z = z.1.1.elements` by D5
`touched_coverage` (323).  The only extra coherence: aligning `s.choiceAt`'s `inl`/`inr` split with the
untouched/touched (`representedByTouched`) partition + the promote-supply `cross`.  No floor-297, no singleton collapse.

Per the HALT: design judgment pin only — the adapter re-key, gate set, `forestTag_agrees` demotion, and forward-outer
skeleton are recorded; NO adapter is built; `forestTag_agrees` is NOT re-fielded as a datum; `innerRaw_mem` is named as
the single new carrier gate (NOT extracted free); the parent-image witness uses D4 uniqueness; right/left cross-disjointness
and Front 2 are OUT of scope; no facade, no flat term, no `forgetHopf`.  STATUS: M3/D4 PROVED, but the adapter construction
+ the full-forest round-trip leaf + `innerRaw_mem` + the forward-outer assembly remain — Front-1 is NOT yet assembled.
-/
