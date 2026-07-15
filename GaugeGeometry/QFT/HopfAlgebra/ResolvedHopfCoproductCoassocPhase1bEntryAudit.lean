import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocGeometryFloorAssembly

/-!
# R-6c-body-301 — phase-1b entry audit: the concrete inhabitant campaign begins (scout)

Three-hundred-and-first genuine-body step, a phase-1b entry-audit scout (no new geometry).  With the round-trip layer
closed at its eight-fact floor (body-299/300), the work changes character: no longer reducing leaves into new records,
but INHABITING the fields of `coassoc_gen_of_geometry_floor` from a concrete resolved model.  This body fixes the full
input surface into three groups and the critical path.  Imports body-299 so the audit stays honest against the target.

## The target's full input tree

`coassoc_gen_of_geometry_floor (A : ResolvedRecoveredPreimageValueGeometryFloorSupply F V) (carrier_isProperForest)
(rep) (repCD) (rep_gen) (x)`.  Unpacking `A` + `F` + `V` + base leaves (all VERBATIM in the source):

```text
FloorSupply(299) = Data + 8 floor facts
  Data(283)      = Tags + forest_nonempty + mixed_ne_pR + mixed_ne_pL
    Tags(282)    = Closure + forestTag + 3 exclusivities (right_notMem_left, forest_notMem_left, forest_notMem_right)
      Closure(281) = Assembly + selected(F) + 3 pairwise disjoint + recovered_raw_mem
        Assembly(280) = Region + Left + 6 sound/complete (right/forest/left × sound/complete)
          Region(277) = componentToRight/rightComponentCD/rightComponentDisjoint + componentToForest/…
          Left(279)   = representedInQuotient (opaque Prop)
  F(245)  = selectedOuter_mem
  V(252)  = Measure + Survivor + Remnant + quotientForestRaw + hcross + union_eq + hRdisj + quot_eq
  base    = carrier_isProperForest, rep, repCD, rep_gen
  carrier D(ResolvedHopfCoproductSupply.lean:128) = carrier/starOf/hCD/carrier_mapPerm/star_mapPerm — NOT inhabited yet
```

## GROUP 1 — canonical / free (the real free cluster is thin)

Only two fields have proved concrete providers:

```text
carrier_isProperForest   PROVED  ResolvedCanonicalCarrierProperSupply.toCarrierProperProvider (CanonicalCarrierProper.lean:91)
V.Survivor               concrete resolvedConcreteRightSurvivorSupply (ConcreteSurvivor.lean:60, needs a nonempty witness)
```

Existing `resolvedConcrete*` providers (the whole list): `resolvedConcreteForestPromoteSupply` (Cross.lean:64),
`resolvedConcreteRightSurvivorSupply` (ConcreteSurvivor.lean:60), `resolvedConcreteLeftSelectionSupply`
(LeftSelectConcrete.lean:74), `resolvedConcreteSelectedOuterImageSupply` (SelectedOuterMem.lean:48).  There is NO concrete
`ResolvedConcreteSummandBundleSupply` / `…ValueSupply` (V) / region construction / `ResolvedMeasureLeafSupply` /
`ResolvedRemnantTransportSupply` / `ResolvedCoproductProperForestData` (`D`).  The `.ofLegacy` / `.toValueCore` reducts
(ConcreteSummandValue.lean:122, RegionConstructionValue.lean:110, LeftResidualValueBridge.lean:75) are migration checks
that consume an already-built input — NOT builders, and off the canonical path.

## GROUP 2 — concrete region geometry (real lemmas; most have total-root analogues to re-key)

```text
survivor_sound/complete_value (293)        SurvivorMemTagReduction.lean:105 (total survivor_mem)
remnant_sound/complete_value  (294)        RemnantMemTagReduction.lean:115  (total remnant_mem)
forest_parent_mem_value       (297)        body-185 forestComponentMem
represented_forest_complete_value (298)    body-180 represented_cases
Assembly 6 sound/complete                  body-173 recovered_region_membership_value re-key
Tags 3 exclusivities                       region-disjointness geometry (consumed by recoverChoiceValue)
forestTag_agrees (295) / promote_collapse (296)   floor pins — genuinely new (de-contraction / occurrence)
mixed_ne_pR / mixed_ne_pL / forest_nonempty       honest classifier leaves — new
Closure 3 pairwise disjoint                 new until representedInQuotient is concretized (see critical path)
```

## GROUP 3 — carrier / model closure (the phase-1b payload work)

```text
F.selectedOuter_mem (245)        constructed selected outer ∈ canonical carrier      (deferred, leaf 128)
Closure.recovered_raw_mem (269)  constructed region union ∈ canonical carrier        (deferred, leaf 159)
Closure.selected                 = F
Left.representedInQuotient        opaque Prop — NO concrete definition — the KEYSTONE (must become the image predicate)
rep / repCD / rep_gen            representative lift — payload work
carrier D                        NOT inhabited — must be CONSTRUCTED from a finite proper-forest index, not Finset.univ
```

## Critical path

The single hardest genuinely-new obligation, and the shared unlock, is **concretizing `Left.representedInQuotient` as the
survivor/remnant image predicate.**  Once it is the image predicate, the Closure three pairwise disjointnesses (158) and
`recovered_raw_mem` (159) both reduce (via `mem_properDisjointAdmissibleDivergentSubgraphs`) to "the three regions are
pieces of one canonical member," and `selectedOuter_mem` (128) follows upstream.  It sits above the deferred round-trip /
promote geometry (bodies 156/157/224/226) and the carrier construction.

## Confirmations (guards for the phase-1b DAG)

* NO all-proper `Finset.univ` carrier — no `Fintype (ResolvedAdmissibleSubgraph G)`; a canonical `D` must be constructed
  from a finite proper-forest index (`ResolvedProperForestFiniteIndex`), not enumerated (body-267 verdict).
* NO legacy `Forward` / total selected outer on the canonical path (RoundTripFloorComplete.lean:57; V drops `Forward`).
* NO new mega-bundle yet: the concrete providers are assembled incrementally, free cluster first.

## Recommended phase-1b DAG

```text
301 exact input audit (this body)
302 canonical/free provider assembly (carrier_isProperForest + V.Survivor + the resolvedConcrete* base)
303+ concretize representedInQuotient (image predicate) — the keystone
...  concrete region right/survivor + forest/remnant de-contraction geometry (Group 2 re-keys)
...  carrier closure + equivariance + selectedOuter_mem / recovered_raw_mem (Group 3)
→ concrete geometry-floor inhabitant → coassoc_gen_of_geometry_floor → full resolved coassociativity
```

Design discipline carried from the reduction campaign: do NOT mix value / membership / identity; do NOT strengthen a
generic statement past its live domain; do NOT treat a subtype's proof field as free.

Per the HALT: this is a docstring audit only; the import keeps it honest against body-299.  No declarations beyond this
docstring; no facade, no flat term, no `forgetHopf`.
-/
