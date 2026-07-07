import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRegionPartitionDisjoint
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecoveredOuterMembership

/-!
# R-6c-body-226 — recovered-outer disjoint / carrier scout: both are abstract floor leaves (like `selectedOuter_mem`)

Two-hundred-and-twenty-sixth genuine-body step, a scout of whether the recovered-outer **pairwise disjointnesses**
(body-158) and the recovered-outer **carrier closure** (body-159) can be reduced/proved against the abstract carrier
`D`, or are genuine floor obligations.  Verdict: **both are abstract floor leaves** — the three cross-disjointnesses
are fresh structure fields (no region fact derives them) and `recovered_outer_mem` has exactly the status of
`selectedOuter_mem` (body-128).  This records the finding so the disjoint / carrier direction is not mistaken for a
shallow reduction.  Imports 158/159 to keep the map honest against the source.

## What 158/159 already are

* **body-158 `ResolvedRegionPartitionSupply`** is *already* the pairwise-disjoint provider.  Its three cross-region
  disjointnesses `left_right_disjoint` / `left_forest_disjoint` / `right_forest_disjoint` are **raw structure fields**;
  the only proved artifacts are the two body-153 *cross forms* it re-exports: `hcross_lr` (verbatim re-export of one
  field) and `hcross_lrf` (a trivial `Finset.mem_union` case-split dispatching to the other two).  No new content.
* **body-159 `ResolvedRecoveredOuterCarrierSupply`** is *already* the carrier-closure provider.  Its single field
  `recovered_outer_mem` (`… ∈ D.carrier G`) is a **raw field**, re-exported verbatim by `toRecoveredOuterMem`.

## Why neither reduces against abstract `D`

```text
Pairwise disjoint (158): NOT provable from region facts.
- leftResidual z = z.1.1.filterElements (¬ representedInQuotient z ·)   [body-157]
- rightRecovered / forestRecovered = ofElements (…image (componentToRight / componentToForest))   [body-156]
- To get left_right_disjoint one would need (a) representedInQuotient DEFINED as "is a componentToRight/Forest
  image" (so the filter and the images are complementary), and (b) A = z.1.1's own pairwise disjointness.
  representedInQuotient is an opaque abstract Prop field (body-157:70, unlinked to the images); A's disjointness is
  itself only a fielded primitive (carrier_isProperForest, body-137). So the cross-disjointnesses are fresh fields.
- The WITHIN-region disjointnesses rightComponentDisjoint / forestComponentDisjoint (body-156) are a DIFFERENT
  obligation (consumed by the two ofElements calls); they do not give the cross ones.

Carrier closure (159): D.carrier is abstract → genuine floor leaf.
- ResolvedCoproductProperForestData.carrier is an abstract Finset field with only starOf / hCD / carrier_mapPerm /
  star_mapPerm — NO proper-forest / union / sub-forest closure. (Confirmed by body-137: even carrier_isProperForest
  is a fresh primitive for abstract D.)
- There is NO carrier-closure principle for abstract D. The only closure machinery
  (forget_mem_properDisjointAdmissibleDivergentSubgraphs + …_isPairwiseDisjoint) acts on the FLAT canonical carrier
  properDisjointAdmissibleDivergentSubgraphs, not on D.carrier.
- So recovered_outer_mem is provable ONLY for the canonical carrier — exactly Case-A status of selectedOuter_mem
  (body-128), which likewise takes carrier membership as an explicit hypothesis.
```

## Assessment and plan

* **The three pairwise disjointnesses (158) are fresh abstract fields**, on par with `carrier_isProperForest`
  (body-137).  No shallow provider reduction exists against abstract `D`.
* **`recovered_outer_mem` (159) is a genuine floor leaf**, status **identical to `selectedOuter_mem` (body-128)**:
  both are Case-A carrier-membership supply hypotheses, dischargeable only for the canonical
  `properDisjointAdmissibleDivergentSubgraphs` carrier via `forget_mem_properDisjointAdmissibleDivergentSubgraphs`.
* **Only banked wins are structural/trivial** — body-153's `union_eq` (proved), 158's `hcross_lr` / `hcross_lrf`
  (trivial from the three fields).  A single `Finset.PairwiseDisjoint` bundling of the three would be pure
  repackaging (no proof content), so it is not pursued here.
* **The productive pivot is the canonical-carrier base instance** — instantiate
  `D.carrier := properDisjointAdmissibleDivergentSubgraphs`, then discharge all four
  (128 `selectedOuter_mem`, 137 `carrier_isProperForest`, 158 cross-disjointnesses, 159 `recovered_outer_mem`) at once
  via `forget_mem_properDisjointAdmissibleDivergentSubgraphs` + `…_isPairwiseDisjoint`.  Alternatively, if
  `representedInQuotient` is later made concrete (as the image predicate), the 158 cross-disjointnesses become
  derivable from `carrier_isProperForest` — but that drags in the deferred round-trip geometry and must be sequenced
  with it, not before.

Per the HALT: no disjointness / injectivity / carrier-closure body is entered; the exact floor leaves are named
(`left_right_disjoint` / `left_forest_disjoint` / `right_forest_disjoint`; `recovered_outer_mem` ≡ `selectedOuter_mem`).
This is a documentation / scout anchor (like body-224 / body-218).  No declarations beyond this docstring.  No facade,
no flat term, no `forgetHopf`.
-/
