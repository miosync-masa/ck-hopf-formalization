import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSelectedOuterMem
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCarrierProperProvider
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecoveredOuterDisjointCarrierScout
import GaugeGeometry.QFT.HopfAlgebra.ResolvedPayloadModel

/-!
# R-6c-body-227 — canonical-carrier base scout: only `carrier_isProperForest` (137) is a free win; 128/158/159 stay genuine

Two-hundred-and-twenty-seventh genuine-body step, a scout of whether instantiating the abstract carrier `D` to the
**canonical** carrier discharges the four floor leaves at once (`selectedOuter_mem` 128, `carrier_isProperForest` 137,
the three cross-disjointnesses 158, `recovered_outer_mem` 159).  Verdict: **NO — the canonical carrier is a
repackaging, not a discharge.** Exactly one leaf (137) is a genuine free win; the other three remain
construction-specific obligations even under the canonical carrier, because they are `∈ carrier` (or cross-disjoint)
statements about **constructed** objects whose properness / disjointness loops back to the abstract
`componentToRight` / `componentToForest` / `representedInQuotient` geometry (bodies 156/157/224/226).  Imports the four
leaves' providers and the payload model to keep the map honest against the source.

## The canonical machinery (verbatim, file:line)

* `FeynmanGraph.properDisjointAdmissibleDivergentSubgraphs` — `Coproduct.lean:259`; membership characterization
  `mem_properDisjointAdmissibleDivergentSubgraphs` — `Coproduct.lean:267` (member ⟺ nonempty-disjoint-admissible-
  divergent ∧ HasNonemptyComponents ∧ `0 < internalEdges.card` ∧ HasPositiveInternalEdgesComponents — the flat
  `IsProperForest` bundle);
* `properDisjointAdmissibleDivergentSubgraphs_isPairwiseDisjoint` — `Coproduct.lean:294` — gives *within-member*
  component disjointness of a single `A`, **NOT** cross-region disjointness of three separately-built forests;
* `forget_mem_properDisjointAdmissibleDivergentSubgraphs` — `ResolvedCoproductIndex.lean:130` — takes
  `A.IsProperForest` as a *hypothesis* and lands in the **flat** carrier of `G.forget`;
* payload side: `ResolvedPayloadModel.ofFlatForest` (`ResolvedPayloadModel.lean:197`), `ofFlatForest_isProperForest`
  (`:236`, a real theorem transferring all five `IsProperForest` conditions), `canonicalCover` (`:429`) — but these
  build a `ResolvedProperForestFiniteCover`, **a different structure with no wiring into `D.carrier`**.

## No existing canonical `D`

There is **no** `def : ResolvedCoproductProperForestData` anywhere setting `carrier := …` — every occurrence is a
consumer (`variable {D}` / parameter).  The structure (`ResolvedHopfCoproductSupply.lean:128`) has only
`carrier / starOf / hCD / carrier_mapPerm / star_mapPerm` — no proper-forest / union / sub-forest closure.  A
canonical `D` must be **constructed** (likely `carrier G := ofFlatForest`-lift of the flat proper index, mirroring
`canonicalCover`); it does not yet exist.

## Per-leaf dischargeability against the canonical carrier

```text
(137) carrier_isProperForest  — FREE.
  Once carrier is the ofFlatForest-lift of the flat proper index, membership ⇒ IsProperForest is a projection
  (ofFlatForest_isProperForest, ResolvedPayloadModel.lean:236). The ONLY genuine free win.

(128) selectedOuter_mem  — NOT FREE.
  selectedOuterRawOf s = (leftOf s).union (promotedOf s) (cross s)  [Promote.lean:61-63], built from the abstract
  componentToRight/promote geometry. Only selectedOuterRawOf_vertices_subset is proved (SelectedOuterSubset.lean:40).
  A canonical carrier turns "∈ carrier" into "IsProperForest ∧ disjoint of the CONSTRUCTED union" via
  mem_properDisjointAdmissibleDivergentSubgraphs — that obligation is exactly the deferred abstract geometry.

(159) recovered_outer_mem  — NOT FREE.
  Identical status: the region union (leftResidual ∪ rightRecovered) ∪ forestRecovered must be shown a canonical
  member ⇒ proper ∧ pairwise-disjoint of a CONSTRUCTED object.

(158) three cross-disjointnesses  — NOT FREE.
  Cross-region disjointness needs the three regions to be pieces of ONE common carrier member (or
  representedInQuotient concretized as the image predicate). _isPairwiseDisjoint is intra-member only.
```

## The key obstruction, sharply

The canonical carrier **re-expresses** `∈ D.carrier` as `IsProperForest ∧ IsPairwiseDisjoint ∧ …` (via
`mem_properDisjointAdmissibleDivergentSubgraphs`); for a **constructed** object (`selectedOuterRawOf`, the region
union, the three regions) that obligation is still the properness / disjointness of the construction, which reduces to
the abstract `componentToRight` / `componentToForest` / `representedInQuotient` / promote geometry (bodies 156/157/224/226).
So the canonical carrier discharges **only** leaf 137 for free; it converts 128/158/159 from carrier-membership into
proper-forest+disjointness obligations on constructed regions **without eliminating them**.

## Assessment and plan

* **Do NOT build a single `ResolvedCanonicalCarrierBaseSupply` claiming all four** — three of the four fields would be
  real obligations wrapped in a `mem_properDisjointAdmissibleDivergentSubgraphs` rewrite, not discharges.
* **The productive banked win is leaf 137 alone.**  Recommended body-228 shape: a one-by-one adapter that (1)
  constructs the missing canonical `D` (`carrier G := ofFlatForest`-lift of the flat proper index), then (2) discharges
  `carrier_isProperForest` via `ofFlatForest_isProperForest` — a genuine free field.
* **For 128 / 159**: a `mem_properDisjointAdmissibleDivergentSubgraphs`-rewrite adapter can *reduce* the carrier
  membership to "the constructed forest is proper + pairwise-disjoint," leaving those as explicit sub-obligations tied
  to the construction geometry — reduce, do not claim free.
* **For 158**: defer until `representedInQuotient` is concretized as the image predicate (drags in the deferred
  round-trip geometry), then derive cross-disjointness from a common member's `_isPairwiseDisjoint`.

Per the HALT: no canonical-carrier construction body is entered; the exact free leaf (137) vs. the three genuine
obligations (128/158/159) are named, and the missing prerequisite (a constructed canonical `D`) is recorded.  This is
a documentation / scout anchor (like body-224 / body-226).  No declarations beyond this docstring.  No facade, no flat
term, no `forgetHopf`.
-/
