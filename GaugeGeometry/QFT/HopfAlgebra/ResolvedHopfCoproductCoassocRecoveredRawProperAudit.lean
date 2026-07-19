import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSupportedWMembership
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocMultiStarRegionCross
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocHasNonemptyComponents
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocPositiveInternalEdges
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocInternalEdgesCardPos

/-!
# R-6c-body-428 — `recovered_raw_mem` normalized to `regionRawUnion.IsProperForest`; the 5-conjunct audit crystallized (PROVED)

Four-hundred-and-twenty-eighth genuine-body step — the sibling of body-427 for the OTHER carrier-closure gate.  The
carrier bundle `ResolvedMultiStarCarrierClosureBundleSupply` was `Closure` (body-427, DEMOTED) + `recovered_raw_mem`
(body-341): the raw recovered-outer union `regionRawUnion M F z` lies in `D.carrier G`.  Body-426's membership `iff`
normalizes any carrier membership over `W` to `ResolvedAmbientSupported ∧ forget.IsConnectedDivergent ∧ IsProperForest`,
so — after the two ambient block conditions — the SOLE residual carrier condition is `(regionRawUnion M F z).IsProperForest`.

This body crystallizes the body-235/238/243 conjunct audit as a **theorem**, individually classifying all five
`IsProperForest` conjuncts of the union (the guard forbids the forward-outer route of body-241, which is circular in a
membership derivation):

```text
1  IsNonempty                          HONEST region datum  (body-241's proof is forward-outer → circular here)
2  HasNonemptyComponents               THEOREM (generic)     hasNonemptyComponents_of_cdNonempty N A       (body-236)
3  0 < internalEdges.card              DERIVED (from 1 + 4)  internalEdges_card_pos_of_isNonempty          (body-239)
4  HasPositiveInternalEdgesComponents  THEOREM (generic)     hasPositiveInternalEdgesComponents_of_cdPositive P A (body-238)
5  0 < complementEdges.card            HONEST measure datum  strict properness A.internalEdges < G.internalEdges;
                                       only the non-strict `internalEdges_le` exists, and the sole positivity lemma
                                       `forget_complementEdges_card_pos` takes `IsProperForest` as hypothesis (circular).
```

* `isProperForest_of_isNonempty_complement` — the generic crystallization: for ANY resolved forest, `IsProperForest`
  reduces to exactly two honest inputs (`IsNonempty`, `0 < complementEdges.card`) given the two measure-leaf supplies
  (`cd_nonempty` / `cd_positiveInternalEdges`); conjuncts 2, 4 discharge generically and 3 is derived from 1 + 4.
* `regionRawUnion_mem_canonicalSupportedCarrier_of` — the `W`-specialization: over `canonicalSupportedCarrierProperSupply`,
  the raw recovered-outer union lies in the carrier as a THEOREM once given the ambient support/CD of the block AND the
  two honest region data.  This demotes `recovered_raw_mem` from an opaque model field to a derivation whose honest
  residuals are named: `IsNonempty` (conjunct 1) and `complementEdges` positivity (conjunct 5) — nothing more.

**Verdict on the battle line (`complementEdges.card > 0`): honest measure datum, NOT a theorem.**  It is strict
properness of the region inside the ambient graph; there is no structural/union reason a union of subgraphs leaves a
positive ambient complement, and the only two library facts are the non-strict `internalEdges_le` and the circular
`forget_complementEdges_card_pos`.

Per the HALT/guards: the forward-outer route (body-241 and later) is NOT used — conjunct 1 is taken as an honest input to
keep the derivation non-circular; conjuncts 2/4 come from the already-isolated measure leaves; `W`'s carrier definition is
not re-expanded (only the body-426 `iff` is consumed).  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO
strict `star_mapPerm` / `promote_collapse` / singleton / floor-297.
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

variable {G : ResolvedFeynmanGraph}

/-- **R-6c-body-428 — the `IsProperForest` conjunct audit, crystallized.**  For ANY resolved admissible forest,
`IsProperForest` reduces to exactly two honest inputs — component-set nonemptiness (conjunct 1) and positive ambient
complement (conjunct 5) — once the two measure-leaf supplies (`cd_nonempty`, `cd_positiveInternalEdges`) are in hand:
conjunct 2 (`HasNonemptyComponents`) and conjunct 4 (`HasPositiveInternalEdgesComponents`) discharge generically, and
conjunct 3 (`0 < internalEdges.card`) is DERIVED from conjuncts 1 + 4. -/
theorem isProperForest_of_isNonempty_complement
    (N : ResolvedConnectedDivergentNonemptySupply G)
    (P : ResolvedConnectedDivergentPositiveInternalEdgesSupply G)
    (A : ResolvedAdmissibleSubgraph G)
    (hNE : A.IsNonempty)
    (hCompl : 0 < A.complementEdges.card) :
    A.IsProperForest := by
  have hPos : A.HasPositiveInternalEdgesComponents :=
    hasPositiveInternalEdgesComponents_of_cdPositive P A
  exact ⟨hNE, hasNonemptyComponents_of_cdNonempty N A,
    A.internalEdges_card_pos_of_isNonempty hNE hPos, hPos, hCompl⟩

/-- **R-6c-body-428 ∎ — `recovered_raw_mem` demoted over `W`.**  The raw recovered-outer union
`regionRawUnion M F z` lies in the constructed canonical carrier as a THEOREM: body-426's membership `iff` reduces the
carrier condition to `ResolvedAmbientSupported ∧ forget.IsConnectedDivergent ∧ IsProperForest`, and the properness in
turn reduces (via `isProperForest_of_isNonempty_complement`) to the two honest region data.  So the model's opaque
`recovered_raw_mem` field is, over `W`, a derivation with named honest residuals: the ambient block support/CD, plus the
region's `IsNonempty` (conjunct 1) and `complementEdges` positivity (conjunct 5). -/
theorem regionRawUnion_mem_canonicalSupportedCarrier_of
    (N : ResolvedConnectedDivergentNonemptySupply G)
    (P : ResolvedConnectedDivergentPositiveInternalEdgesSupply G)
    (M : ResolvedMultiStarDecontractionSupply canonicalSupportedCarrierProperSupply.toData)
    (F : ResolvedCanonicalStarFacts canonicalSupportedCarrierProperSupply.toData)
    (z : ForestBlockCodType canonicalSupportedCarrierProperSupply.toData G)
    (hs : ResolvedAmbientSupported G)
    (hcd : G.forget.IsConnectedDivergent)
    (hNE : (regionRawUnion M F z).IsNonempty)
    (hCompl : 0 < (regionRawUnion M F z).complementEdges.card) :
    regionRawUnion M F z ∈ (canonicalSupportedCarrierProperSupply.index G).carrier :=
  (mem_canonicalSupportedCarrier_iff _).mpr
    ⟨hs, hcd, isProperForest_of_isNonempty_complement N P _ hNE hCompl⟩

end GaugeGeometry.QFT.Combinatorial
