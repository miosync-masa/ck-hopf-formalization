import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecoveredRawProperAudit
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocQuotientPartitionMulti
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocIsNonemptyTransfer
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCarrierProperProvider
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCanonicalCarrierProper

/-!
# R-6c-body-429 — `regionRawUnion.IsNonempty` is a region-specific THEOREM (conjunct 1 falls); conjunct 5 audited (PROVED)

Four-hundred-and-twenty-ninth genuine-body step — sharpening body-428's conservative ledger by one notch.  Body-428
reduced `recovered_raw_mem` (over `W`) to the two honest region data `IsNonempty` (conjunct 1) and `complementEdges`
positivity (conjunct 5).  This body **promotes conjunct 1 from an honest datum to a region-specific theorem**, using
only the quotient forest's properness and the star-filter partition (body-344) — NO forward-outer route (body-241's proof
is circular in a membership derivation), NO `recovered_raw_mem`.

```text
z.2.1.elements.Nonempty                          (P.carrier_isProperForest _ z.2.1 z.2.2).1  — quotient forest B is proper
  = (rightDomain z ∪ forestDomain z).Nonempty    rightDomain_union_forestDomain (body-344, pure star-filter partition)
  → rightDomain nonempty  → rightReembed image  → (rightRegion z).IsNonempty  → union nonempty
  ∨ forestDomain nonempty → M.parent   image    → (forestRegion M F z).IsNonempty → union nonempty
```

* `regionRawUnion_isNonempty` — for ANY `D` with a `ResolvedCarrierProperProvider`, the raw recovered-outer union is
  nonempty (conjunct 1, region-specific THEOREM).  The witness comes from whichever partition half is inhabited, lifted
  through `rightReembed` / `M.parent` and injected into the triple union by `union_isNonempty_left/right` (body-240).
* `regionRawUnion_isProperForest_of_complement` — `IsProperForest` for the union now needs ONLY conjunct 5: conjuncts
  1/2/4 discharge (1 here, 2/4 generic), 3 is derived.  So the SOLE remaining honest input is `0 < complementEdges.card`.
* `regionRawUnion_mem_canonicalSupportedCarrier_of_complement` — the `W`-specialization: carrier membership of the raw
  recovered-outer union from the block's ambient support/CD PLUS the single complement datum (conjunct 1 discharged via
  `W.toCarrierProperProvider`).  Supersedes body-428's version by dropping the `IsNonempty` hypothesis.

## Conjunct-5 audit (`0 < complementEdges.card`) — region-specific verdict PENDING (conservative)

Generically this does not fall (body-428): a union of subgraphs can saturate the ambient internal edges.  Region-specifically
it is a *candidate* along the quotient-residual route, but NOT yet a theorem, and it is left as `hCompl` rather than sold
to a bare-positivity model field:

```text
Target: exhibit e ∈ regionRawUnion.complementEdges = G.internalEdges - regionRawUnion.internalEdges.
Route : the quotient carrier gives a residual quotient edge e_q ∈ (contractedAmbient).internalEdges \ z.2.1.internalEdges
        (strict properness of B in the quotient, body-428 conjunct-5 at the quotient level); lift e_q along the
        outer-complement preimage to e ∈ G.internalEdges and show e ∉ leftRegion/rightRegion/forestRegion internal edges
        (left: untouched-residual filter; right: e_q ∈ δ.internalEdges contradiction; forest: touched/retarget-preimage).
Blockers named: needs q-local `EdgeIdsUnique` + retarget residual injectivity to pin the preimage; the strict-properness
        source at the quotient level is itself the conjunct-5 datum one level down — so the honest reduction is to a
        *minimal quotient-residual edge lift/separation datum*, NOT bare positivity.  Deferred to a dedicated body.
```

So the sharpened ledger is:

```text
IsNonempty          region-specific THEOREM (this body)           — regionRawUnion_isNonempty
complementEdges>0   region-specific verdict PENDING (audited)     — reduces to a quotient-residual edge lift/separation datum
```

Per the HALT/guards: the forward-outer route (body-241+) is NOT used; conjunct 1 closes from the quotient forest's own
properness + the partition; `W`'s carrier definition is not re-expanded (only body-426 `iff` + body-428 reduction are
consumed); conjunct 5 is NOT sold to a bare-positivity field — it stays an explicit hypothesis with its reduction target
named.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO strict `star_mapPerm` / `promote_collapse` /
singleton / floor-297.
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

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-body-429 — conjunct 1 for the raw recovered-outer union, region-specifically.**  The quotient forest `z.2.1`
is proper (carrier member `z.2.2`), so its component set is nonempty; the star-filter partition (body-344) splits that
into `rightDomain ∪ forestDomain`, and whichever half is inhabited lifts (through `rightReembed` / `M.parent`) to a
component of `rightRegion` / `forestRegion`, hence of the triple union.  No forward-outer, no `recovered_raw_mem`. -/
theorem regionRawUnion_isNonempty (P : ResolvedCarrierProperProvider D)
    (M : ResolvedMultiStarDecontractionSupply D) (F : ResolvedCanonicalStarFacts D)
    (z : ForestBlockCodType D G) :
    (regionRawUnion M F z).IsNonempty := by
  have hne : (z.2.1.elements).Nonempty := (P.carrier_isProperForest _ z.2.1 z.2.2).1
  rw [← rightDomain_union_forestDomain z] at hne
  unfold regionRawUnion recoveredRawUnion
  rcases Finset.union_nonempty.mp hne with hR | hF
  · -- right survivor → `rightRegion`, injected as the right of the inner union
    apply ResolvedAdmissibleSubgraph.union_isNonempty_left
    apply ResolvedAdmissibleSubgraph.union_isNonempty_right
    show ((rightRegion z).elements).Nonempty
    rw [rightRegion_elements]
    exact Finset.image_nonempty.mpr (Finset.attach_nonempty_iff.mpr hR)
  · -- forest remnant → `forestRegion`, injected as the right of the outer union
    apply ResolvedAdmissibleSubgraph.union_isNonempty_right
    show ((forestRegion M F z).elements).Nonempty
    rw [forestRegion_elements]
    exact Finset.image_nonempty.mpr (Finset.attach_nonempty_iff.mpr hF)

/-- **R-6c-body-429 — `IsProperForest` for the raw recovered-outer union, needing ONLY conjunct 5.**  With conjunct 1
now a region theorem (`regionRawUnion_isNonempty`), conjuncts 2/4 generic and 3 derived, the sole remaining honest input
is the ambient complement positivity `hCompl`. -/
theorem regionRawUnion_isProperForest_of_complement
    (Nne : ResolvedConnectedDivergentNonemptySupply G)
    (Ppos : ResolvedConnectedDivergentPositiveInternalEdgesSupply G)
    (Pcp : ResolvedCarrierProperProvider D)
    (M : ResolvedMultiStarDecontractionSupply D) (F : ResolvedCanonicalStarFacts D)
    (z : ForestBlockCodType D G)
    (hCompl : 0 < (regionRawUnion M F z).complementEdges.card) :
    (regionRawUnion M F z).IsProperForest :=
  isProperForest_of_isNonempty_complement Nne Ppos _
    (regionRawUnion_isNonempty Pcp M F z) hCompl

/-- **R-6c-body-429 ∎ — `recovered_raw_mem` over `W`, needing ONLY the complement datum.**  Superseding body-428: the
raw recovered-outer union lies in the constructed canonical carrier from the block's ambient support/CD plus the single
honest region datum `0 < complementEdges.card`; conjunct 1 is discharged region-specifically via
`W.toCarrierProperProvider`. -/
theorem regionRawUnion_mem_canonicalSupportedCarrier_of_complement
    (Nne : ResolvedConnectedDivergentNonemptySupply G)
    (Ppos : ResolvedConnectedDivergentPositiveInternalEdgesSupply G)
    (M : ResolvedMultiStarDecontractionSupply canonicalSupportedCarrierProperSupply.toData)
    (F : ResolvedCanonicalStarFacts canonicalSupportedCarrierProperSupply.toData)
    (z : ForestBlockCodType canonicalSupportedCarrierProperSupply.toData G)
    (hs : ResolvedAmbientSupported G)
    (hcd : G.forget.IsConnectedDivergent)
    (hCompl : 0 < (regionRawUnion M F z).complementEdges.card) :
    regionRawUnion M F z ∈ (canonicalSupportedCarrierProperSupply.index G).carrier :=
  (mem_canonicalSupportedCarrier_iff _).mpr
    ⟨hs, hcd, regionRawUnion_isProperForest_of_complement Nne Ppos
      canonicalSupportedCarrierProperSupply.toCarrierProperProvider M F z hCompl⟩

end GaugeGeometry.QFT.Combinatorial
