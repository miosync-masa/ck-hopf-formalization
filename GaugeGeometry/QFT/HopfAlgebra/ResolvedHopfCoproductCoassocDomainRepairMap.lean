import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSelectedOuterFilteredMem
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocInternalEdgesCardPos

/-!
# R-6c-body-247 — domain-repair map: bodies 244–246 (docs anchor)

Two-hundred-and-forty-seventh genuine-body step, a documentation anchor (no new geometry).  It fixes a clear
milestone: the selected-outer domain defect is repaired at its source, and four of the five `IsProperForest` conjuncts
are discharged for both constructed forests.  Imports body-245/246 so the map stays type-checked.  Reader-facing
narrative: `CK_HOPF_FORMALIZATION_MAP.md` §"R-6c bodies 244–246"; proof-dependency map:
`CK_HOPF_DEPENDENCY_GRAPH.md` §"R-6c bodies 244–246".

## The two headline facts

```text
The selected-outer domain defect is repaired at its source:
the carrier-tagged selected outer is now defined only on the filtered forest-block domain.

Four of the five IsProperForest conjuncts are now discharged for both the selected and recovered outer
constructions; only strict complement-edge properness remains.
```

## Bodies 244–246

```text
244  selectedOuterRaw_isNonempty_of_mem_forestChoiceCarrier (P) (hp : p ∈ forestChoiceCarrier A)
       : (selectedOuterRawOf ⟨A, p⟩).IsNonempty      -- X.IsNonempty from p ≠ p_R alone
     inl true → leftOf nonempty; inr B → promotedOf nonempty (carrier_isProperForest on B); union_isNonempty.
     No EmptyPivot / body-151 / promote_collapse / total selectedOuter_mem.

245  ResolvedSelectedOuterFilteredMemSupply (NEW ROOT, total-supply-independent):
       selectedOuter_mem : ∀ {G} A p, p ∈ forestChoiceCarrier A → selectedOuterRawOf ⟨A, p⟩ ∈ D.carrier G
     selectedOuterOfForestChoice (filtered sigma) ; .1 = selectedOuterRawOf ⟨q.1, q.2.1⟩  (rfl)
     mem_of_mem_forestBlockDomFinset : q ∈ forestBlockDomFinset G → selectedOuterRawOf q ∈ D.carrier G
       (reconnects to the sum consumer ResolvedForestBlockBijectionSupply, which already carries hq).

246  internalEdges_card_pos_of_isNonempty (A) (hA : A.IsNonempty) (hPos : A.HasPositiveInternalEdgesComponents)
       : 0 < A.internalEdges.card                     -- witness component → aggregate edge (mem_internalEdges)
```

## The retired total root

```text
The total selectedOuter_mem : ∀ s is RETIRED, not merely unproved:
it is FALSE at the all-right split p_R for the canonical carrier (selectedOuterRawOf p_R = ∅ ∉ D.carrier G).
The honest obligation is the filtered ResolvedSelectedOuterFilteredMemSupply.selectedOuter_mem (body-245);
the p_R boundary is carried cover-external by EmptyPivot.
```

## Status table (the five `IsProperForest` conjuncts, both constructed forests)

```text
HasNonemptyComponents               X ✅ 236   Y ✅ 236     generic
HasPositiveInternalEdgesComponents  X ✅ 238   Y ✅ 238     generic (new measure leaf cd_positiveInternalEdges)
0 < internalEdges.card              X ✅ 246   Y ✅ 246     generic (IsNonempty + positive components)
IsNonempty                          X ✅ 244   Y ✅ 241     filtered domain / forward image
0 < complementEdges.card            X — Y —    the ONLY remaining conjunct (strict properness)
```

## Note

Only `0 < complementEdges.card` (strict `A.internalEdges < G.internalEdges`) remains among the `isProper` conjuncts,
plus `recovered_eq` (the certificate section).  The chain still references the retired total root
`ResolvedForwardMapCoherenceSupply.selectedOuter_mem` (`ForwardMapCoherence.lean:72`) at `fwdMap` and the backward /
bijection layer — a **migration boundary**, not new mathematics (`p_R` is never applied in any live sum).  The next
front is a `fwdMap` filtered-domain migration scout (blast radius + minimal migration boundary), then the strict
`complementEdges` conjunct.  No declarations beyond this docstring anchor; the import keeps the map honest against the
source.  No facade, no flat term, no `forgetHopf`.
-/
