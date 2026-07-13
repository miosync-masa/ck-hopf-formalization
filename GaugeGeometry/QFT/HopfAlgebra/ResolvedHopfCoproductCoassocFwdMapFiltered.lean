import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSelectedOuterFilteredMem
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocWitnessSplitConcrete

/-!
# R-6c-body-249 — the filtered forward map: `fwdMapFiltered` (migration cornerstone, PROVED)

Two-hundred-and-forty-ninth genuine-body step — the cornerstone of the `fwdMap` migration (body-248 verdict (3),
shallow).  A forward map on the **filtered** subtype domain whose carrier tag comes from body-245's honest filtered
membership (`mem_of_mem_forestBlockDomFinset`), **not** from the retired total root
`ResolvedForwardMapCoherenceSupply.selectedOuter_mem` (false at `p_R`).

## The map (total-root-independent at the membership level)

```lean
fwdMapFiltered (F : ResolvedSelectedOuterFilteredMemSupply D) (S : ResolvedConcreteSummandBundleSupply D)
    (q : FilteredForestBlockDom D G) : ForestBlockCodType D G :=
  ⟨⟨selectedOuterRawOf q.1, F.mem_of_mem_forestBlockDomFinset q.1 q.2⟩, S.quotientForest q.1⟩
```

The first component's carrier tag is `F.mem_of_mem_forestBlockDomFinset q.1 q.2` — the honest filtered obligation,
replacing `S.Forward.selectedOuter_mem` (the all-right-false total leaf).  The second component `S.quotientForest q.1`
is honest right-forest data of the summand bundle; its type mentions `(S.Forward.imageSupply …).selectedOuterOf q.1`,
but that is `rfl`-defeq to `selectedOuterRawOf q.1` (`ForwardMapCoherence.selectedOuter_eq`) — it never reads the
proof-irrelevant `.2` tag, so the dependent type aligns and the map is **membership-independent of the total root**.

## The companion equalities (both definitional)

```lean
fwdMapFiltered_outer_fst : (fwdMapFiltered F S q).1.1 = selectedOuterRawOf q.1        (rfl)
fwdMapFiltered_quotient  : HEq (fwdMapFiltered F S q).2 (S.quotientForest q.1)         (HEq.rfl)
```

## The legacy bridge (migration-only)

```lean
fwdMapFiltered_eq_legacy : fwdMapFiltered F S q = fwdMap S q.1        (rfl, by proof irrelevance on the tag)
```

This equality references the total `fwdMap` (via `S.Forward`) and exists **only** to let body-250 port the total
witnessSplit round-trip proofs verbatim onto the filtered domain.  It is not a field of any provider — deleting it
leaves `fwdMapFiltered` and its companions type-checking.  No dummy / total carrier element outside the domain (`p_R`
never applies; `EmptyPivot` carries the boundary cover-external).

Per the HALT: the filtered map + its `rfl` companions + the migration-only legacy bridge are defined/proved; no
round-trip law is restated (body-250), no provider field is changed.  No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

set_option linter.unusedSectionVars false

/-- **R-6c-body-249 — the filtered forward-map domain.**  The forest-block domain summands that actually occur in the
live sum (`p ≠ p_R`, `p ≠ p_L`). -/
abbrev FilteredForestBlockDom (D : ResolvedCoproductProperForestData) (G : ResolvedFeynmanGraph) :=
  {q : ForestBlockDomType D G // q ∈ forestBlockDomFinset G}

/-- **R-6c-body-249 — the filtered forward map.**  Carrier tag from the honest filtered membership (body-245), not
the retired total root.  Value formulas (`selectedOuterRawOf`, `quotientForest`) are the total helpers. -/
noncomputable def fwdMapFiltered (F : ResolvedSelectedOuterFilteredMemSupply D)
    (S : ResolvedConcreteSummandBundleSupply D) (q : FilteredForestBlockDom D G) :
    ForestBlockCodType D G :=
  ⟨⟨(resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf q.1,
      F.mem_of_mem_forestBlockDomFinset q.1 q.2⟩,
    S.quotientForest q.1⟩

/-- **R-6c-body-249 — the filtered map's outer forest is the raw selected outer** (`rfl`). -/
theorem fwdMapFiltered_outer_fst (F : ResolvedSelectedOuterFilteredMemSupply D)
    (S : ResolvedConcreteSummandBundleSupply D) (q : FilteredForestBlockDom D G) :
    (fwdMapFiltered F S q).1.1
      = (resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf q.1 :=
  rfl

/-- **R-6c-body-249 — the filtered map's quotient forest is the summand bundle's** (`HEq.rfl`). -/
theorem fwdMapFiltered_quotient (F : ResolvedSelectedOuterFilteredMemSupply D)
    (S : ResolvedConcreteSummandBundleSupply D) (q : FilteredForestBlockDom D G) :
    HEq (fwdMapFiltered F S q).2 (S.quotientForest q.1) :=
  HEq.rfl

/-- **R-6c-body-249 — the migration-only legacy bridge** (`rfl`, proof irrelevance on the carrier tag).  Lets body-250
port the total witnessSplit round-trip proofs verbatim.  Not a provider field. -/
theorem fwdMapFiltered_eq_legacy (F : ResolvedSelectedOuterFilteredMemSupply D)
    (S : ResolvedConcreteSummandBundleSupply D) (q : FilteredForestBlockDom D G) :
    fwdMapFiltered F S q = fwdMap S q.1 :=
  rfl

end GaugeGeometry.QFT.Combinatorial
