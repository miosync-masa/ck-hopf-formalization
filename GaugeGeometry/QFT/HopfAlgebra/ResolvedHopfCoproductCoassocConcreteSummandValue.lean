import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocFwdMapFiltered

/-!
# R-6c-body-252 — the value-only summand bundle: dropping the retired total root `Forward` (PROVED)

Two-hundred-and-fifty-second genuine-body step — the structural extraction that removes the retired total root from the
summand bundle.  `ResolvedConcreteSummandBundleSupply` has `Forward : ResolvedForwardMapCoherenceSupply D` as a
**required** field (`ConcreteSummandBundle.lean:82`) whose sole leaf `selectedOuter_mem : ∀ s` is false at `p_R` — so
the bundle is not canonically inhabitable.  This body plants an **independent value-only root**
`ResolvedConcreteSummandValueSupply` that **drops `Forward`** and retypes `quotientForest` / `quot_eq` directly via
`selectedOuterRawOf` (`rfl`-defeq to the old types by `ForwardMapCoherence.selectedOuter_eq`), so no field references
the total root.

## The value root (no `Forward`)

```lean
structure ResolvedConcreteSummandValueSupply (D) where
  Measure  : ResolvedMeasureLeafSupply D
  Survivor : ResolvedRightSurvivorTransportSupply D
  Remnant  : ResolvedRemnantTransportSupply D
  quotientForestRaw : ∀ {G} q, (D.supply ((selectedOuterRawOf q).contractWithStars (D.starOf G (selectedOuterRawOf q)))).ForestIdx
  hcross / union_eq / hRdisj / quot_eq       -- all via selectedOuterRawOf / Survivor / Remnant, total-root-free
```

`Measure` / `Survivor` / `Remnant` are Forward-free (they never mention `selectedOuterOf` / `selectedOuter_mem`).
`quotientForestRaw`'s type is **exactly defeq** to the old `quotientForest` (`selectedOuter_eq` is `rfl` in both the
`contractWithStars` receiver and the `starOf` argument), so the legacy assignment is `rfl`.

## The value forward map and its `rfl` projections

`fwdMapFilteredValue F V q = ⟨⟨selectedOuterRawOf q.1, F.mem_of_mem_forestBlockDomFinset q.1 q.2⟩, V.quotientForestRaw q.1⟩`
— the body-249 map with the value root in the second component.  `_outer_fst` is `rfl`; `_quotient` is `HEq.rfl`.

## The migration-check `.ofLegacy` and the `rfl` bridge

`ResolvedConcreteSummandValueSupply.ofLegacy S` assembles the value root from a legacy bundle by **plain defeq
field-by-field assignment** (no cast).  The bridge `fwdMapFilteredValue F (ofLegacy S) q = fwdMapFiltered F S q` is
`rfl` (same first component; second components `S.quotientForest q.1` defeq).  These are migration-check only — the
value root itself carries no `Forward`.

## Residual (body-253)

Re-pointing the branch record (body-251) and cover (body-250) from `fwdMapFiltered F S` onto `fwdMapFilteredValue F V`
is what actually eliminates `S.Forward` from the downstream chain; that is body-253.  A value-side `summand_agree` /
`quot_eq` restatement (the term-agreement path, `ConcreteSummandBundle.lean:114-139`) follows.

Per the HALT: the value root + value map + `rfl` projections + the migration-check `.ofLegacy` / bridge are
defined/proved; no downstream record is re-pointed yet; no field of the value root references the retired total root.
No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData}

set_option linter.unusedSectionVars false

/-- **R-6c-body-252 — the value-only summand bundle.**  Drops the retired total root `Forward`; `quotientForestRaw` /
`quot_eq` are typed via `selectedOuterRawOf` (defeq to the old `Forward`-phrased types). -/
structure ResolvedConcreteSummandValueSupply (D : ResolvedCoproductProperForestData) where
  /-- The measure leaves (Forward-free). -/
  Measure : ResolvedMeasureLeafSupply D
  /-- The right-survivor transport (Forward-free). -/
  Survivor : ResolvedRightSurvivorTransportSupply D
  /-- The remnant transport (Forward-free). -/
  Remnant : ResolvedRemnantTransportSupply D
  /-- The quotient forest index, typed via `selectedOuterRawOf` (no `Forward`). -/
  quotientForestRaw : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G),
    (D.supply (((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf q).contractWithStars
      (D.starOf G ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf q)))).ForestIdx
  /-- The survivor/remnant cross-disjointness. -/
  hcross : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G),
    ∀ γ ∈ (Survivor.survivor.rightSurvivorForest q).elements,
    ∀ δ ∈ (Remnant.remnant.remnantForest q).elements, γ ≠ δ → γ.Disjoint δ
  /-- The quotient forest decomposes as survivor ∪ remnant. -/
  union_eq : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G),
    (quotientForestRaw q).1
      = (Survivor.survivor.rightSurvivorForest q).union (Remnant.remnant.remnantForest q) (hcross q)
  /-- Survivor and remnant are disjoint. -/
  hRdisj : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G),
    Disjoint (Survivor.survivor.rightSurvivorForest q).elements
      (Remnant.remnant.remnantForest q).elements
  /-- The right-term agreement, typed via `selectedOuterRawOf` (no `Forward`). -/
  quot_eq : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G),
    (D.supply G).rightTerm q.1
      = (D.supply (((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf q).contractWithStars
          (D.starOf G ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf q)))).rightTerm
            (quotientForestRaw q)

/-- **R-6c-body-252 — the filtered forward map over the value root.**  Body-249's map with the second component from
the value bundle (no `Forward`). -/
noncomputable def fwdMapFilteredValue (F : ResolvedSelectedOuterFilteredMemSupply D)
    (V : ResolvedConcreteSummandValueSupply D) {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom D G) : ForestBlockCodType D G :=
  ⟨⟨(resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf q.1,
      F.mem_of_mem_forestBlockDomFinset q.1 q.2⟩,
    V.quotientForestRaw q.1⟩

/-- **R-6c-body-252 — the value map's outer forest is the raw selected outer** (`rfl`). -/
theorem fwdMapFilteredValue_outer_fst (F : ResolvedSelectedOuterFilteredMemSupply D)
    (V : ResolvedConcreteSummandValueSupply D) {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom D G) :
    (fwdMapFilteredValue F V q).1.1
      = (resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf q.1 :=
  rfl

/-- **R-6c-body-252 — the value map's quotient forest is the value bundle's** (`HEq.rfl`). -/
theorem fwdMapFilteredValue_quotient (F : ResolvedSelectedOuterFilteredMemSupply D)
    (V : ResolvedConcreteSummandValueSupply D) {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom D G) :
    HEq (fwdMapFilteredValue F V q).2 (V.quotientForestRaw q.1) :=
  HEq.rfl

/-- **R-6c-body-252 — the value root from a legacy bundle** (migration-check, defeq field-by-field). -/
def ResolvedConcreteSummandValueSupply.ofLegacy (S : ResolvedConcreteSummandBundleSupply D) :
    ResolvedConcreteSummandValueSupply D where
  Measure := S.Measure
  Survivor := S.Survivor
  Remnant := S.Remnant
  quotientForestRaw := fun {G} q => S.quotientForest q
  hcross := fun {G} q => S.hcross q
  union_eq := fun {G} q => S.union_eq q
  hRdisj := fun {G} q => S.hRdisj q
  quot_eq := fun {G} q => S.quot_eq q

/-- **R-6c-body-252 — the value map agrees with the legacy filtered map** (`rfl`, migration-check).  Lets body-253
port the branch/cover round-trip proofs onto the value root. -/
theorem fwdMapFilteredValue_ofLegacy_eq (F : ResolvedSelectedOuterFilteredMemSupply D)
    (S : ResolvedConcreteSummandBundleSupply D) {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom D G) :
    fwdMapFilteredValue F (ResolvedConcreteSummandValueSupply.ofLegacy S) q = fwdMapFiltered F S q :=
  rfl

end GaugeGeometry.QFT.Combinatorial
