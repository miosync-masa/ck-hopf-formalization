import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocChoiceComponentCases

/-!
# R-6c-body-196 — forest value equality scout: `forest_value_eq` reduced to a forward-forest coherence

Hundred-and-ninety-sixth genuine-body step, a scout of body-194's last backward-choice leaf, `forest_value_eq`,
before proving it.  The audit found it reduces to a **tag pinning** (reusable, body-188 style) plus **one genuinely
fresh forward-forest value coherence** — and proved the reduction.

## The audit — the leaf is genuinely fresh (strictly stronger than body-188)

`forest_value_eq` asks: on a forward image `fwdMap q`, a forest-region component `γ` whose *original* choice was
`q.2 γ = inr B` has recovered choice `recoverChoice (fwdMap q) γ = inr B` — the **same** `B`.  Two facts stand
between:

1. **Tag pinning** — `recoverChoice (fwdMap q) ⟨γ,_⟩ = inr (forestTag_fwd q γ h)`.  `Region.recoverChoice` is an
   *abstract* field here (its only forest fact is `forest_tag : ∃ B'`), so this pinning is not free; it is the
   body-188 pattern (`recoverChoice_forest_eq`) specialised to `z = fwdMap q`.  It reduces the leaf to `forestTag_fwd
   q γ h = B` but says **nothing** about `q`'s original `B`.
2. **Forward-forest value coherence** — `forestTag_fwd q γ h = B` given `q.2 γ = inr B`.  This is the genuinely
   **fresh** fact: the composite `q ↦ fwdMap q ↦ recover` forest round-trip.  No existing lemma provides it —
   body-152's `forestTag` is a general-`z` tag with no `fwdMap`/`q.2` link, body-171's bridge forgets the index
   (`∃ B`), body-188's `recoverChoice_forest_eq` only pins `recover` to *its own* tag (tautological), and the sector
   inverse laws (`forest_left_inv` / `forest_right_inv`) are fixed-`s` component↔index round-trips that never
   compose with the forward step.  It ultimately needs the sector de-contraction (`remnantClass_eq` /
   `remnantGen`, bodies 125/126) and a `Subtype.ext` (`ForestIdx = {A // A ∈ carrier}`).

## The decomposition (reduction PROVED)

`ResolvedForestValueEqDecompositionSupply D S Region` fields the forward forest tag `forestTag_fwd`, the tag pinning
`recoverChoice_forest_pin` (#1), and the fresh coherence `forestTag_forward_eq` (#2).  Then `.forest_value_eq` is
**proved** — `rw` the pinning, then the coherence:

```text
recoverChoice (fwdMap q) ⟨γ,_⟩ = inr (forestTag_fwd q γ h) = inr B
```

`.toChoiceComponentCasesSupply` (given the three sector bridges) produces body-194's supply, so the backward-choice
`HEq` reduces — through bodies 194/193/192 — to the single fresh `forestTag_forward_eq`.

## Consequence

The backward-choice residual is now the one fresh forward-forest coherence `forestTag_forward_eq` (plus the
body-188-style tag pinning, which is reusable machinery).  The next body attacks `forestTag_forward_eq` via the
sector forest round-trip.

Per the HALT: `forestTag_forward_eq`'s body (the sector de-contraction) is not entered; the tag pinning is fielded
(the body-188 pattern); only the reduction is proved.

Landed:

* `ResolvedForestValueEqDecompositionSupply D S Region` — the forward forest tag + the tag pinning + the fresh
  coherence;
* `.forest_value_eq` — body-194's leaf (PROVED from the pinning + the coherence);
* `.toChoiceComponentCasesSupply` — body-194's supply (given the three sector bridges).

Scout / toolkit body (like body-188).  No facade, no flat term, no `forgetHopf`.
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
set_option linter.unusedVariables false

/-- **R-6c-body-196 — the forest value-equality decomposition supply.**  The forward image's forest tag, the tag
pinning (`recoverChoice (fwdMap q) = inr forestTag_fwd`, body-188 pattern), and the fresh forward-forest value
coherence (`forestTag_fwd = B` from the original choice). -/
structure ResolvedForestValueEqDecompositionSupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) (Region : ResolvedRegionChoiceRoundTripSupply D S) where
  /-- The forward image's reconstructed forest tag on a forest-region component. -/
  forestTag_fwd : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ q.1.1.elements}),
    γ.1 ∈ (Region.Union.forestRecovered (fwdMap S q)).elements →
    (D.supply (γ.1.toResolvedFeynmanGraph)).ForestIdx
  /-- Tag pinning (body-188 pattern): the recovered choice on the forward image is `inr forestTag_fwd`. -/
  recoverChoice_forest_pin : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ q.1.1.elements})
    (hu : γ.1 ∈ (Region.Union.unionOuter (fwdMap S q)).1.elements)
    (hmem : γ.1 ∈ (Region.Union.forestRecovered (fwdMap S q)).elements),
    Region.recoverChoice (fwdMap S q) ⟨γ.1, hu⟩ (Finset.mem_attach _ _)
      = Sum.inr (forestTag_fwd q γ hmem)
  /-- The fresh forward-forest value coherence: the reconstructed tag equals the original forest index. -/
  forestTag_forward_eq : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ q.1.1.elements})
    (hmem : γ.1 ∈ (Region.Union.forestRecovered (fwdMap S q)).elements)
    (B : (D.supply (γ.1.toResolvedFeynmanGraph)).ForestIdx),
    q.2 γ (Finset.mem_attach _ _) = Sum.inr B → forestTag_fwd q γ hmem = B

namespace ResolvedForestValueEqDecompositionSupply

variable {S : ResolvedConcreteSummandBundleSupply D} {Region : ResolvedRegionChoiceRoundTripSupply D S}

/-- **R-6c-body-196 — body-194's `forest_value_eq` from the pinning + the coherence.** -/
theorem forest_value_eq (F : ResolvedForestValueEqDecompositionSupply D S Region)
    {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ q.1.1.elements})
    (hu : γ.1 ∈ (Region.Union.unionOuter (fwdMap S q)).1.elements)
    (B : (D.supply (γ.1.toResolvedFeynmanGraph)).ForestIdx)
    (hmem : γ.1 ∈ (Region.Union.forestRecovered (fwdMap S q)).elements)
    (hqB : q.2 γ (Finset.mem_attach _ _) = Sum.inr B) :
    Region.recoverChoice (fwdMap S q) ⟨γ.1, hu⟩ (Finset.mem_attach _ _) = Sum.inr B := by
  rw [F.recoverChoice_forest_pin q γ hu hmem, F.forestTag_forward_eq q γ hmem B hqB]

/-- **R-6c-body-196 — body-194's choice component cases supply from the decomposition** (given the three sector
bridges). -/
def toChoiceComponentCasesSupply (F : ResolvedForestValueEqDecompositionSupply D S Region)
    (Left : ResolvedLeftResidualSectorBridgeSupply D S Region)
    (Right : ResolvedRightRegionSectorBridgeSupply D S Region)
    (Forest : ResolvedForestRegionSectorBridgeSupply D S Region) :
    ResolvedChoiceComponentCasesSupply D S Region where
  Left := Left
  Right := Right
  Forest := Forest
  forest_value_eq := fun {G} q γ hu B hmem hqB => F.forest_value_eq q γ hu B hmem hqB

end ResolvedForestValueEqDecompositionSupply

end GaugeGeometry.QFT.Combinatorial
