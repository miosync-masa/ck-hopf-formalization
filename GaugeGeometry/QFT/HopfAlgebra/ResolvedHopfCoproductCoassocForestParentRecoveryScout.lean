import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestChoiceOccurrenceRecovery
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestRegionSectorBridge

/-!
# R-6c-body-202 — forest parent recovery: `parent_recovered` collapses to `rfl` via the body-171 bridge

Two-hundred-and-second genuine-body step, a scout that turned into a collapse.  Body-200's last backward-choice
leaf `parent_recovered : occ.γ = γ` is **not** a genuine new fact: defining the recovered occurrence directly from
the body-171 forest bridge's membership witness makes its parent *definitionally* `γ`, so `parent_recovered := rfl`.
The genuine content relocates one level down, into body-171's `forestRecovered_forward_membership`.

## The collapse (scout finding)

The forest-region membership hypothesis already carries the occurrence.  Body-171's bridge gives

```text
γ ∈ forestRecovered (fwdMap q)  ↔  forestChoiceSelected q γ = ∃ hγ, ∃ B, choiceAt q ⟨γ, hγ⟩ = inr B
```

so from `h : γ.1 ∈ forestRecovered (fwdMap q)` the forward direction yields `⟨hγ, B, hchoice⟩`.  Building the
occurrence `⟨⟨γ.1, hγ⟩, B, hchoice⟩` gives parent `⟨γ.1, hγ⟩`, which is `γ` by subtype proof-irrelevance (the
membership proof is a `Prop`).  So `(occurrence q γ h).γ = γ` is `rfl`.  This is sound because the only consumer
(`forest_choiceAt_eq` / `heq_transport_choice`, body-200) needs merely *some* occurrence at `γ` carrying an
`hchoice`; it never inspects which remnant produced it.

Nothing else works: `ResolvedOccurrenceParentInjectivitySupply.parent_inj` (body-…) and body-126's `remnantInj`
are "same contracted graph ⇒ same parent" facts at the *forward / sector* altitude, and the sector `forest_left_inv`
lives at the sector-graph level, disconnected from the region-`G` `componentToForest`.  None of them is the backward
recovery identity, and none composes cleanly.  The `rfl`-collapse via body-171 is the honest route.

## The construction (PROVED)

`ResolvedForestParentRecoverySupply D S Region` fields only the body-171 forest bridge `Forest`.  `occurrence` is
built from `Forest.forestRecovered_forward_membership`, and `parent_recovered` is `rfl`.
`.toForestChoiceOccurrenceRecoverySupply` produces body-200's supply — so the whole backward-choice round-trip
(through bodies 202 → 200 → 198 → 196 → 194 → 193 → 164) stands on the **already-fielded** body-171 forest bridge,
with no new leaf.

## Consequence — backward-choice bottoms out at body-171

`parent_recovered` is retired (`rfl`).  The real remaining backward-choice geometry is body-171's
`forestRecovered_forward_membership` — the sector remnant round-trip (`componentToForest (fwdMap q)` correspondence),
one of the three sector bridges (bodies 170/171/172) that the backward *outer* partition already rests on.  So the
backward-choice and backward-outer sides now share the same floor: the three sector bridges.

Per the HALT: body-171's `forestRecovered_forward_membership` body (the sector round-trip) is not entered; the
occurrence is built from its membership witness; `parent_recovered` is `rfl`; `forward_quotient_heq` is untouched.

Landed:

* `ResolvedForestParentRecoverySupply D S Region` — the body-171 forest bridge;
* `.occurrence` — the recovered occurrence from the bridge membership witness;
* `.parent_recovered` — body-200's leaf (`rfl`);
* `.toForestChoiceOccurrenceRecoverySupply` — body-200's supply (backward-choice on the body-171 bridge).

Toolkit body (like body-181).  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-202 — the forest parent recovery supply.**  Only the body-171 forest region sector bridge — from
its membership witness the recovered occurrence is built with parent `γ` definitionally. -/
structure ResolvedForestParentRecoverySupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) (Region : ResolvedRegionChoiceRoundTripSupply D S) where
  /-- Body-171: the forest region sector bridge (`forestRecovered (fwdMap q) ↔ forestChoiceSelected q`). -/
  Forest : ResolvedForestRegionSectorBridgeSupply D S Region

namespace ResolvedForestParentRecoverySupply

variable {S : ResolvedConcreteSummandBundleSupply D} {Region : ResolvedRegionChoiceRoundTripSupply D S}

/-- **R-6c-body-202 — the recovered occurrence** from the body-171 bridge membership witness (parent `⟨γ.1, hγ⟩`). -/
noncomputable def occurrence (F : ResolvedForestParentRecoverySupply D S Region)
    {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ q.1.1.elements})
    (h : γ.1 ∈ (Region.Union.forestRecovered (fwdMap S q)).elements) :
    ResolvedCoassocSplitChoice.ForestChoiceOccurrence q :=
  let hsel := (F.Forest.forestRecovered_forward_membership q γ.1).mp h
  ⟨⟨γ.1, hsel.choose⟩, hsel.choose_spec.choose, hsel.choose_spec.choose_spec⟩

/-- **R-6c-body-202 — body-200's `parent_recovered`** (`rfl` by subtype proof-irrelevance). -/
theorem parent_recovered (F : ResolvedForestParentRecoverySupply D S Region)
    {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ q.1.1.elements})
    (h : γ.1 ∈ (Region.Union.forestRecovered (fwdMap S q)).elements) :
    (F.occurrence q γ h).γ = γ :=
  rfl

/-- **R-6c-body-202 — body-200's forest choice occurrence recovery supply.** -/
noncomputable def toForestChoiceOccurrenceRecoverySupply
    (F : ResolvedForestParentRecoverySupply D S Region) :
    ResolvedForestChoiceOccurrenceRecoverySupply D S Region where
  occurrence := fun {G} q γ h => F.occurrence q γ h
  parent_recovered := fun {G} q γ h => F.parent_recovered q γ h

end ResolvedForestParentRecoverySupply

end GaugeGeometry.QFT.Combinatorial
