import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocParentKeyIdTrace

/-!
# R-6c-body-22 — parentKey = external leg-id multiset (recovery reduced to id-separation)

Twenty-second genuine-body step, concretizing body-20's abstract `parentKey` to the cleanest id-bearing
candidate — the parent's **external leg-id multiset** `H.externalLegs.map (·.legId)` — and reducing
`parentKey_inj` to the pure id-separation statement "the surviving leg-id multiset determines the parent
among `s`'s disjoint forest components".

The bridge is body-21's `contractedSourceGraph_externalLeg_ids`: the contraction keeps the FULL parent
leg-id multiset (all legs retargeted, none dropped), so `parentLegIdKey o.contractedSourceGraph =
γ.externalLegs.map legId`.  Hence contracted-graph equality ⇒ parent leg-id equality (`congrArg` +
body-21), and the only remaining content is `legIds_determine_parent`.

## Caveat (HALT): leg ids alone may be insufficient

A forest component with NO external legs has an empty leg-id multiset; two such components are not separated
by leg ids.  So `legIds_determine_parent` is fielded (not asserted true) — if it turns out leg ids alone do
not separate, the key generalizes to `(leg ids, complement edge ids)` (body-21 also pins
`contractedSourceGraph_internalEdge_ids`) or a full boundary-id signature.  We start with leg ids as the
cleanest candidate, per the plan.

Per the HALT, `legIds_determine_parent` is NOT proved; `parent_graph_inj` is only reduced through this key.

Landed:

* `parentLegIdKey : ResolvedFeynmanGraph → Multiset ResolvedLegId` — the concrete key;
* `contractedSource_parentLegIdKey` — the key of the contracted graph = the parent leg-id multiset (body-21);
* `ResolvedParentLegIdSeparationSupply D G s` — `legIds_determine_parent`;
* `.toParentKeyRecoverySupply` — body-20's key supply at `parentLegIdKey` (⟹ body-19/`parent_graph_inj`).

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-body-22 — the concrete parent key: a graph's external leg-id multiset.** -/
def parentLegIdKey (H : ResolvedFeynmanGraph) : Multiset ResolvedLegId :=
  H.externalLegs.map (·.legId)

variable {s : ResolvedCoassocSplitChoice D G}

/-- **R-6c-body-22 — the leg-id key of the contracted source graph is the parent's leg-id multiset** (body-21:
all legs survive the contraction). -/
theorem contractedSource_parentLegIdKey (o : s.ForestChoiceOccurrence) :
    parentLegIdKey o.contractedSourceGraph =
      o.γ.1.toResolvedFeynmanGraph.externalLegs.map (·.legId) :=
  o.contractedSourceGraph_externalLeg_ids

/-- **R-6c-body-22 — the parent leg-id separation supply.**  The genuine remaining content: the surviving
leg-id multiset determines the parent among `s`'s disjoint forest components. -/
structure ResolvedParentLegIdSeparationSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph) (s : ResolvedCoassocSplitChoice D G) where
  /-- Equal parent leg-id multisets force equal parent intrinsic graphs. -/
  legIds_determine_parent : ∀ o₁ o₂ : s.ForestChoiceOccurrence,
    o₁.γ.1.toResolvedFeynmanGraph.externalLegs.map (·.legId) =
        o₂.γ.1.toResolvedFeynmanGraph.externalLegs.map (·.legId) →
      o₁.γ.1.toResolvedFeynmanGraph = o₂.γ.1.toResolvedFeynmanGraph

/-- **R-6c-body-22 — body-20's key-recovery supply at the concrete leg-id key.**  Composing with body-20's
`.toParentGraphInjectivitySupply` (and body-19's `.toOccurrenceParentInjectivitySupply`) discharges
`parent_graph_inj` / `parent_inj` down to `legIds_determine_parent`. -/
def ResolvedParentLegIdSeparationSupply.toParentKeyRecoverySupply
    (S : ResolvedParentLegIdSeparationSupply D G s) :
    ResolvedParentKeyRecoverySupply D G s (Multiset ResolvedLegId) where
  parentKey := parentLegIdKey
  parentKey_inj := fun o₁ o₂ h =>
    S.legIds_determine_parent o₁ o₂ (by
      rw [← contractedSource_parentLegIdKey o₁, ← contractedSource_parentLegIdKey o₂]
      exact h)

end GaugeGeometry.QFT.Combinatorial
