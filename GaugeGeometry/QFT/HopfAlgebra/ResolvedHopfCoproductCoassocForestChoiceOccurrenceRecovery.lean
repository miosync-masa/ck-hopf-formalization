import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestTagForwardScout

/-!
# R-6c-body-200 — forest choice occurrence recovery: `forest_choiceAt_eq` from an occurrence + parent recovery

Two-hundredth genuine-body step — a milestone.  The backward-choice round-trip's single fresh leaf
`forest_choiceAt_eq` (body-198/199) is **proved** from a recovered forest-choice occurrence and one fielded parent
recovery, so backward-choice falls to the genuine geometry leaf `parent_recovered` (the forward round-trip parent
identity) alone.

## The occurrence recovery

A forest-region component `γ` of `q` on the forward image `fwdMap q` is, by the sector round-trip, the parent of a
recovered forest-choice occurrence `occ : q.ForestChoiceOccurrence` — carrying `occ.γ` (the parent), `occ.B` (the
chosen sub-forest), and, crucially, `occ.hchoice : choiceAt q occ.γ = inr occ.B` **for free** (the occurrence bundles
its own choice witness).  With the one fielded parent recovery `parent_recovered : occ.γ = γ`, the reconstructed
forest tag is `forestTag_fwd := parent_recovered ▸ occ.B`, and `forest_choiceAt_eq` follows.

## The transport helper (PROVED)

`heq_transport_choice` is the dependent transport: an occurrence whose parent equals `γ` gives `choiceAt γ = inr
(transported B)`.  Proof: `cases` the parent equality (aligning the `ForestIdx` codomain, which depends on the
parent subgraph), then `occ.hchoice`.  This is the clean `subst` handling of the `ForestIdx`-over-parent dependency
— no `HEq`, no `cast` gymnastics.

## The recovery supply (PROVED)

`ResolvedForestChoiceOccurrenceRecoverySupply D S Region` fields the recovered occurrence `occurrence` and the single
fresh `parent_recovered`.  `forestTag_fwd` is the transported `occ.B`, and `.forest_choiceAt_eq` is **proved** by
`heq_transport_choice`.  `.toForestTagForwardDecompositionSupply` produces body-198's supply — so the whole
backward-choice round-trip (through bodies 200 → 198 → 196 → 194 → 193 → 164) is supplied by `occurrence` +
`parent_recovered`.

## Consequence — backward-choice down to the forest parent recovery

The backward-choice residual is now exactly the forward round-trip **parent recovery** `parent_recovered : occ.γ =
γ` (a homogeneous `Eq` of outer components) plus the occurrence construction — genuine `Feynman`-graph geometry, no
longer an `HEq` or a choice-value abstraction.  Everything else on the backward-choice side is proved.
`forward_quotient_heq` (the dual, heavier) is untouched.

Per the HALT: `parent_recovered`'s body (the sector round-trip / occurrence injectivity) is not entered; the
occurrence and its `hchoice` are wired; only the transport reduction is proved.

Landed:

* `heq_transport_choice` — the dependent `ForestIdx` transport (PROVED);
* `ResolvedForestChoiceOccurrenceRecoverySupply D S Region` — the recovered occurrence + `parent_recovered`;
* `.forestTag_fwd` — the transported occurrence forest index;
* `.forest_choiceAt_eq` — body-198's single fresh leaf (PROVED);
* `.toForestTagForwardDecompositionSupply` — body-198's supply (backward-choice down to `parent_recovered`).

Milestone body (like body-100/150).  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-200 — the dependent `ForestIdx` transport.**  An occurrence whose parent equals `γ` gives `choiceAt
γ = inr (transported B)`; `cases` the parent equality (aligning the parent-dependent `ForestIdx` codomain), then the
occurrence's own choice witness. -/
theorem heq_transport_choice {G : ResolvedFeynmanGraph} {s : ResolvedCoassocSplitChoice D G}
    (o : ResolvedCoassocSplitChoice.ForestChoiceOccurrence s)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ s.1.1.elements})
    (hp : o.γ = γ) :
    ResolvedCoassocSplitChoice.choiceAt s γ = Sum.inr (hp ▸ o.B) := by
  cases hp
  exact o.hchoice

/-- **R-6c-body-200 — the forest choice occurrence recovery supply.**  The recovered forest-choice occurrence of a
forest-region component and the single fresh parent recovery. -/
structure ResolvedForestChoiceOccurrenceRecoverySupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) (Region : ResolvedRegionChoiceRoundTripSupply D S) where
  /-- The forest-choice occurrence recovered from a forest-region component of the forward image. -/
  occurrence : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ q.1.1.elements}),
    γ.1 ∈ (Region.Union.forestRecovered (fwdMap S q)).elements →
    ResolvedCoassocSplitChoice.ForestChoiceOccurrence q
  /-- **The single fresh leaf**: the recovered occurrence's parent is `γ` (the forward round-trip parent recovery). -/
  parent_recovered : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ q.1.1.elements})
    (h : γ.1 ∈ (Region.Union.forestRecovered (fwdMap S q)).elements),
    (occurrence q γ h).γ = γ

namespace ResolvedForestChoiceOccurrenceRecoverySupply

variable {S : ResolvedConcreteSummandBundleSupply D} {Region : ResolvedRegionChoiceRoundTripSupply D S}

/-- **R-6c-body-200 — the reconstructed forest tag** (the recovered occurrence's `B`, transported to `γ`). -/
def forestTag_fwd (F : ResolvedForestChoiceOccurrenceRecoverySupply D S Region)
    {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ q.1.1.elements})
    (h : γ.1 ∈ (Region.Union.forestRecovered (fwdMap S q)).elements) :
    (D.supply (γ.1.toResolvedFeynmanGraph)).ForestIdx :=
  (F.parent_recovered q γ h) ▸ (F.occurrence q γ h).B

/-- **R-6c-body-200 — body-198's `forest_choiceAt_eq` from the occurrence + parent recovery.** -/
theorem forest_choiceAt_eq (F : ResolvedForestChoiceOccurrenceRecoverySupply D S Region)
    {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ q.1.1.elements})
    (hmem : γ.1 ∈ (Region.Union.forestRecovered (fwdMap S q)).elements) :
    q.2 γ (Finset.mem_attach _ _) = Sum.inr (F.forestTag_fwd q γ hmem) :=
  heq_transport_choice (F.occurrence q γ hmem) γ (F.parent_recovered q γ hmem)

/-- **R-6c-body-200 — body-198's forest tag forward decomposition supply.** -/
def toForestTagForwardDecompositionSupply
    (F : ResolvedForestChoiceOccurrenceRecoverySupply D S Region) :
    ResolvedForestTagForwardDecompositionSupply D S Region where
  forestTag_fwd := fun {G} q γ hmem => F.forestTag_fwd q γ hmem
  forest_choiceAt_eq := fun {G} q γ hmem => F.forest_choiceAt_eq q γ hmem

end ResolvedForestChoiceOccurrenceRecoverySupply

end GaugeGeometry.QFT.Combinatorial
