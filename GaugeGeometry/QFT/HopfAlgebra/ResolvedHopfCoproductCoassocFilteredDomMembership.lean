import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecoveredChoiceMembership
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestBlockBijection

/-!
# R-6c-body-256 — canonical filtered-domain membership: `witnessSplit_mem` from the tags (total-root-free, PROVED)

Two-hundred-and-fifty-sixth genuine-body step — the canonical, total-root-free inhabitant of the filtered-domain
membership.  Body-253's value cover has `witnessSplit_mem` and its branch data has `forestPreimage_mem` /
`mixedPreimage_mem` as obligations; body-253 already assembles the cover's field from those by `dite`.  This body
supplies the **tag-level discharge**: `q ∈ forestBlockDomFinset G` follows from the reconstruction tags
(`isForestCarryingChoice`, or `≠ p_R ∧ ≠ p_L`) alone — never from `selectedOuter_mem` / `Forward`.

## The reduction (`Finset.mem_sigma` + `mem_attach`)

`forestBlockDomFinset G = (D.carrier G).attach.sigma (fun A => forestChoiceCarrier A)`
(`ForestBlockBijection.lean:84`), so membership reduces to the *fiber*: `q ∈ forestBlockDomFinset G ⟺ q.2 ∈
forestChoiceCarrier q.1` (the base `q.1 ∈ (D.carrier G).attach` is free by `mem_attach`).  The outer forest's carrier
tag is the sigma's first component — no selected-outer membership is needed.

## The three canonical membership tools

```lean
mem_forestBlockDomFinset_of_choice           (hc : q.2 ∈ forestChoiceCarrier q.1) : q ∈ forestBlockDomFinset G
mem_forestBlockDomFinset_of_isForestCarrying (h  : isForestCarryingChoice q.1 q.2) : q ∈ forestBlockDomFinset G  -- forest branch
mem_forestBlockDomFinset_of_ne (hR : q.2 ≠ p_R) (hL : q.2 ≠ p_L)                    : q ∈ forestBlockDomFinset G  -- mixed branch
```

The forest tool composes the reduction with `mem_forestChoiceCarrier_of_isForestCarrying`
(`RecoveredChoiceMembership.lean:103`); the mixed tool with `choice_mem_piCarrier` (`:72`, unconditional) +
`mem_forestChoiceCarrier_of_ne` (`:94`).  These discharge body-253's `forestPreimage_mem` / `mixedPreimage_mem`
obligations from the reconstruction tags (`ResolvedRecoveredChoiceMembershipSupply.forest_tag` / `mixed_ne_pR` /
`mixed_ne_pL`), completing the membership side of the migration without the retired total root.

Per the HALT: only the membership tools are proved (total-root-free); no branch geometry, no forward/backward
round-trip, no `selectedOuter_mem` / `Forward`.  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-256 — filtered-domain membership from the choice fiber.**  `q ∈ forestBlockDomFinset G` reduces to
`q.2 ∈ forestChoiceCarrier q.1` (`Finset.mem_sigma` + `mem_attach`); the outer carrier tag is the sigma base, free. -/
theorem mem_forestBlockDomFinset_of_choice (q : ForestBlockDomType D G)
    (hc : q.2 ∈ forestChoiceCarrier q.1) : q ∈ forestBlockDomFinset G := by
  rw [forestBlockDomFinset, Finset.mem_sigma]
  exact ⟨Finset.mem_attach _ _, hc⟩

/-- **R-6c-body-256 — filtered-domain membership on the forest branch** (from `isForestCarryingChoice`). -/
theorem mem_forestBlockDomFinset_of_isForestCarrying (q : ForestBlockDomType D G)
    (h : isForestCarryingChoice q.1 q.2) : q ∈ forestBlockDomFinset G :=
  mem_forestBlockDomFinset_of_choice q (mem_forestChoiceCarrier_of_isForestCarrying h)

/-- **R-6c-body-256 — filtered-domain membership on the mixed branch** (from `≠ p_R` and `≠ p_L`). -/
theorem mem_forestBlockDomFinset_of_ne (q : ForestBlockDomType D G)
    (hR : q.2 ≠ (fun _ _ => Sum.inl false)) (hL : q.2 ≠ (fun _ _ => Sum.inl true)) :
    q ∈ forestBlockDomFinset G :=
  mem_forestBlockDomFinset_of_choice q
    (mem_forestChoiceCarrier_of_ne (choice_mem_piCarrier q.1 q.2) hR hL)

end GaugeGeometry.QFT.Combinatorial
