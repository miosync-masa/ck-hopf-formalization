import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCorrectedRemnantProvider

/-!
# R-6c-body-462 — the corrected family totality feasibility + V-ownership audit (PROVED / AUDIT)

Four-hundred-and-sixty-second genuine-body step — NOT an implementation migration: a totality-feasibility lemma plus the
family-ownership verdict.  The conclusion:

> The filtered corrected provider (body-461) can be generalized to a total `∀ s` family WITHOUT new geometry; the
> remaining obstacle is not totality but family-level quotient ownership.

## Totality feasibility (PROVED)

The load-bearing membership of bodies 455–461 — `promote_mem_selectedOuterRawOf` (body-385) — reads only `q.1` (the
split choice), never `q.2 : q.1 ∈ forestBlockDomFinset` (filteredness is carried by the TYPE only).  So it generalizes
verbatim to a raw `s : ResolvedCoassocSplitChoice D G`:

* `promote_mem_selectedOuterRawOf_raw` — the raw-domain feasibility lemma (proof identical to body-385 with `q.1 ↦ s`).

This certifies that 455–461 need no hybrid `if s ∈ forestBlockDomFinset` — they generalize to all `s` directly (the
hybrid would only pollute defeq / wiring).

## V-field verdict table

| Field           | verdict                                                                                       |
|-----------------|-----------------------------------------------------------------------------------------------|
| `remnantCD`     | DERIVED — uncorrected contraction CD + `mapPerm_isConnectedDivergent_iff`                      |
| `remnantGen`    | DERIVED — corrected source has class equality with the uncorrected source                     |
| `remnantDisjoint`| GEOMETRY — per-occurrence `ρ` differs, NOT free from `mapPerm` invariance; needs the common promoted-star representation |
| `remnantInj`    | DERIVED — from disjoint + component nonempty/CD                                                |
| `hcross`        | GEOMETRY — right survivor vs corrected remnant, separated inside the common quotient ambient   |
| `hRdisj`        | DERIVED — from cross + equality exclusion                                                       |
| `quotient_mem`  | V OWNERSHIP — decomposes to a W' membership iff (separate audit)                                |
| `quot_eq`       | V OWNERSHIP — must NOT treat distinct `ρ`'s as one global permutation                           |
| `survivorInj/Gen`| unchanged                                                                                     |

## Strict-socket usage map

* `InnerStarRaw` — the `hround` consumer is REPLACED by body-461 (`canonicalCorrectedRemnantComponent_roundtrip`).
* `StarProm` — STILL in the parent-reconstruction chain: body-385 touched theorem, body-387 internal-edge retarget
  bridge, body-388 external legs, body-389 vertices, body-390 assembly.  For a corrected component, `δ`'s source is
  already a promoted-star contraction, so the next front rewrites body-385 to the corrected source (touched collection
  without strict `StarProm`) and reuses the body-459 retarget agreement for the parent projections.

## Prototype interface (un-consumed)

* `ResolvedAlphaNativeCorrectedFamilySupply` — the total corrected family plus the one genuinely-new field
  (`remnantDisjoint`, GEOMETRY).  The DERIVED fields are absent (derivable); the V-OWNERSHIP fields are a separate audit.

Per the HALT/guards: family disjointness, quotient ownership, and the body-445 migration are NOT implemented here; the
two strict sockets are NOT yet recorded as removed from the final signature.  NO permutation equality; body-445 stays a
valid conditional.  NOT the unconditional theorem.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO
`promote_collapse` / singleton / floor-297.
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

/-- **R-6c-body-462 — the raw-domain totality feasibility.**  Body-385's promoted-membership generalizes verbatim from a
filtered `q` to a raw split choice `s` (the proof never reads `q.2`).  Certifies 455–461 need no hybrid. -/
theorem promote_mem_selectedOuterRawOf_raw (s : ResolvedCoassocSplitChoice D G)
    (o : s.ForestChoiceOccurrence) {b : ResolvedFeynmanSubgraph o.γ.1.toResolvedFeynmanGraph}
    (hb : b ∈ o.B.1.elements) :
    o.γ.1.promote b ∈ ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).elements := by
  classical
  have hmem : o.γ.1.promote b ∈ ((resolvedPromotedOfSupply D G).promotedOf s).elements := by
    rw [ResolvedPromotedOfSupply.promotedOf_elements]
    unfold ResolvedCoassocSplitChoice.promotedElements
    refine Finset.mem_biUnion.mpr ⟨o.γ, Finset.mem_attach _ _, ?_⟩
    rw [ResolvedCoassocSplitChoice.promotedComponentElements_inr s o.hchoice]
    simp only [ResolvedAdmissibleSubgraph.promote_elements, Finset.mem_image]
    exact ⟨b, hb, rfl⟩
  simp only [ResolvedForestPromoteSupply.selectedOuterRawOf,
    ResolvedAdmissibleSubgraph.union_elements, Finset.mem_union]
  exact Or.inr hmem

/-- **R-6c-body-462 — prototype: the alpha-native corrected remnant family interface** (un-consumed).  The total corrected
family (feasible by `promote_mem_selectedOuterRawOf_raw`), plus the ONE genuinely-new field `remnantDisjoint` (GEOMETRY,
NOT free from `mapPerm` invariance).  The DERIVED fields (`remnantCD`/`remnantGen`/`remnantInj`/`hRdisj`) are absent, and
the V-OWNERSHIP fields (`quotient_mem`/`quot_eq`) are a separate audit — see the module verdict table. -/
structure ResolvedAlphaNativeCorrectedFamilySupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph) where
  /-- A corrected remnant provider for EVERY raw split choice (totality). -/
  family : ∀ s : ResolvedCoassocSplitChoice D G, ResolvedCorrectedRemnantReembedSupply D G s
  /-- GEOMETRY: the corrected remnant components are pairwise disjoint in the quotient graph. -/
  remnantDisjoint : ∀ (s : ResolvedCoassocSplitChoice D G)
    (o o' : s.ForestChoiceOccurrence), o ≠ o' →
    ((family s).correctedRemnantComponent o).Disjoint ((family s).correctedRemnantComponent o')

end GaugeGeometry.QFT.Combinatorial
