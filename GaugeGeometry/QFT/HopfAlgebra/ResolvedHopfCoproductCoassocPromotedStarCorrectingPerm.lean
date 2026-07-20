import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocResolvedStarRenamePerm
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocTouchedOccurrenceConcrete
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCrossAmbientStarAudit

/-!
# R-6c-body-455 — the forward-owned promoted star correcting permutation (PROVED)

Four-hundred-and-fifty-fifth genuine-body step — the FORWARD comparator, defined from `q, o` ALONE (no recovered
`z, δ`, no inner correction).  It mirrors the inner side (body-450) for the promoted socket: both star maps already live
on the SAME `o.B.1.elements`, so the correcting permutation `ρ q o` is a body-449 `resolvedStarRenamePerm` between the
hardcoded parent star `D.starOf o.γ.1.tRFG o.B.1` and the promoted outer star
`D.starOf G (selectedOuterRawOf q.1) (o.γ.1.promote ·)`.  `ρ q o` fixes only the PARENT ambient `o.γ.1`'s vertices.

* `promotedOccurrenceStar` — the promoted star (outer star of the promoted component in `G`);
* `promotedOccurrenceStar_fresh` — it avoids `o.γ.1`'s vertices (fresh w.r.t. `G ⊇ o.γ.1.vertices`, via the canonical
  `Fstar` on the forward-selected outer, membership from body-385 `promote_mem_selectedOuterRawOf`);
* `promotedOccurrenceStar_injOn` — injective on `o.B.1.elements` (`Fstar.starOf_injective` on the selected outer +
  `promote_injective`);
* `hardcodedOccurrenceStar_injOn` — the parent star is injective (`Fstar.starOf_injective` on the parent ambient);
* `promotedStarCorrectingPerm q o` — `ρ` via the body-449 engine, orientation `ρ (hardcodedStar b) = promotedStar b`;
* `promotedStarCorrectingPerm_on_parent_vertices` / `_on_occurrence_stars` — the two point laws (fixing domain =
  `o.γ.1.vertices` only);
* `canonicalPromotedStarCorrectingPermSupply` — the canonical inhabitant of the body-446 prototype.

Per the HALT/guards: strict `promoted_star_agrees` is NOT used; recovered `z, δ` / inner correction are NOT used; the
fixing domain is the parent ambient only (NOT global `G`); promoted-component membership is the EXPLICIT body-385
consumption (not guessed); `Concrete` / `VBuild` NOT wired; no permutation equality is claimed; body-445 stays a valid
conditional.  NOT the unconditional theorem.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO
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
set_option maxHeartbeats 1600000

variable {D : ResolvedCoproductProperForestData} (Fstar : ResolvedCanonicalStarFacts D)
  {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
  (o : ResolvedCoassocSplitChoice.ForestChoiceOccurrence q.1)

/-- **R-6c-body-455 — the hardcoded parent star of the occurrence.** -/
noncomputable def hardcodedOccurrenceStar :
    ResolvedFeynmanSubgraph o.γ.1.toResolvedFeynmanGraph → VertexId :=
  D.starOf o.γ.1.toResolvedFeynmanGraph o.B.1

/-- **R-6c-body-455 — the promoted outer star of the occurrence.**  The outer star of the promoted component
`o.γ.1.promote b` in the forward-selected outer of `q`. -/
noncomputable def promotedOccurrenceStar :
    ResolvedFeynmanSubgraph o.γ.1.toResolvedFeynmanGraph → VertexId :=
  fun b => D.starOf G ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf q.1)
    (o.γ.1.promote b)

include Fstar

/-- **R-6c-body-455 — the promoted star avoids the parent's vertices.** -/
theorem promotedOccurrenceStar_fresh {b : ResolvedFeynmanSubgraph o.γ.1.toResolvedFeynmanGraph}
    (hb : b ∈ o.B.1.elements) :
    promotedOccurrenceStar q o b ∉ o.γ.1.toResolvedFeynmanGraph.vertices :=
  fun hmem => Fstar.starOf_fresh G ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf q.1)
    (o.γ.1.promote b) (promote_mem_selectedOuterRawOf q o hb) (o.γ.1.vertices_subset hmem)

/-- **R-6c-body-455 — the promoted star is injective on the occurrence forest.** -/
theorem promotedOccurrenceStar_injOn :
    ∀ b₁ ∈ o.B.1.elements, ∀ b₂ ∈ o.B.1.elements,
      promotedOccurrenceStar q o b₁ = promotedOccurrenceStar q o b₂ → b₁ = b₂ := by
  intro b₁ hb₁ b₂ hb₂ heq
  exact o.γ.1.promote_injective
    (Fstar.starOf_injective G ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf q.1)
      (promote_mem_selectedOuterRawOf q o hb₁) (promote_mem_selectedOuterRawOf q o hb₂) heq)

/-- **R-6c-body-455 — the hardcoded parent star is injective on the occurrence forest.** -/
theorem hardcodedOccurrenceStar_injOn :
    ∀ b₁ ∈ o.B.1.elements, ∀ b₂ ∈ o.B.1.elements,
      hardcodedOccurrenceStar q o b₁ = hardcodedOccurrenceStar q o b₂ → b₁ = b₂ :=
  fun _ h₁ _ h₂ heq =>
    Fstar.starOf_injective o.γ.1.toResolvedFeynmanGraph o.B.1 h₁ h₂ heq

/-- **R-6c-body-455 ∎ — the forward-owned promoted star correcting permutation.**  Orientation
`ρ (hardcodedStar b) = promotedStar b`; fixing domain = the parent ambient `o.γ.1`'s vertices only. -/
noncomputable def promotedStarCorrectingPerm : Equiv.Perm VertexId :=
  resolvedStarRenamePerm o.B.1 (hardcodedOccurrenceStar q o) (promotedOccurrenceStar q o)
    (hardcodedOccurrenceStar_injOn Fstar q o) (promotedOccurrenceStar_injOn Fstar q o)

/-- **R-6c-body-455 — `ρ` fixes the parent ambient's vertices** (LOCAL, never a global `G` survivor). -/
theorem promotedStarCorrectingPerm_on_parent_vertices {v : VertexId}
    (hvH : v ∈ o.γ.1.toResolvedFeynmanGraph.vertices) :
    promotedStarCorrectingPerm Fstar q o v = v :=
  resolvedStarRenamePerm_on_ambient _ _ _ _ _
    (fun γ hγ => Fstar.starOf_fresh o.γ.1.toResolvedFeynmanGraph o.B.1 γ hγ)
    (fun _ hb => promotedOccurrenceStar_fresh Fstar q o hb) hvH

/-- **R-6c-body-455 — `ρ` sends each hardcoded star to the promoted star.** -/
theorem promotedStarCorrectingPerm_on_occurrence_stars
    {b : ResolvedFeynmanSubgraph o.γ.1.toResolvedFeynmanGraph} (hb : b ∈ o.B.1.elements) :
    promotedStarCorrectingPerm Fstar q o (hardcodedOccurrenceStar q o b) = promotedOccurrenceStar q o b :=
  resolvedStarRenamePerm_on_stars _ _ _ _ _ hb

/-- **R-6c-body-455 ∎ — the canonical inhabitant of the body-446 promoted-correcting-perm prototype.** -/
noncomputable def canonicalPromotedStarCorrectingPermSupply
    (Fmem : ResolvedSelectedOuterFilteredMemSupply D) (V : ResolvedConcreteSummandValueSupply D) :
    ResolvedPromotedStarCorrectingPermSupply Fmem V where
  ρ := fun q o => promotedStarCorrectingPerm Fstar q o
  promoted_star_agrees_upto := fun q o b hb =>
    (promotedStarCorrectingPerm_on_occurrence_stars Fstar q o hb).symm

end GaugeGeometry.QFT.Combinatorial
