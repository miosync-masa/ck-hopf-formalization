import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaUnconditionalizationFrontier
import GaugeGeometry.QFT.HopfAlgebra.ResolvedSubgraphPromote
import GaugeGeometry.QFT.HopfAlgebra.ResolvedAdmissibleSubgraphOfElements

/-!
# R-6c-body-534 (Step 1) — generic external-leg saturation algebra (PROVED)

Five-hundred-and-thirty-fourth genuine-body step (Step 1) — the carrier-INDEPENDENT saturation algebra that every `W″`
closure audit (selectedOuter / recovered union / corrected quotient) reuses.  Two closure operations preserve
`ResolvedExternalLegSaturated`, multiplicity-safe:

* `resolvedForestExternalLegSaturated_union` — a `union` of two forest-saturated forests is forest-saturated
  (`union_elements` membership dispatch);
* `resolvedExternalLegSaturated_promote_of_nested` — a nested promote `γ.promote δ` is saturated when `γ` is saturated in
  the ambient AND `δ` is saturated in `γ`; the crux is the multiplicity-preserving nested filter
  `G.legs.filter (∈ δ) ≤ γ.legs.filter (∈ δ) ≤ δ.legs` (`count`-safe via `Multiset.le_iff_count` + `count_filter`, NO
  membership-only shortcut);
* `resolvedForestExternalLegSaturated_promote_of_nested` — the forest version (`promote_elements` image + the component
  lemma).

These land selectedOuter's saturation (body-534 Step 2, next): `leftOf` reuses the input-outer saturation directly,
`promotedOf` feeds the parent + chosen-inner saturation through the nested promote, and `union` closes it.

Per the HALT/guards: everything is multiplicity-safe (no membership-only proof); nothing is derived from a target
membership; no "`W′` forests all saturated" claim; `selectedOuter` / recovered union / corrected quotient membership are
NOT entered here (Step 2+); the final coassoc theorem is NOT re-keyed; `Parent`-CD is NOT touched; strict `StarProm` /
`InnerStarRaw` stay ZERO; NO unconditional-coassoc claim.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO
`promote_collapse` / singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

variable {G : ResolvedFeynmanGraph}

/-- **R-6c-body-534 ∎ — saturation is closed under `union`.** -/
theorem resolvedForestExternalLegSaturated_union {H : ResolvedFeynmanGraph}
    (A B : ResolvedAdmissibleSubgraph H)
    (hCross : ∀ γ ∈ A.elements, ∀ δ ∈ B.elements, γ ≠ δ → γ.Disjoint δ)
    (hA : ResolvedForestExternalLegSaturated A) (hB : ResolvedForestExternalLegSaturated B) :
    ResolvedForestExternalLegSaturated (A.union B hCross) := by
  intro δ hδ
  simp only [ResolvedAdmissibleSubgraph.union_elements, Finset.mem_union] at hδ
  rcases hδ with h | h
  · exact hA δ h
  · exact hB δ h

/-- **R-6c-body-534 ∎ — saturation is closed under a nested promote** (multiplicity-safe). -/
theorem resolvedExternalLegSaturated_promote_of_nested (γ : ResolvedFeynmanSubgraph G)
    {δ : ResolvedFeynmanSubgraph γ.toResolvedFeynmanGraph}
    (hγ : ResolvedExternalLegSaturated G γ)
    (hδ : ResolvedExternalLegSaturated γ.toResolvedFeynmanGraph δ) :
    ResolvedExternalLegSaturated G (γ.promote δ) := by
  unfold ResolvedExternalLegSaturated at hγ hδ ⊢
  rw [ResolvedFeynmanSubgraph.promote_vertices, ResolvedFeynmanSubgraph.promote_externalLegs]
  refine le_trans ?_ hδ
  rw [Multiset.le_iff_count]
  intro ℓ
  simp only [Multiset.count_filter]
  by_cases hℓδ : ℓ.attachedTo ∈ δ.vertices
  · rw [if_pos hℓδ, if_pos hℓδ]
    have hc := Multiset.count_le_of_le ℓ hγ
    rw [Multiset.count_filter, if_pos (show ℓ.attachedTo ∈ γ.vertices from δ.vertices_subset hℓδ)] at hc
    exact hc
  · rw [if_neg hℓδ]; exact Nat.zero_le _

/-- **R-6c-body-534 ∎ — the forest version of the nested-promote closure.** -/
theorem resolvedForestExternalLegSaturated_promote_of_nested (γ : ResolvedFeynmanSubgraph G)
    (B : ResolvedAdmissibleSubgraph γ.toResolvedFeynmanGraph)
    (hγ : ResolvedExternalLegSaturated G γ) (hB : ResolvedForestExternalLegSaturated B) :
    ResolvedForestExternalLegSaturated (ResolvedAdmissibleSubgraph.promote γ B) := by
  intro δ' hδ'
  simp only [ResolvedAdmissibleSubgraph.promote_elements, Finset.mem_image] at hδ'
  obtain ⟨b, hb, rfl⟩ := hδ'
  exact resolvedExternalLegSaturated_promote_of_nested γ hγ (hB b hb)

end GaugeGeometry.QFT.Combinatorial
