import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaCarrierLegSaturation
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfSubgraphMapPerm

/-!
# R-6c-body-532 — unconditionalization frontier audit (PROVED)

Five-hundred-and-thirty-second genuine-body step — the frontier audit fixing EXACTLY the boundary between the two model
laws (body-531).  The question is not "is absolute unconditionality possible" but the precise verdict:

```text
combinatorial unconditionality:  reachable iff we move to a W'' saturation carrier
physics unconditionality:        inverse-decontraction divergence class modulo
```

## The leg law is `mapPerm`-invariant (→ a fourth-emptying-axis candidate)

* `ResolvedExternalLegSaturated` / `ResolvedForestExternalLegSaturated` — the intrinsic, carrier-INDEPENDENT saturation
  predicates;
* `ResolvedCarrierExternalLegSaturationSupply.ofForestSaturated` — the body-531 supply is exactly "every live carrier
  member is forest-saturated";
* `resolvedExternalLegSaturated_mapPerm_iff` / `resolvedForestExternalLegSaturated_mapPerm_iff` — the load-bearing
  feasibility fact: saturation is INVARIANT under vertex relabeling (`filter`/`map` commute; `ResolvedExternalLeg.map σ`
  and `σ` are injective; `Multiset.map_le_map_iff`).  So the `filter`-saturated sub-carrier is `mapPerm`-closed — a genuine
  candidate for a fourth emptying axis of the unique-ID carrier, NOT an ad-hoc restriction.

## The `parentCD` frontier — physics, not combinatorics

Every existing class (`IsDivergencePreservedByContract` / `...AdmissibleForestContract` / `Measure.contract_preserves_CD`)
runs `parent → quotient`.  The needed law is the INVERSE — `quotient component + inserted divergent forest →
de-contracted parent` — and since `DivergenceMeasure.degree` is arbitrary, it is NOT derivable from the current
environment and is NOT resolved by any emptying axis.  It stays a genuine power-counting (divergence) class.

## Verdict

```text
LegModel:  mapPerm-invariant + filtered-carrier closure feasible  → W'' fourth-emptying-axis candidate  (combinatorial)
Parent:    inverse-decontraction divergence law                    → honest divergence typeclass         (physics)
```

The two options are now sharply posed: BUILD the W'' saturation carrier (to absorb `LegModel` combinatorially), or CLOSE
on the current `W'` as the final theorem modulo the two CK-model laws.  Neither is started here.

Per the HALT/guards: no `LegModel` inhabitant is fabricated on the current `W'`; the two supplies are NOT wrapped into a
class and called "unconditional"; the `W''` migration is NOT started; `parentCD` is NOT built from forward preservation;
the coassoc theorem is NOT re-issued; strict `StarProm` / `InnerStarRaw` stay ZERO; NO unconditional-coassoc claim.  No
facade, no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
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

/-! ## Step 1 — the intrinsic saturation predicates + the carrier adapter -/

/-- **R-6c-body-532 — intrinsic external-leg saturation** (carrier-independent). -/
def ResolvedExternalLegSaturated (H : ResolvedFeynmanGraph) (δ : ResolvedFeynmanSubgraph H) : Prop :=
  H.externalLegs.filter (fun ℓ => ℓ.attachedTo ∈ δ.vertices) ≤ δ.externalLegs

/-- **R-6c-body-532 — forest external-leg saturation** (all components). -/
def ResolvedForestExternalLegSaturated {H : ResolvedFeynmanGraph} (A : ResolvedAdmissibleSubgraph H) : Prop :=
  ∀ δ ∈ A.elements, ResolvedExternalLegSaturated H δ

/-- **R-6c-body-532 ∎ — the carrier supply is exactly "every live carrier member is forest-saturated".** -/
def ResolvedCarrierExternalLegSaturationSupply.ofForestSaturated {D : ResolvedCoproductProperForestData}
    (h : ∀ {H : ResolvedFeynmanGraph} (A : ResolvedAdmissibleSubgraph H), A ∈ D.carrier H →
      ResolvedForestExternalLegSaturated A) :
    ResolvedCarrierExternalLegSaturationSupply D where
  externalLegs_saturated_of_mem := fun {_H _B} hB {_δ} hδ => h _ hB _ hδ

/-! ## Step 2 — `mapPerm` invariance (the fourth-emptying-axis feasibility) -/

/-- **R-6c-body-532 ∎ — saturation is invariant under vertex relabeling.** -/
theorem resolvedExternalLegSaturated_mapPerm_iff (σ : Equiv.Perm VertexId)
    {H : ResolvedFeynmanGraph} (δ : ResolvedFeynmanSubgraph H) :
    ResolvedExternalLegSaturated (H.mapPerm σ) (δ.mapPerm σ) ↔ ResolvedExternalLegSaturated H δ := by
  have hmapinj : Function.Injective (ResolvedExternalLeg.map σ) := by
    intro ℓ₁ ℓ₂ h
    cases ℓ₁; cases ℓ₂
    simp only [ResolvedExternalLeg.map, ResolvedExternalLeg.mk.injEq] at h ⊢
    exact ⟨h.1, σ.injective h.2.1, h.2.2⟩
  have hfm : (H.externalLegs.map (ResolvedExternalLeg.map σ)).filter
        (fun ℓ => ℓ.attachedTo ∈ δ.vertices.image σ)
      = (H.externalLegs.filter (fun ℓ => ℓ.attachedTo ∈ δ.vertices)).map (ResolvedExternalLeg.map σ) := by
    rw [Multiset.filter_map]
    exact congrArg (Multiset.map (ResolvedExternalLeg.map σ))
      (Multiset.filter_congr (fun ℓ _ => σ.injective.mem_finset_image))
  simp only [ResolvedExternalLegSaturated, ResolvedFeynmanGraph.mapPerm,
    ResolvedFeynmanSubgraph.mapPerm_externalLegs, ResolvedFeynmanSubgraph.mapPerm_vertices, hfm,
    Multiset.map_le_map_iff hmapinj]

/-- **R-6c-body-532 ∎ — forest saturation is invariant under vertex relabeling.** -/
theorem resolvedForestExternalLegSaturated_mapPerm_iff (σ : Equiv.Perm VertexId)
    {H : ResolvedFeynmanGraph} (A : ResolvedAdmissibleSubgraph H) :
    ResolvedForestExternalLegSaturated (A.mapPerm σ) ↔ ResolvedForestExternalLegSaturated A := by
  unfold ResolvedForestExternalLegSaturated
  constructor
  · intro h δ hδ
    have hmem : δ.mapPerm σ ∈ (A.mapPerm σ).elements := by
      simp only [ResolvedAdmissibleSubgraph.mapPerm_elements, Finset.mem_image]
      exact ⟨δ, hδ, rfl⟩
    exact (resolvedExternalLegSaturated_mapPerm_iff σ δ).mp (h _ hmem)
  · intro h δ' hδ'
    simp only [ResolvedAdmissibleSubgraph.mapPerm_elements, Finset.mem_image] at hδ'
    obtain ⟨δ, hδ, rfl⟩ := hδ'
    exact (resolvedExternalLegSaturated_mapPerm_iff σ δ).mpr (h δ hδ)

end GaugeGeometry.QFT.Combinatorial
