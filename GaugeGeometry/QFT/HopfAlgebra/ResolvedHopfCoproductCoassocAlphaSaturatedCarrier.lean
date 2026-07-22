import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaUnconditionalizationFrontier
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocUniqueClosureMigration
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocUniqueIdSupportedW

/-!
# R-6c-body-533 — the canonical external-leg-saturated carrier `W″` (PROVED)

Five-hundred-and-thirty-third genuine-body step — realizing the fourth emptying axis of body-532 as an ACTUAL carrier.
`W″` is `W′` filtered by the intrinsic `ResolvedForestExternalLegSaturated`: a genuine axis that removes the non-saturated
forests, NOT a claim that every `W′` forest is saturated.  On `W″`, `LegModel` is no longer an independent input — it is a
theorem of carrier membership.

* `canonicalLegSaturatedIndex` — `W′`'s proper-forest index, filtered by forest saturation (`mem_proper` inherited);
* `canonicalLegSaturatedIndex_carrier_mapPerm` — the axis is `mapPerm`-closed (`W′.carrier_mapPerm` + body-532's
  saturation invariance);
* `canonicalLegSaturatedCarrierProperSupply` — the full `W″` supply (same allocator / `hCD` / `rightTerm` route as `W′`,
  filter-projected);
* `mem_canonicalLegSaturatedCarrier_iff` / `_full_iff` + accessors — the two-condition and six-condition membership APIs;
* `canonicalLegSaturatedStarFacts` / `...CarrierProperProvider` — the inherited canonical facts (same allocator);
* `canonicalLegSaturatedExternalLegSaturationSupply` — `LegModel` on `W″`, CANONICAL DERIVED from membership.

Per the HALT/guards: no `W″` nonempty claim; no "`W′` forests are all saturated" claim; `selectedOuter` /
`recoveredRawUnion` / corrected-quotient `W″` membership are NOT entered; bodies 496–531 are NOT re-keyed to `W″`; the
final coassoc theorem is NOT migrated; `Parent` / decontraction-CD is NOT derived; no new typeclass; `W′` is NOT modified;
strict `StarProm` / `InnerStarRaw` stay ZERO; NO unconditional-coassoc claim.  No facade, no flat term, no `forgetHopf`, no
rep/perm, and NO `promote_collapse` / singleton / floor-297.
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

/-! ## Step 1 — the filtered proper-forest index -/

/-- **R-6c-body-533 — `W′`'s proper-forest index, filtered by forest saturation.** -/
noncomputable def canonicalLegSaturatedIndex (G : ResolvedFeynmanGraph) :
    ResolvedProperForestFiniteIndex G where
  carrier := (canonicalUniqueSupportedCarrierProperSupply.index G).carrier.filter ResolvedForestExternalLegSaturated
  mem_proper := fun A hA =>
    (canonicalUniqueSupportedCarrierProperSupply.index G).mem_proper A (Finset.mem_filter.mp hA).1

/-! ## Step 2 — `mapPerm` closure of the axis -/

/-- **R-6c-body-533 ∎ — the saturated axis is `mapPerm`-closed.** -/
theorem canonicalLegSaturatedIndex_carrier_mapPerm (G : ResolvedFeynmanGraph) (σ : Equiv.Perm VertexId) :
    (canonicalLegSaturatedIndex (G.mapPerm σ)).carrier
      = (canonicalLegSaturatedIndex G).carrier.image (fun A => A.mapPerm σ) := by
  simp only [canonicalLegSaturatedIndex]
  rw [canonicalUniqueSupportedCarrierProperSupply.carrier_mapPerm]
  ext A
  simp only [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨B, hB, rfl⟩, hsat⟩
    exact ⟨B, ⟨hB, (resolvedForestExternalLegSaturated_mapPerm_iff σ B).mp hsat⟩, rfl⟩
  · rintro ⟨B, ⟨hB, hsat⟩, rfl⟩
    exact ⟨⟨B, hB, rfl⟩, (resolvedForestExternalLegSaturated_mapPerm_iff σ B).mpr hsat⟩

/-! ## Step 3 — the full `W″` canonical supply -/

/-- **R-6c-body-533 ∎ — the canonical external-leg-saturated carrier `W″`.**  Same allocator / `hCD` / `rightTerm` route
as `W′`, filter-projected. -/
noncomputable def canonicalLegSaturatedCarrierProperSupply : ResolvedCanonicalCarrierProperSupply where
  index := canonicalLegSaturatedIndex
  starOf := canonicalUniqueSupportedCarrierProperSupply.starOf
  hCD := fun G A hA =>
    canonicalUniqueSupportedCarrierProperSupply.hCD G A (Finset.mem_filter.mp hA).1
  carrier_mapPerm := fun G σ => by convert canonicalLegSaturatedIndex_carrier_mapPerm G σ using 2
  rightTerm_mapPerm := fun G σ A hA hAσ =>
    canonicalUniqueSupportedCarrierProperSupply.rightTerm_mapPerm G σ A
      (Finset.mem_filter.mp hA).1 (Finset.mem_filter.mp hAσ).1

/-! ## Step 4 — the membership API -/

/-- **R-6c-body-533 ∎ — `W″` membership = `W′` membership + forest saturation.** -/
theorem mem_canonicalLegSaturatedCarrier_iff {G : ResolvedFeynmanGraph} (A : ResolvedAdmissibleSubgraph G) :
    A ∈ (canonicalLegSaturatedCarrierProperSupply.index G).carrier
      ↔ A ∈ (canonicalUniqueSupportedCarrierProperSupply.index G).carrier
          ∧ ResolvedForestExternalLegSaturated A :=
  Finset.mem_filter

/-- **R-6c-body-533 ∎ — `W″` membership, fully expanded** (the six CK conditions). -/
theorem mem_canonicalLegSaturatedCarrier_full_iff {G : ResolvedFeynmanGraph} (A : ResolvedAdmissibleSubgraph G) :
    A ∈ (canonicalLegSaturatedCarrierProperSupply.index G).carrier
      ↔ ResolvedAmbientSupported G ∧ G.forget.IsConnectedDivergent ∧ G.EdgeIdsUnique ∧ G.LegIdsUnique
          ∧ A.IsProperForest ∧ ResolvedForestExternalLegSaturated A := by
  rw [mem_canonicalLegSaturatedCarrier_iff, mem_canonicalUniqueSupportedCarrier_iff]
  tauto

/-- **R-6c-body-533 — accessor: `W″` membership → `W′` membership.** -/
theorem canonicalLegSaturatedCarrier_mem_W' {G : ResolvedFeynmanGraph} {A : ResolvedAdmissibleSubgraph G}
    (hA : A ∈ (canonicalLegSaturatedCarrierProperSupply.index G).carrier) :
    A ∈ (canonicalUniqueSupportedCarrierProperSupply.index G).carrier :=
  ((mem_canonicalLegSaturatedCarrier_iff A).mp hA).1

/-- **R-6c-body-533 — accessor: `W″` membership → forest saturation.** -/
theorem canonicalLegSaturatedCarrier_saturated {G : ResolvedFeynmanGraph} {A : ResolvedAdmissibleSubgraph G}
    (hA : A ∈ (canonicalLegSaturatedCarrierProperSupply.index G).carrier) :
    ResolvedForestExternalLegSaturated A :=
  ((mem_canonicalLegSaturatedCarrier_iff A).mp hA).2

/-! ## Step 5 — inherited canonical facts (same allocator) -/

/-- **R-6c-body-533 ∎ — `W″` canonical star facts** (the `W′` allocator is unchanged). -/
def canonicalLegSaturatedStarFacts :
    ResolvedCanonicalStarFacts canonicalLegSaturatedCarrierProperSupply.toData where
  starOf_fresh := fun G' A η _ => resolvedComponentFreshStar_not_mem_vertices G' A η
  starOf_injective := fun G' A => resolvedComponentFreshStar_injective_on_elements G' A

/-- **R-6c-body-533 ∎ — `W″` carrier-proper provider.** -/
def canonicalLegSaturatedCarrierProperProvider :
    ResolvedCarrierProperProvider canonicalLegSaturatedCarrierProperSupply.toData :=
  canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider

/-! ## Step 6 — `LegModel` absorption -/

/-- **R-6c-body-533 ∎ — `LegModel` on `W″`, CANONICAL DERIVED from membership.** -/
def canonicalLegSaturatedExternalLegSaturationSupply :
    ResolvedCarrierExternalLegSaturationSupply canonicalLegSaturatedCarrierProperSupply.toData :=
  ResolvedCarrierExternalLegSaturationSupply.ofForestSaturated
    (fun _A hA => canonicalLegSaturatedCarrier_saturated hA)

end GaugeGeometry.QFT.Combinatorial
