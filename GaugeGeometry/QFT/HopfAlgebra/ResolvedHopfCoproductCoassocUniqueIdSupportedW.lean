import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSupportedWMembership

/-!
# R-6c-body-442 — the third emptying axis: unique-ID-supported canonical carrier `W'` (PROVED)

Four-hundred-and-forty-second genuine-body step — repairing the `∀ G, EdgeIdsUnique`/`∀ G, LegIdsUnique` over-universal
that body-441's final signature X-rayed.  Those are FALSE on arbitrary resolved graphs (a canonical payload can have
unique ids while a random ambient does not).  The honest fix mirrors body-397's global-ambient-support repair and
body-418's CD emptying: a **third emptying axis** — the canonical carrier is EMPTY on ambients whose edge/leg ids are not
unique.  Then live carrier membership `z.1.2` recovers id-uniqueness, exactly as it already recovers ambient support / CD.

* `ResolvedUniqueIds G := G.EdgeIdsUnique ∧ G.LegIdsUnique`, with `resolvedUniqueIds_mapPerm_iff` (relabeling preserves
  id-uniqueness: `ResolvedFeynmanEdge.map` keeps `edgeId` and is injective, via the `σ⁻¹` round-trip);
* `uniqueIdSupportedIndex` — the CD-supported index emptied by `ResolvedUniqueIds` (`carrier_mapPerm` and `hCD` inherited
  from `cdSupportedIndex` / the body-425 raw supply);
* `canonicalUniqueSupportedW` — the new canonical carrier, `= raw.toSupportedCanonicalCarrier canonicalStarRawFacts`;
* `mem_canonicalUniqueSupportedCarrier_iff` — `A ∈ … ↔ ResolvedAmbientSupported G ∧ G.forget.IsConnectedDivergent ∧
  G.EdgeIdsUnique ∧ G.LegIdsUnique ∧ A.IsProperForest`; `edgeIdsUnique_of_carrier_mem` / `legIdsUnique_of_carrier_mem`
  are the live accessors.

Per the HALT: this body builds ONLY the carrier + membership API; the closure chain (bodies 427/439) is NOT migrated here
(that is the next body).  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO strict `star_mapPerm` /
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

/-- **R-6c-body-442 — unique edge/leg ids on the ambient.** -/
def ResolvedUniqueIds (G : ResolvedFeynmanGraph) : Prop := G.EdgeIdsUnique ∧ G.LegIdsUnique

variable {G : ResolvedFeynmanGraph}

/-! ### `mapPerm`-invariance of id-uniqueness. -/

theorem edgeIdsUnique_mapPerm (σ : Equiv.Perm VertexId) (h : G.EdgeIdsUnique) :
    (G.mapPerm σ).EdgeIdsUnique := by
  intro e₁ h₁ e₂ h₂ hid
  have hIE : (G.mapPerm σ).internalEdges = G.internalEdges.map (ResolvedFeynmanEdge.map σ) := rfl
  obtain ⟨a₁, ha₁, rfl⟩ := Multiset.mem_map.mp (hIE ▸ h₁)
  obtain ⟨a₂, ha₂, rfl⟩ := Multiset.mem_map.mp (hIE ▸ h₂)
  rw [h a₁ ha₁ a₂ ha₂ hid]

theorem legIdsUnique_mapPerm (σ : Equiv.Perm VertexId) (h : G.LegIdsUnique) :
    (G.mapPerm σ).LegIdsUnique := by
  intro ℓ₁ h₁ ℓ₂ h₂ hid
  have hLE : (G.mapPerm σ).externalLegs = G.externalLegs.map (ResolvedExternalLeg.map σ) := rfl
  obtain ⟨b₁, hb₁, rfl⟩ := Multiset.mem_map.mp (hLE ▸ h₁)
  obtain ⟨b₂, hb₂, rfl⟩ := Multiset.mem_map.mp (hLE ▸ h₂)
  rw [h b₁ hb₁ b₂ hb₂ hid]

theorem resolvedUniqueIds_mapPerm (σ : Equiv.Perm VertexId) (h : ResolvedUniqueIds G) :
    ResolvedUniqueIds (G.mapPerm σ) :=
  ⟨edgeIdsUnique_mapPerm σ h.1, legIdsUnique_mapPerm σ h.2⟩

/-- **R-6c-body-442 — id-uniqueness is relabeling-invariant.** -/
theorem resolvedUniqueIds_mapPerm_iff (σ : Equiv.Perm VertexId) :
    ResolvedUniqueIds (G.mapPerm σ) ↔ ResolvedUniqueIds G := by
  constructor
  · intro h
    have hb := resolvedUniqueIds_mapPerm σ⁻¹ h
    rwa [← ResolvedFeynmanGraph.mapPerm_mul, inv_mul_cancel, ResolvedFeynmanGraph.mapPerm_one] at hb
  · exact resolvedUniqueIds_mapPerm σ

/-! ### The unique-ID emptying. -/

/-- **R-6c-body-442 — the unique-ID-emptied index.**  The CD-supported index, further emptied on ambients without unique
edge/leg ids. -/
noncomputable def uniqueIdSupportedIndex (G : ResolvedFeynmanGraph) : ResolvedProperForestFiniteIndex G where
  carrier := if ResolvedUniqueIds G then (cdSupportedIndex G).carrier else ∅
  mem_proper := by
    intro A hA
    by_cases h : ResolvedUniqueIds G
    · rw [if_pos h] at hA; exact (cdSupportedIndex G).mem_proper A hA
    · rw [if_neg h] at hA; exact absurd hA (Finset.notMem_empty A)

@[simp] theorem uniqueIdSupportedIndex_carrier (G : ResolvedFeynmanGraph) :
    (uniqueIdSupportedIndex G).carrier
      = if ResolvedUniqueIds G then (cdSupportedIndex G).carrier else ∅ := rfl

theorem mem_cdSupportedIndex_of_uniqueId {A : ResolvedAdmissibleSubgraph G}
    (hA : A ∈ (uniqueIdSupportedIndex G).carrier) : A ∈ (cdSupportedIndex G).carrier := by
  by_cases h : ResolvedUniqueIds G
  · rwa [uniqueIdSupportedIndex_carrier, if_pos h] at hA
  · rw [uniqueIdSupportedIndex_carrier, if_neg h] at hA; exact absurd hA (Finset.notMem_empty A)

theorem uniqueIds_of_mem_uniqueIdSupportedIndex {A : ResolvedAdmissibleSubgraph G}
    (hA : A ∈ (uniqueIdSupportedIndex G).carrier) : ResolvedUniqueIds G := by
  by_cases h : ResolvedUniqueIds G
  · exact h
  · rw [uniqueIdSupportedIndex_carrier, if_neg h] at hA; exact absurd hA (Finset.notMem_empty A)

theorem uniqueIdSupportedIndex_carrier_mapPerm (G : ResolvedFeynmanGraph) (σ : Equiv.Perm VertexId) :
    (uniqueIdSupportedIndex (G.mapPerm σ)).carrier
      = ((uniqueIdSupportedIndex G).carrier).image (fun A => A.mapPerm σ) := by
  rw [uniqueIdSupportedIndex_carrier, uniqueIdSupportedIndex_carrier]
  by_cases h : ResolvedUniqueIds G
  · rw [if_pos ((resolvedUniqueIds_mapPerm_iff σ).mpr h), if_pos h]
    exact cdSupportedIndex_carrier_mapPerm σ
  · rw [if_neg (fun h' => h ((resolvedUniqueIds_mapPerm_iff σ).mp h')), if_neg h, Finset.image_empty]

/-! ### The unique-ID-supported canonical carrier. -/

/-- **R-6c-body-442 — the raw supply on the unique-ID-emptied index.**  `starOf` / `hCD` are the body-425 canonical
allocator's, restricted through `mem_cdSupportedIndex_of_uniqueId`. -/
noncomputable def canonicalUniqueResolvedCarrierProperRawSupply :
    ResolvedCanonicalCarrierProperRawSupply where
  index := uniqueIdSupportedIndex
  starOf := fun G A => resolvedComponentFreshStar G A
  hCD := fun G A hA => canonicalResolvedCarrierProperRawSupply.hCD G A (mem_cdSupportedIndex_of_uniqueId hA)
  carrier_mapPerm := uniqueIdSupportedIndex_carrier_mapPerm

/-- **R-6c-body-442 — the canonical star raw facts for the unique-ID raw supply** (same allocator as body-425). -/
def canonicalUniqueStarRawFacts :
    ResolvedCanonicalStarRawFacts canonicalUniqueResolvedCarrierProperRawSupply.toRawData where
  starOf_fresh := fun G' A η _ => resolvedComponentFreshStar_not_mem_vertices G' A η
  starOf_injective := fun G' A => resolvedComponentFreshStar_injective_on_elements G' A

/-- **R-6c-body-442 ∎ — the unique-ID-supported canonical carrier `W'`.** -/
noncomputable def canonicalUniqueSupportedCarrierProperSupply : ResolvedCanonicalCarrierProperSupply :=
  canonicalUniqueResolvedCarrierProperRawSupply.toSupportedCanonicalCarrier canonicalUniqueStarRawFacts

/-- **R-6c-body-442 ∎ — the unique-ID carrier membership criterion.**  Membership now also recovers edge/leg id
uniqueness — the third emptying axis, read off as one condition. -/
theorem mem_canonicalUniqueSupportedCarrier_iff {G : ResolvedFeynmanGraph}
    (A : ResolvedAdmissibleSubgraph G) :
    A ∈ (canonicalUniqueSupportedCarrierProperSupply.index G).carrier
      ↔ ResolvedAmbientSupported G ∧ G.forget.IsConnectedDivergent
        ∧ G.EdgeIdsUnique ∧ G.LegIdsUnique ∧ A.IsProperForest := by
  show A ∈ (canonicalUniqueResolvedCarrierProperRawSupply.supportedIndex G).carrier ↔ _
  rw [ResolvedCanonicalCarrierProperRawSupply.supportedIndex_carrier]
  by_cases hs : ResolvedAmbientSupported G
  · rw [if_pos hs]
    show A ∈ (uniqueIdSupportedIndex G).carrier ↔ _
    rw [uniqueIdSupportedIndex_carrier]
    by_cases hu : ResolvedUniqueIds G
    · rw [if_pos hu]
      show A ∈ (cdSupportedIndex G).carrier ↔ _
      rw [cdSupportedIndex_carrier]
      by_cases hcd : G.forget.IsConnectedDivergent
      · rw [if_pos hcd]
        simp only [saturatedProperForestIndex, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h => ⟨hs, hcd, hu.1, hu.2, h⟩, fun h => h.2.2.2.2⟩
      · rw [if_neg hcd]
        constructor
        · exact fun h => absurd h (Finset.notMem_empty A)
        · exact fun h => absurd h.2.1 hcd
    · rw [if_neg hu]
      constructor
      · exact fun h => absurd h (Finset.notMem_empty A)
      · exact fun h => absurd (⟨h.2.2.1, h.2.2.2.1⟩ : ResolvedUniqueIds G) hu
  · rw [if_neg hs]
    constructor
    · exact fun h => absurd h (Finset.notMem_empty A)
    · exact fun h => absurd h.1 hs

/-- **R-6c-body-442 — live edge-id uniqueness from carrier membership.** -/
theorem edgeIdsUnique_of_carrier_mem {G : ResolvedFeynmanGraph}
    {A : ResolvedAdmissibleSubgraph G}
    (hA : A ∈ (canonicalUniqueSupportedCarrierProperSupply.index G).carrier) : G.EdgeIdsUnique :=
  ((mem_canonicalUniqueSupportedCarrier_iff A).mp hA).2.2.1

/-- **R-6c-body-442 — live leg-id uniqueness from carrier membership.** -/
theorem legIdsUnique_of_carrier_mem {G : ResolvedFeynmanGraph}
    {A : ResolvedAdmissibleSubgraph G}
    (hA : A ∈ (canonicalUniqueSupportedCarrierProperSupply.index G).carrier) : G.LegIdsUnique :=
  ((mem_canonicalUniqueSupportedCarrier_iff A).mp hA).2.2.2.1

end GaugeGeometry.QFT.Combinatorial
