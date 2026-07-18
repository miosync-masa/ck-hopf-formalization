import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCanonicalSupportedCarrierAudit
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCanonicalCarrierProper

/-!
# R-6c-body-402 — ambient-support carrier emptying: a supported canonical carrier from any `W` (PROVED)

Four-hundred-and-second genuine-body step — the emptying wrapper.  Instead of identifying `G = ofFlatGraphWithUniqueIds
Gf` (which drags in the unproven `mapPerm`-naturality of the `Multiset.toList.zipIdx` id-assignment), the carrier is
emptied by AMBIENT SUPPORT itself: on a malformed ambient the index is `∅`; on a supported ambient it is `W`'s.  Then the
body-397 ambient gate is DERIVED from `W`, with NO exact-unique-lift test and NO id naturality.

* `ResolvedAmbientSupported G` — `AmbientEdgesSupported G ∧ AmbientLegsSupported G`;
* `ambientSupported_mapPerm_iff` — `mapPerm`-invariance (recover the source edge/leg by `mem_map`, transport the vertex
  membership by `σ` / `σ⁻¹`);
* `emptyProperForestIndex` — the `∅`-carrier index;
* `ResolvedCanonicalCarrierProperSupply.supportedIndex` — `W.index` on supported `G`, `∅` otherwise;
* `.toSupportedCarrier` — the supported canonical interface (`carrier_mapPerm` synchronises both `if`-branches via the
  `iff`; `starOf` / `hCD` / `star_mapPerm` are `W`'s, `hCD` restricted to the supported branch);
* `.toSupportedCarrierAmbient` — the body-397 gate: membership forces the supported branch, whose `h.1` / `h.2` is the
  support;
* `supportedIndex_eq_of_ambientSupported` — on a supported `G` (e.g. body-401's `WellFormed` payload) the carrier is
  unchanged.

Per the HALT: the ambient-support socket becomes DERIVED from `W`; only malformed graphs are emptied; NO exact-unique-lift
test, NO id-assignment naturality; `W` itself STAYS an honest interface (NOT claimed built from `canonicalCover`).  No
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

/-- **R-6c-body-402 — ambient support of a resolved graph** (edges + legs, as one predicate). -/
def ResolvedAmbientSupported (G : ResolvedFeynmanGraph) : Prop :=
  AmbientEdgesSupported G ∧ AmbientLegsSupported G

private theorem perm_mem_image_iff (σ : Equiv.Perm VertexId) (v : VertexId) (s : Finset VertexId) :
    σ v ∈ s.image σ ↔ v ∈ s := by
  constructor
  · intro hv
    obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp hv
    rwa [σ.injective hwv] at hw
  · intro hv; exact Finset.mem_image_of_mem σ hv

/-- **R-6c-body-402 — ambient support is `mapPerm`-invariant.** -/
theorem ambientSupported_mapPerm_iff (G : ResolvedFeynmanGraph) (σ : Equiv.Perm VertexId) :
    ResolvedAmbientSupported (G.mapPerm σ) ↔ ResolvedAmbientSupported G := by
  constructor
  · rintro ⟨hE, hL⟩
    refine ⟨fun e₀ he₀ => ?_, fun ℓ₀ hℓ₀ => ?_⟩
    · have hmem : e₀.map σ ∈ (G.mapPerm σ).internalEdges := Multiset.mem_map_of_mem _ he₀
      obtain ⟨hs, ht⟩ := hE (e₀.map σ) hmem
      exact ⟨(perm_mem_image_iff σ e₀.source G.vertices).mp hs,
        (perm_mem_image_iff σ e₀.target G.vertices).mp ht⟩
    · have hmem : ℓ₀.map σ ∈ (G.mapPerm σ).externalLegs := Multiset.mem_map_of_mem _ hℓ₀
      exact (perm_mem_image_iff σ ℓ₀.attachedTo G.vertices).mp (hL (ℓ₀.map σ) hmem)
  · rintro ⟨hE, hL⟩
    refine ⟨fun e he => ?_, fun ℓ hℓ => ?_⟩
    · obtain ⟨e₀, he₀, rfl⟩ := Multiset.mem_map.mp he
      obtain ⟨hs, ht⟩ := hE e₀ he₀
      exact ⟨(perm_mem_image_iff σ e₀.source G.vertices).mpr hs,
        (perm_mem_image_iff σ e₀.target G.vertices).mpr ht⟩
    · obtain ⟨ℓ₀, hℓ₀, rfl⟩ := Multiset.mem_map.mp hℓ
      exact (perm_mem_image_iff σ ℓ₀.attachedTo G.vertices).mpr (hL ℓ₀ hℓ₀)

/-- **R-6c-body-402 — the empty proper-forest index.** -/
def emptyProperForestIndex (G : ResolvedFeynmanGraph) : ResolvedProperForestFiniteIndex G where
  carrier := ∅
  mem_proper := fun A hA => absurd hA (Finset.notMem_empty A)

namespace ResolvedCanonicalCarrierProperSupply

variable (W : ResolvedCanonicalCarrierProperSupply)

/-- **R-6c-body-402 — the ambient-support-emptied index.**  `W`'s index on a supported graph, `∅` otherwise. -/
noncomputable def supportedIndex (G : ResolvedFeynmanGraph) : ResolvedProperForestFiniteIndex G where
  carrier := if ResolvedAmbientSupported G then (W.index G).carrier else ∅
  mem_proper := by
    intro A hA
    by_cases h : ResolvedAmbientSupported G
    · rw [if_pos h] at hA; exact (W.index G).mem_proper A hA
    · rw [if_neg h] at hA; exact absurd hA (Finset.notMem_empty A)

@[simp] theorem supportedIndex_carrier (G : ResolvedFeynmanGraph) :
    (W.supportedIndex G).carrier = if ResolvedAmbientSupported G then (W.index G).carrier else ∅ :=
  rfl

/-- **R-6c-body-402 — the supported canonical carrier interface** (only malformed graphs emptied). -/
noncomputable def toSupportedCarrier : ResolvedCanonicalCarrierProperSupply where
  index := W.supportedIndex
  starOf := W.starOf
  hCD := by
    intro G A hA
    rw [supportedIndex_carrier] at hA
    by_cases h : ResolvedAmbientSupported G
    · rw [if_pos h] at hA; exact W.hCD G A hA
    · rw [if_neg h] at hA; exact absurd hA (Finset.notMem_empty A)
  carrier_mapPerm := by
    intro G σ
    rw [supportedIndex_carrier, supportedIndex_carrier]
    by_cases h : ResolvedAmbientSupported G
    · rw [if_pos ((ambientSupported_mapPerm_iff G σ).mpr h), if_pos h]
      ext A
      rw [W.carrier_mapPerm G σ]
    · rw [if_neg (fun hs => h ((ambientSupported_mapPerm_iff G σ).mp hs)), if_neg h]
      simp
  star_mapPerm := W.star_mapPerm

/-- **R-6c-body-402 — the body-397 ambient gate, DERIVED from the supported carrier.**  Carrier membership forces the
supported branch, whose conjuncts are the endpoint support. -/
def toSupportedCarrierAmbient :
    ResolvedCarrierAmbientSupportSupply W.toSupportedCarrier.toData where
  edges_supported_of_mem := by
    intro G A hA
    by_cases h : ResolvedAmbientSupported G
    · exact h.1
    · have hA' : A ∈ (W.supportedIndex G).carrier := hA
      rw [supportedIndex_carrier, if_neg h] at hA'
      exact absurd hA' (Finset.notMem_empty A)
  legs_supported_of_mem := by
    intro G A hA
    by_cases h : ResolvedAmbientSupported G
    · exact h.2
    · have hA' : A ∈ (W.supportedIndex G).carrier := hA
      rw [supportedIndex_carrier, if_neg h] at hA'
      exact absurd hA' (Finset.notMem_empty A)

/-- **R-6c-body-402 — on a supported graph the carrier is unchanged** (so body-401's `WellFormed` payload keeps `W`'s
carrier). -/
theorem supportedIndex_eq_of_ambientSupported {G : ResolvedFeynmanGraph}
    (h : ResolvedAmbientSupported G) : (W.supportedIndex G).carrier = (W.index G).carrier := by
  rw [supportedIndex_carrier, if_pos h]

end ResolvedCanonicalCarrierProperSupply

end GaugeGeometry.QFT.Combinatorial
