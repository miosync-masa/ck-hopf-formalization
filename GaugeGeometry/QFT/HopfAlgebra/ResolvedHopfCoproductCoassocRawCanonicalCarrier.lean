import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSupportedCarrierEmptying
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRawDataConstructor

/-!
# R-6c-body-413 — supported full `W` from a raw canonical carrier + raw star facts (PROVED)

Four-hundred-and-thirteenth genuine-body step.  Body-412 made a full `ResolvedCoproductProperForestData` constructible
from the `rightTerm`-free raw core plus raw facts, cycle-free.  This body carries that all the way up to the canonical
carrier interface: from a `rightTerm`-free RAW canonical carrier `Wraw` (index / starOf / hCD / carrier_mapPerm — NO
`rightTerm_mapPerm`) plus raw star facts, a supported FULL `W := ResolvedCanonicalCarrierProperSupply` is assembled, with
its heavy `rightTerm_mapPerm` field DERIVED (via the body-412 pipeline) rather than fielded.

* `ResolvedCanonicalCarrierProperRawSupply` — the `rightTerm`-free raw canonical carrier;
* `Wraw.toRawData` — its raw core (`carrier G := (index G).carrier`);
* `Wraw.supportedIndex` / `Wraw.toSupportedRawCarrier` / `Wraw.toSupportedRawAmbient` — body-402's ambient-support
  emptying, transported onto the raw carrier (no `rightTerm_mapPerm` obligation to discharge here);
* `ResolvedCanonicalStarRawFacts.toSupported` — the raw star facts move to the supported raw core by `rfl` (`starOf`
  unchanged);
* `Wraw.toSupportedCanonicalCarrier` — the supported full `W`, `rightTerm_mapPerm := (…toDataOfFreshCorrecting…).rightTerm_mapPerm`;
* `toSupportedCanonicalCarrier_toData` / `ResolvedCanonicalStarRawFacts.toCanonicalStarFacts` — the named bridges back to
  the `D`-facing world.

The whole chain — Raw `W` → support emptying → raw ambient → fresh/injective stars → correcting `τ` → contract graph
equality → class equality → right-term equality — issues `rightTerm_mapPerm` with NO cycle and NO strict star law.

Per the HALT: NO canonical inhabitant of `Wraw` is built; `index` is NOT claimed built from `canonicalCover`; the
deliverable is exactly "Raw `W` + raw star facts → supported full `W`".  The full-`W` body-402 emptying stays intact.  No
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

/-- **R-6c-body-413 — the `rightTerm`-free raw canonical carrier.**  The canonical carrier interface MINUS
`rightTerm_mapPerm` — the honest ingredient list a real model must supply (`index` / `starOf` / `hCD` /
`carrier_mapPerm`).  `rightTerm_mapPerm` is no longer fielded; it is derived downstream via body-412. -/
structure ResolvedCanonicalCarrierProperRawSupply where
  /-- The per-graph proper-forest index (carrier + `mem_proper`). -/
  index : (G : ResolvedFeynmanGraph) → ResolvedProperForestFiniteIndex G
  /-- The star assignment per forest. -/
  starOf : (G : ResolvedFeynmanGraph) → ResolvedAdmissibleSubgraph G →
    (ResolvedFeynmanSubgraph G → VertexId)
  /-- The contraction is connected divergent for every index member. -/
  hCD : ∀ (G : ResolvedFeynmanGraph) (A : ResolvedAdmissibleSubgraph G), A ∈ (index G).carrier →
    ((A.contractWithStars (starOf G A)).forget.toClass.IsConnectedDivergent)
  /-- The index carrier transports by relabeling. -/
  carrier_mapPerm : ∀ (G : ResolvedFeynmanGraph) (σ : Equiv.Perm VertexId),
    (index (G.mapPerm σ)).carrier = ((index G).carrier).image (fun A => A.mapPerm σ)

namespace ResolvedCanonicalCarrierProperRawSupply

variable (Wraw : ResolvedCanonicalCarrierProperRawSupply)

/-- **R-6c-body-413 — the raw core of a raw canonical carrier** (`carrier G := (index G).carrier`). -/
def toRawData : ResolvedCoproductProperForestRawData where
  carrier := fun G => (Wraw.index G).carrier
  starOf := Wraw.starOf
  hCD := Wraw.hCD
  -- `convert` bridges the `DecidableEq ResolvedAdmissibleSubgraph` diamond (subsingleton) between the raw carrier's
  -- `image` instance and `ResolvedCoproductProperForestRawData`'s.
  carrier_mapPerm := fun G σ => by convert Wraw.carrier_mapPerm G σ

/-- **R-6c-body-413 — the ambient-support-emptied index** (body-402, on the raw carrier). -/
noncomputable def supportedIndex (G : ResolvedFeynmanGraph) : ResolvedProperForestFiniteIndex G where
  carrier := if ResolvedAmbientSupported G then (Wraw.index G).carrier else ∅
  mem_proper := by
    intro A hA
    by_cases h : ResolvedAmbientSupported G
    · rw [if_pos h] at hA; exact (Wraw.index G).mem_proper A hA
    · rw [if_neg h] at hA; exact absurd hA (Finset.notMem_empty A)

@[simp] theorem supportedIndex_carrier (G : ResolvedFeynmanGraph) :
    (Wraw.supportedIndex G).carrier
      = if ResolvedAmbientSupported G then (Wraw.index G).carrier else ∅ := rfl

/-- **R-6c-body-413 — the supported raw canonical carrier** (only malformed graphs emptied; NO `rightTerm_mapPerm`
obligation, unlike the full-`W` body-402 version). -/
noncomputable def toSupportedRawCarrier : ResolvedCanonicalCarrierProperRawSupply where
  index := Wraw.supportedIndex
  starOf := Wraw.starOf
  hCD := by
    intro G A hA
    rw [supportedIndex_carrier] at hA
    by_cases h : ResolvedAmbientSupported G
    · rw [if_pos h] at hA; exact Wraw.hCD G A hA
    · rw [if_neg h] at hA; exact absurd hA (Finset.notMem_empty A)
  carrier_mapPerm := by
    intro G σ
    rw [supportedIndex_carrier, supportedIndex_carrier]
    by_cases h : ResolvedAmbientSupported G
    · rw [if_pos ((ambientSupported_mapPerm_iff G σ).mpr h), if_pos h]
      ext A
      rw [Wraw.carrier_mapPerm G σ]
    · rw [if_neg (fun hs => h ((ambientSupported_mapPerm_iff G σ).mp hs)), if_neg h]
      simp

/-- **R-6c-body-413 — the raw ambient-support gate, DERIVED from the supported raw carrier.**  Carrier membership forces
the supported branch, whose conjuncts are the endpoint support. -/
def toSupportedRawAmbient :
    ResolvedCarrierAmbientSupportRawSupply Wraw.toSupportedRawCarrier.toRawData where
  edges_supported_of_mem := by
    intro G A hA
    by_cases h : ResolvedAmbientSupported G
    · exact h.1
    · have hA' : A ∈ (Wraw.supportedIndex G).carrier := hA
      rw [supportedIndex_carrier, if_neg h] at hA'
      exact absurd hA' (Finset.notMem_empty A)
  legs_supported_of_mem := by
    intro G A hA
    by_cases h : ResolvedAmbientSupported G
    · exact h.2
    · have hA' : A ∈ (Wraw.supportedIndex G).carrier := hA
      rw [supportedIndex_carrier, if_neg h] at hA'
      exact absurd hA' (Finset.notMem_empty A)

end ResolvedCanonicalCarrierProperRawSupply

/-- **R-6c-body-413 — raw star facts move to the supported raw core by `rfl`** (`starOf` unchanged by the emptying). -/
def ResolvedCanonicalStarRawFacts.toSupported
    {Wraw : ResolvedCanonicalCarrierProperRawSupply}
    (StarRaw : ResolvedCanonicalStarRawFacts Wraw.toRawData) :
    ResolvedCanonicalStarRawFacts Wraw.toSupportedRawCarrier.toRawData where
  -- field-by-field (the type is indexed by the whole raw core, but both share `starOf = Wraw.starOf`, so the field
  -- types are definitionally equal).
  starOf_fresh := StarRaw.starOf_fresh
  starOf_injective := StarRaw.starOf_injective

namespace ResolvedCanonicalCarrierProperRawSupply

variable (Wraw : ResolvedCanonicalCarrierProperRawSupply)

/-- **R-6c-body-413 ∎ — the supported full `W` from raw canonical carrier + raw star facts.**  The heavy
`rightTerm_mapPerm` field is DERIVED via the body-412 cycle-free pipeline (`toDataOfFreshCorrecting`), not fielded. -/
noncomputable def toSupportedCanonicalCarrier
    (StarRaw : ResolvedCanonicalStarRawFacts Wraw.toRawData) :
    ResolvedCanonicalCarrierProperSupply where
  index := Wraw.toSupportedRawCarrier.index
  starOf := Wraw.toSupportedRawCarrier.starOf
  hCD := Wraw.toSupportedRawCarrier.hCD
  carrier_mapPerm := fun G σ => by convert Wraw.toSupportedRawCarrier.carrier_mapPerm G σ
  rightTerm_mapPerm :=
    (Wraw.toSupportedRawCarrier.toRawData.toDataOfFreshCorrecting
      Wraw.toSupportedRawAmbient StarRaw.toSupported).rightTerm_mapPerm

/-- **R-6c-body-413 — the supported full `W`'s `toData` is exactly the body-412 fresh-correcting `D`.** -/
theorem toSupportedCanonicalCarrier_toData
    (StarRaw : ResolvedCanonicalStarRawFacts Wraw.toRawData) :
    (Wraw.toSupportedCanonicalCarrier StarRaw).toData
      = Wraw.toSupportedRawCarrier.toRawData.toDataOfFreshCorrecting
          Wraw.toSupportedRawAmbient StarRaw.toSupported := rfl

/-- **R-6c-body-413 — the raw star facts are the canonical star facts of the supported full `W`** (field-by-field
`rfl`; `starOf` is shared). -/
def toCanonicalStarFacts
    (StarRaw : ResolvedCanonicalStarRawFacts Wraw.toRawData) :
    ResolvedCanonicalStarFacts (Wraw.toSupportedCanonicalCarrier StarRaw).toData where
  starOf_fresh := StarRaw.starOf_fresh
  starOf_injective := StarRaw.starOf_injective

end ResolvedCanonicalCarrierProperRawSupply

end GaugeGeometry.QFT.Combinatorial
