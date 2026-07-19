import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocFlatStarRenameContract
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCDSupportedIndex
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocContractForget
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRawCanonicalCarrier
import GaugeGeometry.QFT.HopfAlgebra.ResolvedCoproductIndex

/-!
# R-6c-body-425 — a genuine supported `W` inhabitant, constructed (PROVED)

Four-hundred-and-twenty-fifth genuine-body step — the culmination.  Body-401 audited the canonical carrier `W`
(`ResolvedCanonicalCarrierProperSupply`) as an interface with no inhabitant, because its `rightTerm_mapPerm` demanded a
strict fresh-star equivariance that body-403 proved INCONSISTENT with freshness.  Bodies 405–424 rebuilt the whole
mechanism WITHOUT that strict law: finite carrier (415), naturality (416/417), ambient-CD emptying (418), the resolved
fresh-star allocator (414), the resolved↔flat contraction identification (419–422), and the fresh star-renaming
correcting permutation (423/424).  This body issues the certificate.

> **A genuine supported `ResolvedCanonicalCarrierProperSupply` inhabitant has been constructed, without strict
> fresh-star equivariance.**

Three layers:
1. `resolvedStarOnForget_isFreshStarAssignment` — the descended star is fresh + injective (414 freshness/injectivity +
   420 spec + 419 forget-injectivity);
2. `resolvedCanonicalContract_hCD_of_mem` — the RawW `hCD`: from carrier membership, the resolved star-contraction's
   forget is connected-divergent, via the chain `membership → ambient CD + proper (418) → flat proper index (419-lib) →
   flat canonical CD (Coproduct) → star-renaming (424) → mapPerm_isConnectedDivergent_iff → 422 → resolved CD`;
3. `canonicalResolvedCarrierProperRawSupply` / `canonicalStarRawFacts` / `canonicalSupportedCarrierProperSupply` — the
   record assembly: the `rightTerm`-free raw canonical carrier (index = `cdSupportedIndex`, starOf = the fresh allocator,
   hCD = layer 2, carrier_mapPerm = 418), its raw star facts (414), and the supported full `W` via body-413's
   `toSupportedCanonicalCarrier`.

Status update: body-401's "`W` is only an interface" becomes **`W` inhabitant constructed**.  This closes the last
carrier root; the coassociativity development's OTHER inhabitants (the full `D`-chain payloads) remain separate open
work.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
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

/-- **R-6c-body-425 (layer 1) — the descended star is a fresh star assignment on `A.forget`.** -/
theorem resolvedStarOnForget_isFreshStarAssignment {G : ResolvedFeynmanGraph}
    (A : ResolvedAdmissibleSubgraph G) (hpf : A.IsProperForest) :
    A.forget.IsFreshStarAssignment (resolvedStarOnForget A) := by
  refine ⟨fun η hη => ?_, fun η₁ hη₁ η₂ hη₂ hstar => ?_⟩
  · obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.mp hη
    rw [resolvedStarOnForget_spec A hpf hδ]
    exact resolvedComponentFreshStar_not_mem_vertices G A δ
  · obtain ⟨δ₁, hδ₁, rfl⟩ := Finset.mem_image.mp hη₁
    obtain ⟨δ₂, hδ₂, rfl⟩ := Finset.mem_image.mp hη₂
    rw [resolvedStarOnForget_spec A hpf hδ₁, resolvedStarOnForget_spec A hpf hδ₂] at hstar
    exact congrArg _ (resolvedComponentFreshStar_injective_on_elements G A hδ₁ hδ₂ hstar)

/-- **R-6c-body-425 (layer 2) — the RawW `hCD`.**  From carrier membership the resolved star-contraction's forget is
connected-divergent — via the flat canonical CD and the star-renaming permutation, with NO strict fresh-star
equivariance. -/
theorem resolvedCanonicalContract_hCD_of_mem {G : ResolvedFeynmanGraph}
    (A : ResolvedAdmissibleSubgraph G) (hmem : A ∈ (cdSupportedIndex G).carrier) :
    (A.contractWithStars (resolvedComponentFreshStar G A)).forget.toClass.IsConnectedDivergent := by
  have hpf : A.IsProperForest := (cdSupportedIndex G).mem_proper A hmem
  have hambCD : G.forget.IsConnectedDivergent := ambientCD_of_mem_cdSupportedIndex hmem
  have hA'mem : A.forget ∈ (G.forget).properDisjointAdmissibleDivergentSubgraphs :=
    A.forget_mem_properDisjointAdmissibleDivergentSubgraphs hpf
  have hcanonCD : (A.forget.contractWithStars A.forget.componentFreshStar).IsConnectedDivergent := by
    have hx := FeynmanGraph.admissibleForestCanonicalContractGraph_hCD_of_ambient_preservation
      (G.forget) hambCD.wellFormed hambCD.self_isConnectedDivergent.isOnePI hambCD A.forget hA'mem
    simpa [FeynmanGraph.admissibleForestContractGraphWithStars,
      FeynmanGraph.admissibleForestCanonicalStarOf] using hx
  have h₂ := A.forget.componentFreshStar_isFreshStarAssignment
  have h₁ := resolvedStarOnForget_isFreshStarAssignment A hpf
  rw [flatStarRename_contractWithStars A.forget (resolvedStarOnForget A)
    A.forget.componentFreshStar h₁ h₂ hambCD.wellFormed] at hcanonCD
  have hs₁CD : (A.forget.contractWithStars (resolvedStarOnForget A)).IsConnectedDivergent :=
    (FeynmanGraph.mapPerm_isConnectedDivergent_iff _ _).mp hcanonCD
  rw [← forget_contractWithStars_resolvedStar A hpf] at hs₁CD
  exact (FeynmanGraphClass.isConnectedDivergent_toClass _).mpr hs₁CD

/-- **R-6c-body-425 (layer 3) — the `rightTerm`-free raw canonical carrier.**  Index = the CD-emptied saturated index,
star = the fresh allocator, `hCD` = layer 2, `carrier_mapPerm` = body-418. -/
noncomputable def canonicalResolvedCarrierProperRawSupply :
    ResolvedCanonicalCarrierProperRawSupply where
  index := cdSupportedIndex
  starOf := fun G A => resolvedComponentFreshStar G A
  hCD := fun _ A hA => resolvedCanonicalContract_hCD_of_mem A hA
  carrier_mapPerm := fun _ σ => cdSupportedIndex_carrier_mapPerm σ

/-- **R-6c-body-425 (layer 3) — the raw star facts** for the fresh allocator (body-414). -/
def canonicalStarRawFacts :
    ResolvedCanonicalStarRawFacts canonicalResolvedCarrierProperRawSupply.toRawData where
  starOf_fresh := fun G' A η _ => resolvedComponentFreshStar_not_mem_vertices G' A η
  starOf_injective := fun G' A => resolvedComponentFreshStar_injective_on_elements G' A

/-- **R-6c-body-425 ∎ — the genuine supported `W` inhabitant.**  Constructed from the raw canonical carrier + raw star
facts via body-413's `toSupportedCanonicalCarrier`, with NO strict fresh-star equivariance.  Body-401's audit verdict
"`W` is only an interface" is hereby updated to "`W` inhabitant constructed". -/
noncomputable def canonicalSupportedCarrierProperSupply :
    ResolvedCanonicalCarrierProperSupply :=
  canonicalResolvedCarrierProperRawSupply.toSupportedCanonicalCarrier canonicalStarRawFacts

end GaugeGeometry.QFT.Combinatorial
