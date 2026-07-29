import GaugeGeometry.QFT.HopfAlgebra.Phi4ResolvedRigidification
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaUnconditionalizationFrontier
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSupportedCarrierEmptying

/-!
# QFT-R1-body-586 — family-indexed W″ finite index + rigidified landing criterion

Body-585 built the chosen unique-ID rigidification section `phi4RigidifiedGraph : Phi4HopfGen →
ResolvedFeynmanGraph`, but left W″ membership OPEN.  This body re-keys the W″ ownership correctly and
lands the landing criterion.

**The ownership correction (the whole point).**  The subject of W″ membership is NOT the resolved graph —
it is the **admissible forest `A` on the ambient resolved graph**.  The rigidified graph supplies four
*ambient* conditions (support, family-CD, `EdgeIdsUnique`, `LegIdsUnique`); a forest `A` on it lands in W″
iff those ambient conditions hold AND `A` is a proper, externally-leg-saturated forest.

## Contents

* private R1 — a clean `Fintype (ResolvedAdmissibleSubgraph G)` (`rfsFintype'` / `rasFintype'`),
  re-derived without the forbidden-class-polluted `resolvedAdmissibleSubgraphFintype`.
* private R2 — `resolvedAmbientSupported_ofFlatGraphWithUniqueIds'` from `Gf.WellFormed`.
* Step 1 `ResolvedAdmissibleSubgraphFor` — the forest ownership re-key.
* Step 2 `ResolvedFamilyAmbientEligible` — the four ambient gates as one bare predicate.
* Step 3 `resolvedLegSaturatedIndexFor` + `mem_resolvedLegSaturatedIndexFor` — the family-indexed W″
  finite index and its membership `iff`.
* Step 4 `phi4RigidifiedGraph_ambientEligible` — the chosen rigidification passes all four ambient gates.
* Step 5 `phi4WDoublePrimeIndex` + `mem_phi4WDoublePrimeIndex_rigidified(_of)` — the φ⁴ W″ index and the
  rigidified landing criterion (a forest `A` on `phi4RigidifiedGraph x` lands iff proper + leg-saturated).

## HALT compliance

The W″ subject is the forest `A`, never the graph; no `phi4RigidifiedGraph ∈ W″` statement.  ZERO forbidden
divergence classes (`IsPermInvariantDivergence` / `IsIsoInvariantDivergence` / `IsAmbientInvariantDivergence`
/ `IsDivergencePreservedByContract` / `...ByAdmissibleForestContract`) appear in ANY declaration's type; the
polluted fintype/carrier lemmas are re-derived, never consumed.  No `mapPerm` carrier equality, no canonical
star allocator / `hCD` / `rightTerm`, no closure bundle, no Measure / E / rep*, no coproduct / coassoc, no
rigidification naturality or reverse inverse.  Zero new `class` / `structure` / `instance`.  The only
divergence-flavored binder anywhere is the explicit `D : DivergenceMeasureFamily`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

/-! ## R1 — clean `Fintype (ResolvedAdmissibleSubgraph G)` (re-derived, forbidden-class-free) -/

/-- **body-586 (private R1)** — the finiteness floor for resolved subgraphs, mirroring
`resolvedFeynmanSubgraphFintype` but built with the CLEAN `ResolvedFeynmanSubgraph.ext` (the polluted
`resolvedFeynmanSubgraph_ext` carries forbidden classes and is unusable). -/
private noncomputable def rfsFintype' (G : ResolvedFeynmanGraph) :
    Fintype (ResolvedFeynmanSubgraph G) :=
  Fintype.ofInjective
    (fun γ : ResolvedFeynmanSubgraph G =>
      ((⟨γ.vertices, Finset.mem_powerset.mpr γ.vertices_subset⟩ :
          {vs // vs ∈ G.vertices.powerset}),
       (⟨γ.internalEdges,
          Multiset.mem_toFinset.mpr (Multiset.mem_powerset.mpr γ.internalEdges_le)⟩ :
          {es // es ∈ G.internalEdges.powerset.toFinset}),
       (⟨γ.externalLegs,
          Multiset.mem_toFinset.mpr (Multiset.mem_powerset.mpr γ.externalLegs_le)⟩ :
          {ls // ls ∈ G.externalLegs.powerset.toFinset})))
    (by
      intro γ δ h
      exact ResolvedFeynmanSubgraph.ext
        (congrArg (fun t => (Prod.fst t).val) h)
        (congrArg (fun t => (Prod.fst (Prod.snd t)).val) h)
        (congrArg (fun t => (Prod.snd (Prod.snd t)).val) h))

/-- **body-586 (private R1)** — the admissible-subgraph `Fintype`, family-indexed by an explicit
`D : DivergenceMeasureFamily` (inject by `.elements`).  Carries ONLY `DivergenceMeasureFamily`, no forbidden
class. -/
private noncomputable def rasFintype' (D : DivergenceMeasureFamily) (G : ResolvedFeynmanGraph) :
    Fintype (@ResolvedAdmissibleSubgraph D G) := by
  letI : (H : FeynmanGraph) → DivergenceMeasure H := D
  letI := rfsFintype' G
  exact Fintype.ofInjective (fun A : @ResolvedAdmissibleSubgraph D G => A.elements)
    (by intro A B h; cases A; cases B; cases h; rfl)

/-! ## R2 — clean ambient support of the unique-ID lift, from flat well-formedness -/

/-- **body-586 (private R2)** — the unique-ID resolved lift of a `WellFormed` flat graph is
ambient-supported.  Re-derived (the polluted `ambientSupported_of_ofFlatGraphWithUniqueIds` carries
forbidden classes). -/
private theorem resolvedAmbientSupported_ofFlatGraphWithUniqueIds' {Gf : FeynmanGraph}
    (hGf : Gf.WellFormed) : ResolvedAmbientSupported (ofFlatGraphWithUniqueIds Gf) := by
  refine ⟨?_, ?_⟩
  · intro e he
    have hef : e.forget ∈ Gf.internalEdges := by
      have hmem : e.forget ∈ (uniqueIdEdges Gf.internalEdges).map ResolvedFeynmanEdge.forget :=
        Multiset.mem_map_of_mem _ he
      rwa [map_forget_uniqueIdEdges] at hmem
    have hsupp := hGf.1 e.forget hef
    simp only [FeynmanEdge.SupportedOn] at hsupp
    exact ⟨hsupp.1, hsupp.2⟩
  · intro ℓ hℓ
    have hℓf : ℓ.forget ∈ Gf.externalLegs := by
      have hmem : ℓ.forget ∈ (uniqueIdLegs Gf.externalLegs).map ResolvedExternalLeg.forget :=
        Multiset.mem_map_of_mem _ hℓ
      rwa [map_forget_uniqueIdLegs] at hmem
    have hsupp := hGf.2 ℓ.forget hℓf
    simp only [ExternalLeg.SupportedOn] at hsupp
    exact hsupp

/-! ## Step 1 — resolved forest ownership re-key -/

/-- **body-586 — the W″ ownership subject.**  A family-indexed resolved admissible forest on the ambient
resolved graph `G` — the correct subject of W″ membership (NOT the resolved graph itself). -/
abbrev ResolvedAdmissibleSubgraphFor (D : DivergenceMeasureFamily) (G : ResolvedFeynmanGraph) : Type :=
  @ResolvedAdmissibleSubgraph D G

/-! ## Step 2 — family ambient gate (bare predicate) -/

/-- **body-586 — the four ambient gates of the rigidified graph.**  A resolved graph `G` is family-ambient
eligible to host W″ forests iff it is ambient-supported, family-connected-divergent, and has unique edge and
leg ids. -/
def ResolvedFamilyAmbientEligible (D : DivergenceMeasureFamily)
    (Inv : PermInvariantDivergenceMeasureFamily D) (G : ResolvedFeynmanGraph) : Prop :=
  ResolvedAmbientSupported G
    ∧ ResolvedFeynmanGraphClass.IsConnectedDivergentFor D Inv G.toResolvedClass
    ∧ G.EdgeIdsUnique
    ∧ G.LegIdsUnique

/-! ## Step 3 — family-indexed W″ finite index + membership iff -/

/-- **body-586 — the family-indexed W″ finite index.**  On an ambient-eligible `G`, the finite set of all
proper, externally-leg-saturated resolved forests on `G`; empty otherwise. -/
noncomputable def resolvedLegSaturatedIndexFor (D : DivergenceMeasureFamily)
    (Inv : PermInvariantDivergenceMeasureFamily D) (G : ResolvedFeynmanGraph) :
    Finset (ResolvedAdmissibleSubgraphFor D G) := by
  letI : (H : FeynmanGraph) → DivergenceMeasure H := D
  letI := rasFintype' D G
  exact
    if ResolvedFamilyAmbientEligible D Inv G then
      (Finset.univ.filter (fun A : ResolvedAdmissibleSubgraphFor D G =>
        A.IsProperForest ∧ ResolvedForestExternalLegSaturated A))
    else ∅

/-- **body-586 — W″ membership criterion.**  A resolved forest `A` on `G` lands in the family-indexed W″
index iff the four ambient gates hold AND `A` is a proper, externally-leg-saturated forest. -/
theorem mem_resolvedLegSaturatedIndexFor (D : DivergenceMeasureFamily)
    (Inv : PermInvariantDivergenceMeasureFamily D) (G : ResolvedFeynmanGraph)
    (A : ResolvedAdmissibleSubgraphFor D G) :
    A ∈ resolvedLegSaturatedIndexFor D Inv G ↔
      ResolvedAmbientSupported G
        ∧ ResolvedFeynmanGraphClass.IsConnectedDivergentFor D Inv G.toResolvedClass
        ∧ G.EdgeIdsUnique ∧ G.LegIdsUnique
        ∧ A.IsProperForest ∧ ResolvedForestExternalLegSaturated A := by
  letI : (H : FeynmanGraph) → DivergenceMeasure H := D
  letI := rasFintype' D G
  unfold resolvedLegSaturatedIndexFor
  by_cases hE : ResolvedFamilyAmbientEligible D Inv G
  · rw [if_pos hE, Finset.mem_filter]
    obtain ⟨h1, h2, h3, h4⟩ := hE
    constructor
    · rintro ⟨_, hp, hs⟩; exact ⟨h1, h2, h3, h4, hp, hs⟩
    · rintro ⟨_, _, _, _, hp, hs⟩; exact ⟨Finset.mem_univ _, hp, hs⟩
  · rw [if_neg hE]
    simp only [Finset.notMem_empty, false_iff]
    rintro ⟨h1, h2, h3, h4, _, _⟩
    exact hE ⟨h1, h2, h3, h4⟩

/-! ## Step 4 — chosen rigidification's ambient gate -/

/-- **body-586 — the chosen rigidification passes all four ambient gates.**  `phi4RigidifiedGraph x` is
ambient-supported (from the `WellFormed` witness inside its family-CD property), family-connected-divergent,
and has unique edge/leg ids. -/
theorem phi4RigidifiedGraph_ambientEligible (x : Phi4HopfGen) :
    ResolvedFamilyAmbientEligible phi4DivergenceMeasureFamily phi4PermInvariantDivergenceMeasureFamily
      (phi4RigidifiedGraph x) := by
  have hcd : ResolvedFeynmanGraphClass.IsConnectedDivergentFor
      phi4DivergenceMeasureFamily phi4PermInvariantDivergenceMeasureFamily
      (phi4RigidifiedGraph x).toResolvedClass := by
    have h := (rigidifyPhi4Gen x).property
    rwa [rigidifyPhi4Gen_val] at h
  have hwf : (Quotient.out x.val).WellFormed := by
    have he := (ResolvedFeynmanGraphClass.isConnectedDivergentFor_toResolvedClass
      phi4DivergenceMeasureFamily phi4PermInvariantDivergenceMeasureFamily
      (phi4RigidifiedGraph x)).mp hcd
    have hfe : (phi4RigidifiedGraph x).forget = Quotient.out x.val := by
      unfold phi4RigidifiedGraph
      exact forget_ofFlatGraphWithUniqueIds _
    exact hfe ▸ he.choose
  refine ⟨?_, hcd, phi4RigidifiedGraph_edgeIdsUnique x, phi4RigidifiedGraph_legIdsUnique x⟩
  unfold phi4RigidifiedGraph
  exact resolvedAmbientSupported_ofFlatGraphWithUniqueIds' hwf

/-! ## Step 5 — φ⁴ W″ index + rigidified landing criterion -/

/-- **body-586 — the φ⁴ W″ finite index** (family-indexed index specialized to the φ⁴ family). -/
noncomputable def phi4WDoublePrimeIndex (G : ResolvedFeynmanGraph) :
    Finset (ResolvedAdmissibleSubgraphFor phi4DivergenceMeasureFamily G) :=
  resolvedLegSaturatedIndexFor phi4DivergenceMeasureFamily phi4PermInvariantDivergenceMeasureFamily G

/-- **body-586 (TARGET) — the rigidified landing criterion.**  A resolved forest `A` on the chosen
rigidification `phi4RigidifiedGraph x` lands in the φ⁴ W″ index iff it is a proper, externally-leg-saturated
forest — the four ambient gates are automatic from `phi4RigidifiedGraph_ambientEligible`. -/
theorem mem_phi4WDoublePrimeIndex_rigidified (x : Phi4HopfGen)
    (A : ResolvedAdmissibleSubgraphFor phi4DivergenceMeasureFamily (phi4RigidifiedGraph x)) :
    A ∈ phi4WDoublePrimeIndex (phi4RigidifiedGraph x) ↔
      @ResolvedAdmissibleSubgraph.IsProperForest phi4DivergenceMeasureFamily (phi4RigidifiedGraph x) A
        ∧ @ResolvedForestExternalLegSaturated phi4DivergenceMeasureFamily (phi4RigidifiedGraph x) A := by
  unfold phi4WDoublePrimeIndex
  rw [mem_resolvedLegSaturatedIndexFor]
  obtain ⟨h1, h2, h3, h4⟩ := phi4RigidifiedGraph_ambientEligible x
  constructor
  · rintro ⟨_, _, _, _, hp, hs⟩; exact ⟨hp, hs⟩
  · rintro ⟨hp, hs⟩; exact ⟨h1, h2, h3, h4, hp, hs⟩

/-- **body-586 — rigidified landing (constructor direction).**  A proper, externally-leg-saturated resolved
forest on `phi4RigidifiedGraph x` lands in the φ⁴ W″ index. -/
theorem mem_phi4WDoublePrimeIndex_rigidified_of (x : Phi4HopfGen)
    (A : ResolvedAdmissibleSubgraphFor phi4DivergenceMeasureFamily (phi4RigidifiedGraph x))
    (hp : @ResolvedAdmissibleSubgraph.IsProperForest phi4DivergenceMeasureFamily (phi4RigidifiedGraph x) A)
    (hs : @ResolvedForestExternalLegSaturated phi4DivergenceMeasureFamily (phi4RigidifiedGraph x) A) :
    A ∈ phi4WDoublePrimeIndex (phi4RigidifiedGraph x) :=
  (mem_phi4WDoublePrimeIndex_rigidified x A).mpr ⟨hp, hs⟩

end GaugeGeometry.QFT.Combinatorial
