import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCorrectingPermContract
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightTermCorrectingPerm

/-!
# R-6c-body-411 — the correcting-permutation supply from fresh/ambient facts (PROVED, pure assembly)

Four-hundred-and-eleventh genuine-body step — the pure assembly that turns body-410's graph equality into body-406's
class-level socket.  Given the canonical star facts `Fstar` (freshness + injectivity) and the carrier-ambient support gate
`Ambient`, every `(G, σ, A)` with `A ∈ D.carrier G` gets a `ResolvedContractTwiceClassData` with `starPerm = τ :=
correctingPerm Fstar.toRaw σ A` and the three field equalities read off `correctingPerm_contractWithStars` by `congrArg`.

* `correctingPermSupplyOfFacts` — inhabits `ResolvedRightTermCorrectingPermSupply D` from `Ambient` + `Fstar`;
* `rightTermAlphaOfFacts` — the body-404 alpha law issued from it;
* `rightTerm_mapPerm_of_fresh_correcting` — the named right-term equality (the whole point, as a theorem).

**Ownership guard (why this body stops here).**  Both `Ambient : ResolvedCarrierAmbientSupportSupply D` and `Fstar :
ResolvedCanonicalStarFacts D` take an ALREADY-COMPLETED `D` — and that `D` itself carries the `rightTerm_mapPerm` field.
So plugging this straight into the `W` constructor would be a definitional cycle.  This body proves only "on an existing
`D`, the law is DERIVED"; it does NOT build `W.rightTerm_mapPerm`.  The ownership repair — cutting a rightTerm-free raw
carrier/star core and lowering the 407–411 consumption onto it — is body-412.

Per the HALT: `W` is NOT inhabited; `D.rightTerm_mapPerm` is NOT plugged; no raw-core migration here.  No facade, no flat
term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

variable {D : ResolvedCoproductProperForestData}

set_option linter.unusedSectionVars false

/-- **R-6c-body-411 — the correcting-permutation class socket from fresh/ambient facts.**  For each carrier-hosted
`(G, σ, A)`, the two-stage class datum with `starPerm = correctingPerm Fstar.toRaw σ A` and the three field equalities from
`correctingPerm_contractWithStars` (endpoint support supplied by `Ambient` off `A ∈ D.carrier G`).  `hAσ` is required by
the field TYPE, not by the geometry. -/
noncomputable def correctingPermSupplyOfFacts
    (Ambient : ResolvedCarrierAmbientSupportSupply D)
    (Fstar : ResolvedCanonicalStarFacts D) :
    ResolvedRightTermCorrectingPermSupply D where
  classData := fun G σ A hA _hAσ =>
    have hgraph :
        (A.mapPerm σ).contractWithStars (D.starOf (G.mapPerm σ) (A.mapPerm σ))
          = (A.contractWithStars (D.starOf G A)).mapPerm (correctingPerm Fstar.toRaw σ A) :=
      correctingPerm_contractWithStars Fstar.toRaw σ A
        (Ambient.edges_supported_of_mem hA) (Ambient.legs_supported_of_mem hA)
    { starPerm := correctingPerm Fstar.toRaw σ A
      vertices_eq := congrArg (fun H : ResolvedFeynmanGraph => H.vertices) hgraph
      internalEdges_eq := congrArg (fun H : ResolvedFeynmanGraph => H.internalEdges) hgraph
      externalLegs_eq := congrArg (fun H : ResolvedFeynmanGraph => H.externalLegs) hgraph }

/-- **R-6c-body-411 — the body-404 alpha law issued from the fresh/ambient correcting-permutation supply.** -/
noncomputable def rightTermAlphaOfFacts
    (Ambient : ResolvedCarrierAmbientSupportSupply D)
    (Fstar : ResolvedCanonicalStarFacts D) : ResolvedRightTermAlphaSupply D :=
  (correctingPermSupplyOfFacts Ambient Fstar).toRightTermAlphaSupply

/-- **R-6c-body-411 — the right-term equality from freshness + ambient support** (the whole point, as a named theorem).
The right-term of the relabeled forest equals that of the original — via the correcting permutation `τ`, NOT strict
star-equivariance (which body-403 refuted). -/
theorem rightTerm_mapPerm_of_fresh_correcting
    (Ambient : ResolvedCarrierAmbientSupportSupply D)
    (Fstar : ResolvedCanonicalStarFacts D)
    (G : ResolvedFeynmanGraph) (σ : Equiv.Perm VertexId) (A : ResolvedAdmissibleSubgraph G)
    (hA : A ∈ D.carrier G) (hAσ : A.mapPerm σ ∈ D.carrier (G.mapPerm σ)) :
    resolvedForestRightTerm A (D.starOf G A) (D.hCD G A hA)
      = resolvedForestRightTerm (A.mapPerm σ) (D.starOf (G.mapPerm σ) (A.mapPerm σ))
          (D.hCD (G.mapPerm σ) (A.mapPerm σ) hAσ) :=
  rightTerm_mapPerm_of_correctingPerm (correctingPermSupplyOfFacts Ambient Fstar) G σ A hA hAσ

end GaugeGeometry.QFT.Combinatorial
