import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocMultiStarValueCore

/-!
# R-6c-body-377 — bank-4a: the inner-raw carrier closure, isolated from the value core (PROVED)

Three-hundred-and-seventy-seventh genuine-body step — the carrier socket, kept STRICTLY separate from the value core
(body-252/374 lesson: `A.IsProperForest` does NOT give `A ∈ D.carrier G`, because `D.carrier` is a supplied FINITE
payload).  The inner raw's mathematical VALUE (its properness) is a theorem (body-378); its membership in the supplied
carrier is an honest closure field, never derived from properness.

* `ResolvedMultiStarInnerRawCarrierClosureSupply Core` — the single field `innerRaw_mem`, over a value core (body-374);
* `ResolvedMultiStarDecontractionValueCoreSupply.toDecontractionSupply` — value core + closure ⟶ full
  `ResolvedMultiStarDecontractionSupply`, field-by-field `rfl` (the converter completes the `bank-3a → bank-4a` order).

Landed axiom-clean.

Per the HALT: only the carrier-closure interface + the converter are built; properness is NOT used to derive membership;
no `P.carrier_isProperForest` inverse, no `Finset.univ`, no forget-section, no subtype-`.2` bypass; the converter is
field-by-field `rfl`.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton /
floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

variable {D : ResolvedCoproductProperForestData}

set_option linter.unusedSectionVars false

/-- **R-6c-body-377 — the inner-raw carrier-closure supply** over a value core.  The ONLY carrier-dependent gate:
the (mathematically proper) inner raw is a member of the supplied finite carrier of its parent. -/
structure ResolvedMultiStarInnerRawCarrierClosureSupply
    (Core : ResolvedMultiStarDecontractionValueCoreSupply D) where
  /-- The inner forest is a carrier member of the parent's graph. -/
  innerRaw_mem : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) // x ∈ forestDomain z}),
    Core.innerRaw z δ ∈ D.carrier (Core.parent z δ).toResolvedFeynmanGraph

/-- **R-6c-body-377 — value core + carrier closure ⟶ the full de-contraction supply** (field-by-field `rfl`). -/
noncomputable def ResolvedMultiStarDecontractionValueCoreSupply.toDecontractionSupply
    (Core : ResolvedMultiStarDecontractionValueCoreSupply D)
    (Closure : ResolvedMultiStarInnerRawCarrierClosureSupply Core) :
    ResolvedMultiStarDecontractionSupply D where
  hE := Core.hE
  hL := Core.hL
  legLift := Core.legLift
  parentCD := Core.parentCD
  innerRaw_mem := Closure.innerRaw_mem

end GaugeGeometry.QFT.Combinatorial
