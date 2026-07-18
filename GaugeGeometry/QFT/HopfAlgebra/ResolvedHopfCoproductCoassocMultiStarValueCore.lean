import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocMultiStarDecontraction

/-!
# R-6c-body-374 — Front-3 ownership audit: the value core is `innerRaw_mem`-free (PROVED)

Three-hundred-and-seventy-fourth genuine-body step — the dependency audit before inhabiting Front-3.  Body-252's
lesson: never let VALUE and carrier-MEMBERSHIP ride the same socket, or the ordering (inhabit value, then carrier)
stops being realisable.  `ResolvedMultiStarDecontractionSupply` currently bundles both.

**Audit verdict.**  The de-contraction VALUE geometry reads only `hE` / `hL` / `legLift` / `parentCD`; the carrier
membership `innerRaw_mem` is read by NOTHING but `innerIdx` (the `ForestIdx` wrapper) and `forestTag` downstream:

| gate | reads `innerRaw_mem`? |
|---|---|
| `parent` (`= localizedParentWithTouchedLegs … legLift … hE … hL`) | NO |
| `innerRaw` (raw, `= innerRaw … legLift … hE … hL`) | NO |
| `parentCD` (M2b) | NO |
| `innerIdx : ForestIdx` (`= ⟨innerRaw …, innerRaw_mem⟩`) | YES |
| `forestTag` (via `innerIdx`) | YES (transitively) |

So the value core `{hE, hL, legLift, parentCD}` is a genuine `innerRaw_mem`-free reduct: `parent` and `innerRaw`
are defined on it, and `M.parent = M.toValueCore.parent` / `(M.innerIdx …).1 = M.toValueCore.innerRaw …` by `rfl`.
The `bank-3 → bank-4` order (inhabit value, then lift `innerRaw` into `D.carrier`) is therefore realisable.

Landed axiom-clean: `ResolvedMultiStarDecontractionValueCoreSupply`, `toValueCore`, `toValueCore_parent`,
`toValueCore_innerRaw`.

Per the HALT: only the ownership audit + the value-core extraction is done; no gate is inhabited yet; the carrier
lift (`innerRaw_mem`), `innerStar_agrees` (raw), and occurrence inversion (raw) stay for bank-3/4.  No facade, no flat
term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
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

/-- **R-6c-body-374 — the `innerRaw_mem`-free value core** of the multi-star de-contraction supply. -/
structure ResolvedMultiStarDecontractionValueCoreSupply (D : ResolvedCoproductProperForestData) where
  /-- Payload edge-support. -/
  hE : ∀ (G : ResolvedFeynmanGraph), ∀ e ∈ G.internalEdges, e.source ∈ G.vertices ∧ e.target ∈ G.vertices
  /-- Payload leg-support. -/
  hL : ∀ (G : ResolvedFeynmanGraph), ∀ ℓ ∈ G.externalLegs, ℓ.attachedTo ∈ G.vertices
  /-- The touched-leg-lift datum for each star-touching quotient component. -/
  legLift : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) // x ∈ forestDomain z}),
    ResolvedTouchedLegLiftDatum z δ.1
  /-- The de-contracted parent is connected-divergent (M2b). -/
  parentCD : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) // x ∈ forestDomain z}),
    (localizedParentWithTouchedLegs z δ.1 (legLift z δ) (hE G) (hL G)).forget.IsConnectedDivergent

namespace ResolvedMultiStarDecontractionValueCoreSupply

variable (Mv : ResolvedMultiStarDecontractionValueCoreSupply D) {G : ResolvedFeynmanGraph}

/-- **R-6c-body-374 — the de-contracted parent, on the value core** (`innerRaw_mem`-free). -/
noncomputable def parent (z : ForestBlockCodType D G)
    (δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) // x ∈ forestDomain z}) :
    ResolvedFeynmanSubgraph G :=
  localizedParentWithTouchedLegs z δ.1 (Mv.legLift z δ) (Mv.hE G) (Mv.hL G)

/-- **R-6c-body-374 — the raw inner forest, on the value core** (`innerRaw_mem`-free). -/
noncomputable def innerRaw (z : ForestBlockCodType D G)
    (δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) // x ∈ forestDomain z}) :
    ResolvedAdmissibleSubgraph (Mv.parent z δ).toResolvedFeynmanGraph :=
  GaugeGeometry.QFT.Combinatorial.innerRaw z δ.1 (Mv.legLift z δ) (Mv.hE G) (Mv.hL G)

end ResolvedMultiStarDecontractionValueCoreSupply

namespace ResolvedMultiStarDecontractionSupply

variable (M : ResolvedMultiStarDecontractionSupply D) {G : ResolvedFeynmanGraph}

/-- **R-6c-body-374 — forget the carrier membership**, keeping the value core. -/
def toValueCore : ResolvedMultiStarDecontractionValueCoreSupply D where
  hE := M.hE
  hL := M.hL
  legLift := M.legLift
  parentCD := M.parentCD

/-- **R-6c-body-374 — `parent` factors through the value core** (`rfl`). -/
theorem toValueCore_parent (z : ForestBlockCodType D G)
    (δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) // x ∈ forestDomain z}) :
    M.parent z δ = M.toValueCore.parent z δ :=
  rfl

/-- **R-6c-body-374 — the raw inner forest factors through the value core** (`rfl`). -/
theorem toValueCore_innerRaw (z : ForestBlockCodType D G)
    (δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) // x ∈ forestDomain z}) :
    (M.innerIdx z δ).1 = M.toValueCore.innerRaw z δ :=
  rfl

end ResolvedMultiStarDecontractionSupply

end GaugeGeometry.QFT.Combinatorial
