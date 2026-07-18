import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocMultiStarValueCore

/-!
# R-6c-body-397 — ambient-support scope-repair audit: `Core.hE/hL` are over-typed (verdict + discharge interface)

Three-hundred-and-ninety-seventh genuine-body step — the scope-repair audit that catches an over-typing defect BEFORE
the body-397 carrier-closure assembly.  The value core's endpoint-support fields are currently

```lean
hE : ∀ (G : ResolvedFeynmanGraph), ∀ e ∈ G.internalEdges, e.source ∈ G.vertices ∧ e.target ∈ G.vertices
hL : ∀ (G : ResolvedFeynmanGraph), ∀ ℓ ∈ G.externalLegs, ℓ.attachedTo ∈ G.vertices
```

i.e. a UNIVERSAL claim over ALL `ResolvedFeynmanGraph`.  But `ResolvedHopfCoproductCoassocRemnantSupport.lean:7-9`
states it verbatim: **a `ResolvedFeynmanGraph` carries NO endpoint well-formedness invariant by type — an arbitrary
resolved graph may have an edge with endpoints outside its vertex set**.  So `∀ G, AmbientEdgesSupported G` is FALSE and
CANNOT be canonically inhabited; `canonicalPayload_edges_supported` / `legs_supported` prove it only for the specific
canonical payload graph, not for a universally quantified `G`.  This is a floor-297-isomorphic "plausible-looking global
field": body-395's "`hE`/`hL` EXISTING" verdict is CORRECTED — they are NOT existing; they are an over-typed interface
that must be repaired before `Core` can be inhabited.

## Where `hE`/`hL` are actually used — the faithful scope

`Core.hE G` / `Core.hL G` feed exactly `localizedParentWithTouchedLegs z δ.1 (legLift z δ) (hE G) (hL G)` — where a
LIVE codomain `z : ForestBlockCodType D G` exists, so `z.1.1 ∈ D.carrier G` (`z.1.2`).  Support is only ever needed on a
`G` that hosts a carrier member; the `∀ G` is strictly stronger than the usage.

## The selected repair — live-`z` retyping, discharged from carrier membership

Retype the value-core fields (a follow-up interface edit) to the live-`z` scope

```lean
hE : ∀ {G} (z : ForestBlockCodType D G), ∀ e ∈ G.internalEdges, e.source ∈ G.vertices ∧ e.target ∈ G.vertices
hL : ∀ {G} (z : ForestBlockCodType D G), ∀ ℓ ∈ G.externalLegs, ℓ.attachedTo ∈ G.vertices
```

and discharge the canonical `D` via `ResolvedCarrierAmbientSupportSupply` (support required ONLY for a `G` hosting a
carrier member), through `z.1.2`.  Banked here (feasibility, PROVED): `liveAmbient_edges_supported` /
`liveAmbient_legs_supported` — the live-`z` support IS derivable from the ambient-support gate.

Per the HALT: this is the scope-repair verdict + the discharge interface + its feasibility ONLY; `Core`'s fields are NOT
retyped here (that edits bodies 374-396 and is the follow-up); the `Closure` / `rrm` carrier-closure assembly is NOT
done; body-394 stays a VALID conditional theorem (its `Core` hypothesis is simply not yet inhabitable — the conditional
is sound, the UNCONDITIONAL path needs this repair).  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO
`promote_collapse` / singleton / floor-297.
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

/-- **R-6c-body-397 — ambient edge well-formedness** (the honest scope, as a predicate on ONE graph). -/
def AmbientEdgesSupported (G : ResolvedFeynmanGraph) : Prop :=
  ∀ e ∈ G.internalEdges, e.source ∈ G.vertices ∧ e.target ∈ G.vertices

/-- **R-6c-body-397 — ambient leg well-formedness** (the honest scope, as a predicate on ONE graph). -/
def AmbientLegsSupported (G : ResolvedFeynmanGraph) : Prop :=
  ∀ ℓ ∈ G.externalLegs, ℓ.attachedTo ∈ G.vertices

/-- **R-6c-body-397 — the carrier-ambient support gate.**  Endpoint well-formedness required ONLY for the graphs that
host a carrier member — the honest replacement for the over-typed `∀ G` claim (NOT canonically inhabitable). -/
structure ResolvedCarrierAmbientSupportSupply (D : ResolvedCoproductProperForestData) where
  /-- A graph hosting a carrier member is edge-well-formed. -/
  edges_supported_of_mem : ∀ {G : ResolvedFeynmanGraph} {A : ResolvedAdmissibleSubgraph G},
    A ∈ D.carrier G → AmbientEdgesSupported G
  /-- A graph hosting a carrier member is leg-well-formed. -/
  legs_supported_of_mem : ∀ {G : ResolvedFeynmanGraph} {A : ResolvedAdmissibleSubgraph G},
    A ∈ D.carrier G → AmbientLegsSupported G

/-- **R-6c-body-397 — feasibility (edges): the live-`z` edge support is derivable from the ambient-support gate**
through `z.1.2`.  Shows the retyped `Core.hE` is dischargeable — the `∀ G` was strictly over-typed. -/
theorem liveAmbient_edges_supported (Amb : ResolvedCarrierAmbientSupportSupply D)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) :
    ∀ e ∈ G.internalEdges, e.source ∈ G.vertices ∧ e.target ∈ G.vertices :=
  Amb.edges_supported_of_mem z.1.2

/-- **R-6c-body-397 — feasibility (legs): the live-`z` leg support is derivable from the ambient-support gate**
through `z.1.2`. -/
theorem liveAmbient_legs_supported (Amb : ResolvedCarrierAmbientSupportSupply D)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) :
    ∀ ℓ ∈ G.externalLegs, ℓ.attachedTo ∈ G.vertices :=
  Amb.legs_supported_of_mem z.1.2

end GaugeGeometry.QFT.Combinatorial
