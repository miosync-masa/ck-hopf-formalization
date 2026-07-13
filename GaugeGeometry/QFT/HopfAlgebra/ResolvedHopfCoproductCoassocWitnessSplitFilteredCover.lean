import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocFwdMapFiltered

/-!
# R-6c-body-250 — the filtered witnessSplit cover: round-trip laws on the filtered domain (PROVED via legacy bridge)

Two-hundred-and-fiftieth genuine-body step — the filtered-domain forward/backward round-trip laws for the migration
(body-248 verdict (3)).  The **canonical** record `ResolvedWitnessSplitFilteredCoverSupply` states the round-trips
against `fwdMapFiltered` (body-249), so its statements never mention the retired total root.  A `.ofLegacy` builder
discharges them from the existing total `ResolvedWitnessSplitConcreteData` via the `rfl` bridge
`fwdMapFiltered_eq_legacy` — a **migration-check**, honestly carrying the legacy dependency it retires.

## The canonical record (statements total-root-free)

```lean
structure ResolvedWitnessSplitFilteredCoverSupply (F) (S) where
  witnessSplit      : ForestBlockCodType D G → ForestBlockDomType D G
  witnessSplit_mem  : ∀ z, z ∈ forestBlockCodFinset G → witnessSplit z ∈ forestBlockDomFinset G
  forward_witness   : ∀ z hz, fwdMapFiltered F S ⟨witnessSplit z, witnessSplit_mem z hz⟩ = z
  backward_witness  : ∀ (q : FilteredForestBlockDom D G), witnessSplit (fwdMapFiltered F S q) = q.1
```

Its `forward_witness` / `backward_witness` are phrased with `fwdMapFiltered`; the `.1.2` carrier tag there is the
honest filtered membership (body-245), not `S.Forward.selectedOuter_mem`.

## The `.ofLegacy` builder (migration-check, legacy dependency named)

`ofLegacy` builds the record from the total `W : ResolvedWitnessSplitConcreteData D S` and a supplied
`witnessSplit_mem`, discharging each round-trip by `rw [fwdMapFiltered_eq_legacy]` (rfl) then the total law
(`W.forward_witness` / `W.backward_witness`, `WitnessSplitConcrete.lean:117/130`).  This *confirms* the filtered laws
are attainable; it is not the final canonical construction.

## Audit — what is total-root-free and what is the residual boundary

* **`witnessSplit_mem` is total-root-free**: the discharge machinery (`mixed/forest_invFun_mem_of_tag`,
  `OuterMixingInvMem.lean:65-79`, fed by `forestChoiceCarrier` membership `RecoveredChoiceMembership.lean:94-108`)
  depends only on `q.2 ∈ forestChoiceCarrier q.1` and the reconstruction / non-extremality tags — **not** on the total
  `selectedOuter_mem` (`ForwardMapCoherence.lean:72`) and **not** on `recovered_outer_mem` (body-159).  So this field
  can be supplied canonically (a later body instantiates it from that machinery).
* **The round-trip laws still carry the legacy boundary**: the total branch specs
  `ResolvedWitnessSplitConcreteData.mixed/forest_forward/backward` (`WitnessSplitConcrete.lean:94-105`) are typed
  against `fwdMap S`, i.e. through `ResolvedConcreteSummandBundleSupply.Forward :
  ResolvedForwardMapCoherenceSupply` whose `selectedOuter_mem` is the retired total leaf.  So `.ofLegacy` carries `W`
  (→ `S.Forward`).  **Migration boundary**: `ResolvedConcreteSummandBundleSupply.Forward` / the four branch specs of
  `ResolvedWitnessSplitConcreteData` — a full canonical discharge restates those specs against `fwdMapFiltered`
  (a follow-up body).

Per the HALT: the canonical filtered record is defined (statements total-root-free); the round-trips are proved only
via the legacy bridge (migration-check), with the residual legacy boundary named.  No branch spec is restated, no
provider field is changed.  No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData}

set_option linter.unusedSectionVars false

/-- **R-6c-body-250 — the filtered witnessSplit cover.**  Forward/backward round-trips phrased against `fwdMapFiltered`
(honest filtered carrier tag), so the statements never mention the retired total root. -/
structure ResolvedWitnessSplitFilteredCoverSupply (F : ResolvedSelectedOuterFilteredMemSupply D)
    (S : ResolvedConcreteSummandBundleSupply D) where
  /-- The backward map (star-touch classifier split), total on the codomain. -/
  witnessSplit : ∀ {G : ResolvedFeynmanGraph}, ForestBlockCodType D G → ForestBlockDomType D G
  /-- The backward map lands in the filtered domain (total-root-free: from `forestChoiceCarrier` membership). -/
  witnessSplit_mem : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    z ∈ forestBlockCodFinset G → witnessSplit z ∈ forestBlockDomFinset G
  /-- Forward round-trip on the filtered domain. -/
  forward_witness : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (hz : z ∈ forestBlockCodFinset G),
    fwdMapFiltered F S ⟨witnessSplit z, witnessSplit_mem z hz⟩ = z
  /-- Backward round-trip on the filtered domain. -/
  backward_witness : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G),
    witnessSplit (fwdMapFiltered F S q) = q.1

/-- **R-6c-body-250 — the filtered cover from the legacy total data** (migration-check).  Discharges the round-trips
via the `rfl` bridge `fwdMapFiltered_eq_legacy` + the total round-trips.  Carries the legacy `W` (→ `S.Forward`), the
named migration boundary. -/
noncomputable def ResolvedWitnessSplitFilteredCoverSupply.ofLegacy
    (F : ResolvedSelectedOuterFilteredMemSupply D) {S : ResolvedConcreteSummandBundleSupply D}
    (W : ResolvedWitnessSplitConcreteData D S)
    (wmem : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
      z ∈ forestBlockCodFinset G → W.witnessSplit z ∈ forestBlockDomFinset G) :
    ResolvedWitnessSplitFilteredCoverSupply F S where
  witnessSplit := W.witnessSplit
  witnessSplit_mem := wmem
  forward_witness := fun z hz => by
    rw [fwdMapFiltered_eq_legacy]
    exact W.forward_witness z
  backward_witness := fun q => by
    rw [fwdMapFiltered_eq_legacy]
    exact W.backward_witness q.1

end GaugeGeometry.QFT.Combinatorial
