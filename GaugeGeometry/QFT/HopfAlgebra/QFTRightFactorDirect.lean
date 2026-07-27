import GaugeGeometry.QFT.HopfAlgebra.QFTContractDivergenceScope
import GaugeGeometry.QFT.Combinatorial.Phi4DivergenceMeasure

/-!
# QFT-R1-body-563 — direct quotient `HopfGen` entrance without ambient invariance

The SHALLOW right factor, closed.  Body-560 built a faithful quotient right factor
`contractToHopfGen_of_isDivergent`, but it routed through `FeynmanSubgraph.toHopfGen`, whose
subgraph→graph lift `toFeynmanGraph_isConnectedDivergent` consumes `IsAmbientInvariantDivergence` — and
body-562 refuted that class for boundaryful subgraphs under the correct φ⁴ measure.

The fix is purely an ownership one.  The quotient `γ.contract` is *already a full graph*, and graph-level
`FeynmanGraph.IsConnectedDivergent` is **defined** as
`∃ hWF, (FeynmanSubgraph.self γ.contract hWF).IsConnectedDivergent`.  Body-560 Step 1 already produces
exactly that self-subgraph witness from the explicit quotient-divergence leaf `hQDiv`, in the *same*
ambient `γ.contract` — so no ambient change occurs, and the graph→class lift
`FeynmanGraphClass.isConnectedDivergent_toClass` needs only `DivergenceMeasure` + `IsPermInvariantDivergence`
(it `omit`s iso, and never mentions ambient invariance).  Threading through the graph level instead of the
subgraph level removes `IsAmbientInvariantDivergence` from the right factor entirely.

## Contents

* Step 1 `FeynmanGraph.toHopfGenDirect` — graph-level CD ⟹ `HopfGen`, via `isConnectedDivergent_toClass`
  (no ambient invariance).
* Step 2 `contract_graph_isConnectedDivergent_of_isDivergent` — assemble `γ.contract.IsConnectedDivergent`
  from body-560 Step 1's self-subgraph CD (no new topology).
* Step 3 `contractToHopfGenDirect_of_isDivergent` — the direct right factor; does not touch `toHopfGen`.
* Step 4 value anchor (`= γ.contract.toClass`, `rfl`) — the downstream-replacement hook.
* Step 5 `contractToHopfGenDirect_eq_body560` — equals body-560's constructor when
  `IsAmbientInvariantDivergence` is present (the ONLY place that class appears).
* Step 6 (docstring) φ⁴ wiring boundary + residual ledger.

## φ⁴ wiring boundary (Step 6)

Body-562's `phi4_contract_self_isDivergent_of_ambient` has exactly the logical type of the `hQDiv`
argument here — full-ambient φ⁴-divergence ⟹ full-quotient φ⁴-divergence.  But no concrete φ⁴ `HopfGen`
theorem is issued yet: `HopfGen` itself (via the class quotient) needs the rename/iso invariance
realized concretely, which is not yet built.  Exact residual:

```text
quotient divergence leaf         DERIVED (562)
right-factor graph constructor   DERIVED (563)  — ambient invariance on the right: GONE
φ⁴ right-factor specialization   waits only for Perm/Iso realization
left factor                      boundary completion OPEN
```

Per the HALT: body-560/562 are not edited; ZERO new `class`/`structure`/`instance`; no φ⁴ measure is
instantiated; `IsAmbientInvariantDivergence` is kept out of the main path (only the Step 5 compatibility
theorem may name it); `IsDivergencePreservedByContract` is unused; the left factor / boundary completion
is not entered; no coproduct summand / coassociativity / final theorem is edited; no topology is re-proved;
the main direct constructor never uses `γ.toFeynmanGraph`.
-/

namespace GaugeGeometry.QFT.Combinatorial

set_option linter.unusedSectionVars false

-- Minimal blanket binders: the graph→class lift needs `DivergenceMeasure` + `IsPermInvariantDivergence`;
-- body-560 Step 1 additionally carries `IsIsoInvariantDivergence` in its (auto-included) signature.
-- `IsAmbientInvariantDivergence` is deliberately ABSENT.
variable [∀ H : FeynmanGraph, DivergenceMeasure H]
variable [∀ H : FeynmanGraph, IsPermInvariantDivergence H]
variable [∀ H : FeynmanGraph, IsIsoInvariantDivergence H]

/-! ## Step 1 — graph-level direct `HopfGen` constructor -/

/-- **R-6c-QFT-R1-body-563 — direct graph-level generator.**  A connected-divergent *graph* is a
`HopfGen` via the class lift `isConnectedDivergent_toClass`.  Unlike `FeynmanSubgraph.toHopfGen`, this
does not route through the subgraph→intrinsic-graph lift and hence consumes **no**
`IsAmbientInvariantDivergence`. -/
def FeynmanGraph.toHopfGenDirect (G : FeynmanGraph) (hGCD : G.IsConnectedDivergent) : HopfGen :=
  ⟨G.toClass, (FeynmanGraphClass.isConnectedDivergent_toClass G).mpr hGCD⟩

@[simp] theorem FeynmanGraph.toHopfGenDirect_val (G : FeynmanGraph) (hGCD : G.IsConnectedDivergent) :
    (G.toHopfGenDirect hGCD).val = G.toClass := rfl

variable {G : FeynmanGraph}

/-! ## Step 2 — quotient graph-level CD assembly -/

/-- **R-6c-QFT-R1-body-563 — graph-level quotient CD.**  `γ.contract.IsConnectedDivergent`, assembled
directly from body-560 Step 1's self-subgraph CD (`WellFormed := wellFormed_contract`, the
connected/1PI/divergent triple from the topological preservation lemmas + `hQDiv`).  No ambient
invariance, no new topology. -/
theorem FeynmanSubgraph.contract_graph_isConnectedDivergent_of_isDivergent
    (hGWF : G.WellFormed) (hG1PI : G.IsOnePI) {γ : FeynmanSubgraph G}
    (hγ1PI : γ.IsOnePI) (hγNe : γ.IsNonempty)
    (hQDiv : (FeynmanSubgraph.self γ.contract
      (FeynmanSubgraph.wellFormed_contract hGWF)).IsDivergent) :
    γ.contract.IsConnectedDivergent :=
  ⟨FeynmanSubgraph.wellFormed_contract hGWF,
    FeynmanSubgraph.contract_isConnectedDivergent_of_isDivergent hGWF hG1PI hγ1PI hγNe hQDiv⟩

/-! ## Step 3 — direct quotient right factor -/

/-- **R-6c-QFT-R1-body-563 — direct quotient right factor `[Γ/γ]`.**  Builds the `HopfGen` right factor
from the explicit quotient-divergence leaf `hQDiv` through the graph level, so it consumes **no**
`IsAmbientInvariantDivergence` (contrast body-560's `contractToHopfGen_of_isDivergent`, which does via
`toHopfGen`). -/
def FeynmanSubgraph.contractToHopfGenDirect_of_isDivergent
    (hGWF : G.WellFormed) (hG1PI : G.IsOnePI) (γ : FeynmanSubgraph G)
    (hγ1PI : γ.IsOnePI) (hγNe : γ.IsNonempty)
    (hQDiv : (FeynmanSubgraph.self γ.contract
      (FeynmanSubgraph.wellFormed_contract hGWF)).IsDivergent) :
    HopfGen :=
  γ.contract.toHopfGenDirect
    (FeynmanSubgraph.contract_graph_isConnectedDivergent_of_isDivergent
      hGWF hG1PI hγ1PI hγNe hQDiv)

/-! ## Step 4 — value anchor -/

/-- **R-6c-QFT-R1-body-563 — direct right-factor value.**  The underlying class is `γ.contract.toClass`
(`rfl`) — the anchor for downstream replacement of body-560's constructor. -/
@[simp] theorem FeynmanSubgraph.contractToHopfGenDirect_of_isDivergent_val
    (hGWF : G.WellFormed) (hG1PI : G.IsOnePI) (γ : FeynmanSubgraph G)
    (hγ1PI : γ.IsOnePI) (hγNe : γ.IsNonempty)
    (hQDiv : (FeynmanSubgraph.self γ.contract
      (FeynmanSubgraph.wellFormed_contract hGWF)).IsDivergent) :
    (γ.contractToHopfGenDirect_of_isDivergent hGWF hG1PI hγ1PI hγNe hQDiv).val
      = γ.contract.toClass := rfl

/-! ## Step 5 — body-560 compatibility (the only place ambient invariance appears) -/

/-- **R-6c-QFT-R1-body-563 — direct = body-560.**  When `IsAmbientInvariantDivergence` is present, the
direct right factor equals body-560's `contractToHopfGen_of_isDivergent` on the same data (both have
underlying class `γ.contract.toClass`).  `Subtype.ext rfl`; no new physics.  This is the sole occurrence
of `IsAmbientInvariantDivergence` in this module. -/
theorem FeynmanSubgraph.contractToHopfGenDirect_eq_body560
    [IsAmbientInvariantDivergence]
    (hGWF : G.WellFormed) (hG1PI : G.IsOnePI) (γ : FeynmanSubgraph G)
    (hγ1PI : γ.IsOnePI) (hγNe : γ.IsNonempty)
    (hQDiv : (FeynmanSubgraph.self γ.contract
      (FeynmanSubgraph.wellFormed_contract hGWF)).IsDivergent) :
    γ.contractToHopfGenDirect_of_isDivergent hGWF hG1PI hγ1PI hγNe hQDiv
      = γ.contractToHopfGen_of_isDivergent hGWF hG1PI hγ1PI hγNe hQDiv :=
  Subtype.ext rfl

end GaugeGeometry.QFT.Combinatorial
