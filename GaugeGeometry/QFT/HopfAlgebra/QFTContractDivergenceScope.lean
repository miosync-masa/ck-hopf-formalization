import GaugeGeometry.QFT.HopfAlgebra.StrictGenerators
import GaugeGeometry.QFT.Combinatorial.ExternalBoundaryContraction

/-!
# QFT-R1-body-560 — single-contraction divergence scope audit + explicit quotient-divergence adapter

This body does **not** change `IsDivergencePreservedByContract`; it audits its real consumption path and
opens a *parallel* right-factor entrance that consumes the correct physical leaf — the divergence of the
**quotient** — instead of the over-strong single-contraction class.

## Scope audit — where the class is actually consumed

The one load-bearing consumption chain is essentially a single strand:

```text
IsDivergencePreservedByContract.contract_isDivergent
  → FeynmanSubgraph.contract_isDivergent                 (re-export of the class field)
  → FeynmanSubgraph.contract_isConnectedDivergent        (Connected + 1PI + [Divergent via the class])
  → FeynmanSubgraph.contractToHopfGen                    (right tensor factor `[Γ/γ]`)
  → strict coproduct right factor
```

Everything else is instance-binder propagation.  The canonical strict coproduct entry is a
`g : HopfGen`, and `HopfGen = { c : FeynmanGraphClass // c.IsConnectedDivergent }` — so the ambient
generator **already carries** its own connected-divergence witness.  The information needed to conclude
that the quotient stays divergent is present at the entrance, but the class re-derives it *abstractly*
(via `contract_isDivergent`, which asserts `γ 1PI → γ divergent ⟹ quotient divergent` with **no ambient
premise**) and thereby demands more than a boundary-dependent measure can give (cf. body-559: the
single-contraction class does not follow from external-boundary preservation; `φ⁴₄` counterexample).

**Verdict:** the missing ambient premise is an *API ownership loss*, not a physics deficit.  The correct
fix is to thread the quotient-divergence witness explicitly, not to inhabit the over-strong socket.

## What this body does / does not do

* Step 1 rebuilds the `IsConnectedDivergent` aggregate of the quotient from an **explicit** quotient
  divergence hypothesis `hQDiv`, reusing the purely-topological connectivity / 1PI preservation lemmas
  and **not** consuming `IsDivergencePreservedByContract`.
* Step 2 exposes a faithful right-factor constructor `contractToHopfGen_of_isDivergent` built on Step 1;
  its type is free of `IsDivergencePreservedByContract`.
* Step 3 proves the new and legacy constructors agree (as the same `HopfGen`) whenever the old class is
  present — no new physics, pure `Subtype.ext` + proof irrelevance.
* Step 4 (this docstring) records the scope split; the old class is retained as a valid *conditional*.

In `φ⁴₄` the missing `hQDiv` will be supplied (next body) as
`ambient divergent + externalLegCount quotient = externalLegCount ambient ⟹ quotient divergent`,
using the body-559 boundary-preservation corollaries — the over-strong socket is bypassed, not
fabricated.  Whether a broad migration off the old class is warranted is deferred until the new
constructor's consumers are threaded.

Per the HALT: `IsDivergencePreservedByContract` is not edited; ZERO new `class` / `structure` /
`instance`; no `φ⁴` measure is implemented; the coproduct / coassociativity / final theorem are not
edited; ambient divergence is never fabricated from `γ` divergence; `Coproduct.lean` is not imported
(no cycle).
-/

namespace GaugeGeometry.QFT.Combinatorial

set_option linter.unusedSectionVars false

-- The Path-W ambient invariance families are *assumed* (instance binders) exactly as the strict
-- generator layer requires them; no invariance instance is defined here (per the HALT).
variable [∀ G : FeynmanGraph, DivergenceMeasure G]
variable [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
variable [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
variable {G : FeynmanGraph}

/-! ## Step 1 — quotient `IsConnectedDivergent` from an explicit quotient-divergence leaf -/

/-- **R-6c-QFT-R1-body-560 — faithful quotient CD assembly.**  `γ.contract` (as a full self-subgraph)
is connected-divergent, built from an **explicit** quotient-divergence witness `hQDiv` together with the
purely topological preservation facts.  Unlike `FeynmanSubgraph.contract_isConnectedDivergent`, this does
**not** consume `IsDivergencePreservedByContract`: connectivity is `IsConnected_contract_of_IsConnected`,
1PI is `contract_isOnePI`, and divergence is supplied directly by `hQDiv`. -/
theorem FeynmanSubgraph.contract_isConnectedDivergent_of_isDivergent
    (hGwf : G.WellFormed) (hG1PI : G.IsOnePI)
    {γ : FeynmanSubgraph G}
    (hγ1PI : γ.IsOnePI) (hγNe : γ.IsNonempty)
    (hQDiv : (FeynmanSubgraph.self γ.contract
      (FeynmanSubgraph.wellFormed_contract hGwf)).IsDivergent) :
    (FeynmanSubgraph.self γ.contract
      (FeynmanSubgraph.wellFormed_contract hGwf)).IsConnectedDivergent := by
  refine ⟨?_, ?_, ?_⟩
  · -- IsConnected: H1.16 (topology only).
    show (FeynmanSubgraph.self γ.contract _).toFeynmanGraph.IsSupportConnected
    show γ.contract.IsSupportConnected
    exact FeynmanSubgraph.IsConnected_contract_of_IsConnected hG1PI.isSupportConnected
      hγ1PI.isConnected hγNe
  · -- IsOnePI: `contract_isOnePI` (topology only).
    show (FeynmanSubgraph.self γ.contract _).toFeynmanGraph.IsOnePI
    show γ.contract.IsOnePI
    exact FeynmanSubgraph.contract_isOnePI hG1PI hγ1PI hγNe
  · -- IsDivergent: the explicit physical leaf, NOT the class.
    exact hQDiv

/-! ## Step 2 — faithful right-factor constructor (parallel to `contractToHopfGen`) -/

/-- **R-6c-QFT-R1-body-560 — quotient-divergence right-factor constructor.**  The `HopfGen` element
`[Γ/γ]`, built from an **explicit** quotient-divergence witness `hQDiv` via Step 1 and the Path-Sub lift
`toHopfGen`.  Its type carries only `IsAmbientInvariantDivergence` (for the ambient lift) — it is free of
`IsDivergencePreservedByContract`, so a boundary-dependent measure can feed it directly. -/
def FeynmanSubgraph.contractToHopfGen_of_isDivergent
    [IsAmbientInvariantDivergence]
    (hGwf : G.WellFormed) (hG1PI : G.IsOnePI)
    (γ : FeynmanSubgraph G)
    (hγ1PI : γ.IsOnePI) (hγNe : γ.IsNonempty)
    (hQDiv : (FeynmanSubgraph.self γ.contract
      (FeynmanSubgraph.wellFormed_contract hGwf)).IsDivergent) :
    HopfGen :=
  (FeynmanSubgraph.self γ.contract
      (FeynmanSubgraph.wellFormed_contract hGwf)).toHopfGen
    (FeynmanSubgraph.contract_isConnectedDivergent_of_isDivergent hGwf hG1PI hγ1PI hγNe hQDiv)

/-- **R-6c-QFT-R1-body-560 — right-factor value.**  The underlying class of the faithful right factor is
`γ.contract.toClass` (`rfl`, since `(self γ.contract _).toFeynmanGraph = γ.contract`). -/
@[simp] theorem FeynmanSubgraph.contractToHopfGen_of_isDivergent_val
    [IsAmbientInvariantDivergence]
    (hGwf : G.WellFormed) (hG1PI : G.IsOnePI)
    (γ : FeynmanSubgraph G) (hγ1PI : γ.IsOnePI) (hγNe : γ.IsNonempty)
    (hQDiv : (FeynmanSubgraph.self γ.contract
      (FeynmanSubgraph.wellFormed_contract hGwf)).IsDivergent) :
    (γ.contractToHopfGen_of_isDivergent hGwf hG1PI hγ1PI hγNe hQDiv).val
      = γ.contract.toClass := rfl

/-! ## Step 3 — legacy compatibility (same `HopfGen` when the old class is present) -/

/-- **R-6c-QFT-R1-body-560 — new = legacy.**  With `IsDivergencePreservedByContract` present, feeding the
faithful constructor the class-derived quotient divergence yields exactly the legacy
`contractToHopfGen`.  Pure `Subtype.ext` + definitional proof irrelevance — no new physics. -/
theorem FeynmanSubgraph.contractToHopfGen_of_isDivergent_eq_legacy
    [IsDivergencePreservedByContract] [IsAmbientInvariantDivergence]
    (hGwf : G.WellFormed) (hG1PI : G.IsOnePI)
    (γ : FeynmanSubgraph G) (hγCD : γ.IsConnectedDivergent) (hγNe : γ.IsNonempty) :
    γ.contractToHopfGen_of_isDivergent hGwf hG1PI hγCD.isOnePI hγNe
        (FeynmanSubgraph.contract_isDivergent hGwf hγCD.isOnePI hγCD.isDivergent)
      = γ.contractToHopfGen hGwf hG1PI hγCD hγNe :=
  Subtype.ext rfl

end GaugeGeometry.QFT.Combinatorial
