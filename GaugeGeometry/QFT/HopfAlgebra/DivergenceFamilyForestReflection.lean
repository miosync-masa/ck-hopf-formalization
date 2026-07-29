import GaugeGeometry.QFT.HopfAlgebra.DivergenceFamilyForwardLanding

/-!
# QFT-R1-body-583 — family-explicit canonical forest reflection leaf

Body-575's audit listed `IsDivergenceReflectedByAdmissibleForestContract` (the reverse power-counting law)
as GENUINE RESOLVED WORK still open.  But body-577's landing root carries the **degree equality itself** —
`ω(G/A) = ω(G)` — not a one-directional forward law.  An equality has no preferred direction, so the
reverse divergence transport is *already contained numerically*; this body simply reads it off.

The scope is deliberately narrow: only the **canonical full-graph forest contraction** `G/A` (body-573's
`phi4CanonicalForestContractGraph`), never an arbitrary nested subgraph.  The old generic class
`IsDivergenceReflectedByAdmissibleForestContract` is **not** inhabited or consumed — the family-explicit
`iff` is strictly weaker and honest about its domain.

## Contents

* Step 1 `DivergenceMeasureFamilyForwardLandingSupply.forestContract_isDivergent_iff_ambient` — the full
  `iff` from the degree equality (the forward-only `forestContract_isDivergent_of_ambient`, body-577, is
  its `.mpr`).
* Step 2 `…forestContract_ambient_isDivergent_of_quotient` — the reverse corollary (`.mp`).
* Step 3 `phi4CanonicalForestContractGraph_isDivergent_iff_ambient` /
  `phi4CanonicalForestContractGraph_ambient_isDivergent_of_quotient` — the φ⁴ specialization, both
  endpoints pinned to the explicit `phi4DivergenceMeasureFamily`.

## Revised verdict

```text
numerical reverse power-counting     DERIVED (from body-577's degree equality, this body)
old generic reflection class         NOT INHABITED (family-explicit iff is strictly weaker)
resolved parent/remainder alignment  OPEN (coherence + traceability, the real remaining work)
flat → resolved Measure/E/rep* bridge OPEN
```

Per the HALT: the old reflection / preservation classes are neither inhabited nor consumed anywhere in
this file; no W″ carrier / resolved parent machinery; no local/global `DivergenceMeasure` instance is
created; `coproduct_phi4` is not edited; zero new `class`/`structure`/`instance`; no coassociativity is
claimed.  The only instance binder is `[∀ H, Fintype (FeynmanSubgraph H)]` — finite infrastructure.
-/

namespace GaugeGeometry.QFT.Combinatorial

/-! ## Step 1 — the canonical forest contraction divergence `iff` -/

/-- **body-583 — canonical forest-contraction divergence `iff`.**  The quotient `G/A` is divergent
**iff** the ambient `G` is, read directly off body-577's degree equality `ω(G/A) = ω(G)`.  The forward
direction is body-577's `forestContract_isDivergent_of_ambient`; this adds the reverse.  No reflection /
preservation class. -/
theorem DivergenceMeasureFamilyForwardLandingSupply.forestContract_isDivergent_iff_ambient
    {D : DivergenceMeasureFamily} (S : DivergenceMeasureFamilyForwardLandingSupply D)
    [∀ H : FeynmanGraph, Fintype (FeynmanSubgraph H)] {G : FeynmanGraph} (hGWF : G.WellFormed)
    (A : AdmissibleSubgraphFor D G)
    (hA : A ∈ FeynmanGraph.properDisjointAdmissibleDivergentSubgraphsFor D G)
    (hQWF : (@FeynmanGraph.admissibleForestCanonicalContractGraph D _ G A hA).WellFormed) :
    @FeynmanSubgraph.IsDivergent (@FeynmanGraph.admissibleForestCanonicalContractGraph D _ G A hA)
        (D (@FeynmanGraph.admissibleForestCanonicalContractGraph D _ G A hA))
        (FeynmanSubgraph.self _ hQWF)
      ↔ @FeynmanSubgraph.IsDivergent G (D G) (FeynmanSubgraph.self G hGWF) := by
  unfold FeynmanSubgraph.IsDivergent FeynmanSubgraph.divergenceDegree
  rw [S.forestContract_degree hGWF A hA hQWF]

/-! ## Step 2 — reverse corollary -/

/-- **body-583 — reverse forest divergence transport.**  Ambient divergence *from* quotient divergence,
the `.mp` of the `iff`.  This is the numerical content the old
`IsDivergenceReflectedByAdmissibleForestContract` would have supplied — but here only for the canonical
full-graph contraction, and with no class inhabited. -/
theorem DivergenceMeasureFamilyForwardLandingSupply.forestContract_ambient_isDivergent_of_quotient
    {D : DivergenceMeasureFamily} (S : DivergenceMeasureFamilyForwardLandingSupply D)
    [∀ H : FeynmanGraph, Fintype (FeynmanSubgraph H)] {G : FeynmanGraph} (hGWF : G.WellFormed)
    (A : AdmissibleSubgraphFor D G)
    (hA : A ∈ FeynmanGraph.properDisjointAdmissibleDivergentSubgraphsFor D G)
    (hQWF : (@FeynmanGraph.admissibleForestCanonicalContractGraph D _ G A hA).WellFormed)
    (hQDiv : @FeynmanSubgraph.IsDivergent (@FeynmanGraph.admissibleForestCanonicalContractGraph D _ G A hA)
      (D (@FeynmanGraph.admissibleForestCanonicalContractGraph D _ G A hA))
      (FeynmanSubgraph.self _ hQWF)) :
    @FeynmanSubgraph.IsDivergent G (D G) (FeynmanSubgraph.self G hGWF) :=
  (S.forestContract_isDivergent_iff_ambient hGWF A hA hQWF).mp hQDiv

/-! ## Step 3 — φ⁴ specialization -/

/-- **body-583 — φ⁴ canonical forest-contraction divergence `iff`.**  Both endpoints pinned to the
explicit `phi4DivergenceMeasureFamily`; the quotient graph is body-573's `phi4CanonicalForestContractGraph`
(definitionally the canonical forest contraction).  No local/global instance. -/
theorem phi4CanonicalForestContractGraph_isDivergent_iff_ambient
    [∀ H : FeynmanGraph, Fintype (FeynmanSubgraph H)] {G : FeynmanGraph} (hGWF : G.WellFormed)
    (A : AdmissibleSubgraphFor phi4DivergenceMeasureFamily G)
    (hA : A ∈ G.phi4ProperDisjointAdmissibleDivergentSubgraphs)
    (hQWF : (phi4CanonicalForestContractGraph G A hA).WellFormed) :
    @FeynmanSubgraph.IsDivergent (phi4CanonicalForestContractGraph G A hA)
        (phi4DivergenceMeasureFamily (phi4CanonicalForestContractGraph G A hA))
        (FeynmanSubgraph.self _ hQWF)
      ↔ @FeynmanSubgraph.IsDivergent G (phi4DivergenceMeasureFamily G) (FeynmanSubgraph.self G hGWF) :=
  phi4DivergenceMeasureFamilyForwardLandingSupply.forestContract_isDivergent_iff_ambient
    hGWF A hA hQWF

/-- **body-583 — reverse φ⁴ forest divergence transport.**  The `.mp` of the φ⁴ `iff`: ambient
φ⁴-divergence from quotient φ⁴-divergence, for the canonical full-graph forest contraction. -/
theorem phi4CanonicalForestContractGraph_ambient_isDivergent_of_quotient
    [∀ H : FeynmanGraph, Fintype (FeynmanSubgraph H)] {G : FeynmanGraph} (hGWF : G.WellFormed)
    (A : AdmissibleSubgraphFor phi4DivergenceMeasureFamily G)
    (hA : A ∈ G.phi4ProperDisjointAdmissibleDivergentSubgraphs)
    (hQWF : (phi4CanonicalForestContractGraph G A hA).WellFormed)
    (hQDiv : @FeynmanSubgraph.IsDivergent (phi4CanonicalForestContractGraph G A hA)
      (phi4DivergenceMeasureFamily (phi4CanonicalForestContractGraph G A hA))
      (FeynmanSubgraph.self _ hQWF)) :
    @FeynmanSubgraph.IsDivergent G (phi4DivergenceMeasureFamily G) (FeynmanSubgraph.self G hGWF) :=
  (phi4CanonicalForestContractGraph_isDivergent_iff_ambient hGWF A hA hQWF).mp hQDiv

end GaugeGeometry.QFT.Combinatorial
