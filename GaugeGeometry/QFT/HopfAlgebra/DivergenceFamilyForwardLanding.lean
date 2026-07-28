import GaugeGeometry.QFT.HopfAlgebra.Phi4IsoInvariance
import GaugeGeometry.QFT.HopfAlgebra.Phi4ForestRightFactor
import GaugeGeometry.QFT.Combinatorial.BoundaryCompletedSubgraph

/-!
# QFT-R1-body-577 — explicit-family forward landing physics root

Body-575's audit split the seven old blanket divergence classes into REUSE / FAMILY RE-KEY / GENUINE
RESOLVED WORK.  Bodies 565/576/567/573 solved the **entire forward side** of the FAMILY RE-KEY column.
This body bundles exactly that solved forward physics into a **single explicit supply owner** — no reflection,
no resolved bridge (those stay outside the root).

## Contents

* Step 1 `DivergenceMeasureFamilyForwardLandingSupply` — one `Prop` structure carrying: `Perm` (565), `Iso`
  (576), the boundary-completed intrinsic degree equality (567's shape), and the forward canonical-forest
  contraction degree equality (573's shape).  The forest field uses the **clean generic**
  `@FeynmanGraph.admissibleForestCanonicalContractGraph D …` directly — never a polluted wrapper.
* Step 2 `phi4DivergenceMeasureFamilyForwardLandingSupply` — the φ⁴ inhabitant, wired from 565/576/567/573.
* Step 3 `boundaryCompleted_isDivergent_iff` / `forestContract_isDivergent_of_ambient` — derived from the
  degree equalities alone; the latter is the family-explicit replacement for
  `IsDivergencePreservedByAdmissibleForestContract` (no single-contraction preservation field added).

## Residual (kept OUTSIDE the root)

```text
SOLVED ROOT              D / Perm / Iso / boundary-completed intrinsic transport / forward forest contraction
OPEN (not in the root)   forest reflection (reverse power-counting) ; flat → resolved W″ carrier bridge (Measure/E/rep*)
```

Per the HALT: zero new `class`/`instance` (exactly one new `Prop` structure); zero old
Perm/Iso/Ambient/Preservation classes; no boundary/forest geometry re-proof; the reflection law is NOT
fabricated from a forward equality; no forest invariance / correcting permutation; no W″ carrier / coassoc.
-/

namespace GaugeGeometry.QFT.Combinatorial

/-! ## Step 1 — single explicit forward-landing supply -/

/-- **R-6c-QFT-R1-body-577 — the solved forward-physics landing root.**  A `Prop` structure bundling the
forward FAMILY RE-KEY column that φ⁴ has already discharged: permutation coherence, iso coherence, the
boundary-completed intrinsic degree equality, and the forward canonical-forest contraction degree equality.
Consumed as an explicit argument — no blanket class, no instance inference. -/
structure DivergenceMeasureFamilyForwardLandingSupply (D : DivergenceMeasureFamily) : Prop where
  Perm : PermInvariantDivergenceMeasureFamily D
  Iso : IsoInvariantDivergenceMeasureFamily D
  boundaryCompleted_degree :
    ∀ {G : FeynmanGraph} (γ : FeynmanSubgraph G),
      @DivergenceMeasure.degree γ.boundaryCompletedGraph (D γ.boundaryCompletedGraph)
          (FeynmanSubgraph.self γ.boundaryCompletedGraph γ.boundaryCompletedGraph_wellFormed)
        = @DivergenceMeasure.degree G (D G) γ
  forestContract_degree :
    ∀ [∀ H : FeynmanGraph, Fintype (FeynmanSubgraph H)] {G : FeynmanGraph} (hGWF : G.WellFormed)
      (A : AdmissibleSubgraphFor D G)
      (hA : A ∈ FeynmanGraph.properDisjointAdmissibleDivergentSubgraphsFor D G)
      (hQWF : (@FeynmanGraph.admissibleForestCanonicalContractGraph D _ G A hA).WellFormed),
      @DivergenceMeasure.degree (@FeynmanGraph.admissibleForestCanonicalContractGraph D _ G A hA)
          (D (@FeynmanGraph.admissibleForestCanonicalContractGraph D _ G A hA))
          (FeynmanSubgraph.self _ hQWF)
        = @DivergenceMeasure.degree G (D G) (FeynmanSubgraph.self G hGWF)

/-! ## Step 2 — φ⁴ inhabitant -/

/-- **R-6c-QFT-R1-body-577 — φ⁴ solves the forward landing root.**  A `def`, not an `instance`: `Perm` from
body-565, `Iso` from body-576, `boundaryCompleted_degree` from body-567, `forestContract_degree` from
body-573.  Every degree endpoint is explicit (φ⁴ family), no instance inference. -/
def phi4DivergenceMeasureFamilyForwardLandingSupply :
    DivergenceMeasureFamilyForwardLandingSupply phi4DivergenceMeasureFamily where
  Perm := phi4PermInvariantDivergenceMeasureFamily
  Iso := phi4IsoInvariantDivergenceMeasureFamily
  boundaryCompleted_degree γ := by
    show (FeynmanSubgraph.self γ.boundaryCompletedGraph γ.boundaryCompletedGraph_wellFormed).phi4SuperficialDegree
      = γ.phi4SuperficialDegree
    exact γ.phi4SuperficialDegree_self_boundaryCompletedGraph
  forestContract_degree hGWF A hA hQWF := by
    show (FeynmanSubgraph.self (phi4CanonicalForestContractGraph _ A hA) hQWF).phi4SuperficialDegree
      = (FeynmanSubgraph.self _ hGWF).phi4SuperficialDegree
    exact phi4CanonicalForestContractGraph_degree_eq_ambient hGWF A hA hQWF

/-! ## Step 3 — derived corollaries (from the degree equalities alone) -/

/-- **R-6c-QFT-R1-body-577 — boundary-completed divergence transport.** -/
theorem DivergenceMeasureFamilyForwardLandingSupply.boundaryCompleted_isDivergent_iff
    {D : DivergenceMeasureFamily} (S : DivergenceMeasureFamilyForwardLandingSupply D)
    {G : FeynmanGraph} (γ : FeynmanSubgraph G) :
    @FeynmanSubgraph.IsDivergent γ.boundaryCompletedGraph (D γ.boundaryCompletedGraph)
        (FeynmanSubgraph.self γ.boundaryCompletedGraph γ.boundaryCompletedGraph_wellFormed)
      ↔ @FeynmanSubgraph.IsDivergent G (D G) γ := by
  unfold FeynmanSubgraph.IsDivergent FeynmanSubgraph.divergenceDegree
  rw [S.boundaryCompleted_degree γ]

/-- **R-6c-QFT-R1-body-577 — forward forest-contraction divergence.**  The family-explicit replacement for
`IsDivergencePreservedByAdmissibleForestContract`: ambient divergence ⟹ quotient divergence, from the
degree equality alone (no preservation class). -/
theorem DivergenceMeasureFamilyForwardLandingSupply.forestContract_isDivergent_of_ambient
    {D : DivergenceMeasureFamily} (S : DivergenceMeasureFamilyForwardLandingSupply D)
    [∀ H : FeynmanGraph, Fintype (FeynmanSubgraph H)] {G : FeynmanGraph} (hGWF : G.WellFormed)
    (A : AdmissibleSubgraphFor D G)
    (hA : A ∈ FeynmanGraph.properDisjointAdmissibleDivergentSubgraphsFor D G)
    (hQWF : (@FeynmanGraph.admissibleForestCanonicalContractGraph D _ G A hA).WellFormed)
    (hGDiv : @FeynmanSubgraph.IsDivergent G (D G) (FeynmanSubgraph.self G hGWF)) :
    @FeynmanSubgraph.IsDivergent (@FeynmanGraph.admissibleForestCanonicalContractGraph D _ G A hA)
      (D (@FeynmanGraph.admissibleForestCanonicalContractGraph D _ G A hA))
      (FeynmanSubgraph.self _ hQWF) := by
  unfold FeynmanSubgraph.IsDivergent FeynmanSubgraph.divergenceDegree
  rw [S.forestContract_degree hGWF A hA hQWF]
  exact hGDiv

end GaugeGeometry.QFT.Combinatorial
