import GaugeGeometry.QFT.Combinatorial.Phi4ExternalValence

/-!
# QFT-R1-body-562 — φ⁴ `DivergenceMeasure` packaging + ambient-invariance no-go audit

Body-561 finished the numerical kernel `phi4SuperficialDegree = 4 − (E_ambient + |∂γ|)`.  Packaging it as
an explicit `DivergenceMeasure` immediately exposes **another scope trap**, one layer past body-560.

## The gap the type forces open

The correct φ⁴ degree of an arbitrary subgraph carries the induced boundary `|∂γ| = γ.boundaryEdgeCount`.
But the existing intrinsic lift `γ.toFeynmanGraph` **drops** the boundary edges (it does not turn them into
external legs — `SubGraph.lean` says so explicitly), so

```text
ω(self γ.toFeynmanGraph) = 4 − E_ambient(γ) = ω(γ) + |∂γ|.
```

Hence the abstract law `IsAmbientInvariantDivergence.degree_self_eq` — `deg γ = deg (self γ.toFeynmanGraph)`
— holds **only when `γ.boundaryEdgeCount = 0`** under the correct φ⁴ measure (Steps 3–4).  Body-560's
`hQDiv` entrance is still right; but the `IsAmbientInvariantDivergence` that `contractToHopfGen_of_isDivergent`
demands (via `toHopfGen`) is, for a boundaryful subgraph, **not realizable** by this measure on the current
boundary-forgetting API.  Once again:

```text
not a physics deficit  →  API ownership loss: toFeynmanGraph forgot the induced boundary.
```

## Contents

* Step 1 `phi4DivergenceMeasure` — the measure as an **explicit value** (no global/scoped instance).
* Step 2 `phi4_isDivergent_iff` — φ⁴ divergence criterion (explicit measure, no inference).
* Step 3 `phi4_degree_self_toFeynmanGraph` — the exact gap `ω(self toFeynmanGraph) = ω(γ) + |∂γ|`, and
  the equality holds `↔ boundaryEdgeCount = 0`.
* Step 4 `phi4_degree_self_ne_of_boundaryEdgeCount_pos` — the **no-go**, fixed as a plain theorem (no giant
  instance-contradiction needed).
* Step 5 `phi4_contract_self_isDivergent_iff` / `..._of_ambient` — full-graph divergence transport under the
  explicit measure; the forward corollary is exactly body-560's `hQDiv` leaf.
* Step 6 (docstring) safe-stop verdict + named residuals; **body-560 is NOT wired up here.**

## Verdict (Step 6)

```text
IsAmbientInvariantDivergence is NOT realizable by the correct φ⁴ measure on the current
boundary-forgetting `toFeynmanGraph` API — it holds only in the boundaryEdgeCount = 0 scope.
```

Named residuals:

```text
right factor : graph-level HopfGen constructor from quotient CD, WITHOUT
               IsAmbientInvariantDivergence                                 — SHALLOW
left factor  : a boundary-completed intrinsic subgraph graph, or a resolved
               boundary-aware generator                                     — GENUINE QFT WORK
```

Per the HALT: no global/scoped `DivergenceMeasure` instance; no `IsAmbientInvariantDivergence` instance is
built; the boundary count is never ignored to fake that class; body-560 is not edited; `toFeynmanGraph` is
not changed; no boundary-completed graph is constructed here; the coproduct/coassociativity/final theorem
are untouched; ZERO new `class`/`structure`/`instance`.  The forest transport is **safe-stopped** (a clean
explicit-measure forest statement is non-shallow: `AdmissibleSubgraph G` carries a `[DivergenceMeasure G]`
instance in its very type) — deferred, not faked.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable {G : FeynmanGraph}

/-! ## Step 1 — the explicit φ⁴ measure (no instance) -/

/-- **R-6c-QFT-R1-body-562 — φ⁴ superficial-divergence measure, as an explicit value.**  Its `degree`
field is body-561's boundary-corrected `phi4SuperficialDegree`.  Deliberately **not** an `instance`: no
global/scoped `DivergenceMeasure` is registered — every use below passes it explicitly.  Marked
`@[reducible]` only to satisfy the class-valued-`def` linter; `@[reducible]` is **not** `@[instance]`, so
instance resolution still never picks this up (no pollution). -/
@[reducible] def phi4DivergenceMeasure (G : FeynmanGraph) : DivergenceMeasure G where
  degree := FeynmanSubgraph.phi4SuperficialDegree

@[simp] theorem phi4DivergenceMeasure_degree (γ : FeynmanSubgraph G) :
    @DivergenceMeasure.degree G (phi4DivergenceMeasure G) γ = γ.phi4SuperficialDegree := rfl

/-! ## Step 2 — φ⁴ divergence criterion -/

/-- **R-6c-QFT-R1-body-562 — φ⁴ divergence criterion.**  Under the explicit φ⁴ measure, a subgraph is
(Weinberg-)divergent iff its physical external valence is at most `4`. -/
theorem phi4_isDivergent_iff (γ : FeynmanSubgraph G) :
    @FeynmanSubgraph.IsDivergent G (phi4DivergenceMeasure G) γ
      ↔ γ.physicalExternalLegCount ≤ 4 := by
  simp only [FeynmanSubgraph.isDivergent_def, FeynmanSubgraph.divergenceDegree,
    phi4DivergenceMeasure_degree, FeynmanSubgraph.phi4SuperficialDegree_nonneg_iff]

/-! ## Step 3 — the ambient degree gap (load-bearing audit) -/

/-- **R-6c-QFT-R1-body-562 — the boundary gap.**  The φ⁴ degree of the *intrinsic self-graph* of `γ`
exceeds `γ`'s own φ⁴ degree by exactly the induced boundary `|∂γ|`, because `toFeynmanGraph` drops the
boundary edges. -/
theorem phi4_degree_self_toFeynmanGraph (γ : FeynmanSubgraph G) :
    (FeynmanSubgraph.self γ.toFeynmanGraph γ.toFeynmanGraph_wellFormed).phi4SuperficialDegree
      = γ.phi4SuperficialDegree + (γ.boundaryEdgeCount : Int) := by
  rw [FeynmanSubgraph.phi4SuperficialDegree_self]
  simp only [FeynmanSubgraph.toFeynmanGraph_externalLegs]
  unfold FeynmanSubgraph.phi4SuperficialDegree FeynmanSubgraph.physicalExternalLegCount
    FeynmanSubgraph.externalLegCount
  push_cast
  omega

/-- **R-6c-QFT-R1-body-562 — ambient equality holds iff no induced boundary.** -/
theorem phi4_degree_self_eq_iff_boundaryEdgeCount_eq_zero (γ : FeynmanSubgraph G) :
    (FeynmanSubgraph.self γ.toFeynmanGraph γ.toFeynmanGraph_wellFormed).phi4SuperficialDegree
        = γ.phi4SuperficialDegree
      ↔ γ.boundaryEdgeCount = 0 := by
  rw [phi4_degree_self_toFeynmanGraph]
  omega

/-- **R-6c-QFT-R1-body-562 — forward corollary.** -/
theorem boundaryEdgeCount_eq_zero_of_phi4_degree_self_eq (γ : FeynmanSubgraph G)
    (h : (FeynmanSubgraph.self γ.toFeynmanGraph γ.toFeynmanGraph_wellFormed).phi4SuperficialDegree
          = γ.phi4SuperficialDegree) :
    γ.boundaryEdgeCount = 0 :=
  (phi4_degree_self_eq_iff_boundaryEdgeCount_eq_zero γ).mp h

/-! ## Step 4 — the no-go, as a plain theorem -/

/-- **R-6c-QFT-R1-body-562 — ambient-invariance no-go.**  If `γ` has a positive induced boundary, the
φ⁴ ambient-invariance equality `deg(self γ.toFeynmanGraph) = deg γ` is **false** — so the correct φ⁴
measure cannot realize `IsAmbientInvariantDivergence` outside the `boundaryEdgeCount = 0` scope.  Stated as
a counterexample condition; no `IsAmbientInvariantDivergence` instance is assumed or contradicted. -/
theorem phi4_degree_self_ne_of_boundaryEdgeCount_pos (γ : FeynmanSubgraph G)
    (h : 0 < γ.boundaryEdgeCount) :
    (FeynmanSubgraph.self γ.toFeynmanGraph γ.toFeynmanGraph_wellFormed).phi4SuperficialDegree
      ≠ γ.phi4SuperficialDegree := by
  intro heq
  have hzero := boundaryEdgeCount_eq_zero_of_phi4_degree_self_eq γ heq
  omega

/-! ## Step 5 — full-graph divergence transport under the explicit measure -/

/-- **R-6c-QFT-R1-body-562 — full-graph divergence transport.**  Under the explicit φ⁴ measure, the full
quotient `G/γ` is divergent iff the full ambient `G` is.  Full-graph statement only; proved measure-freely
from body-559's external-boundary preservation (`contract_externalLegs` + `card_map`), so the public type
carries no blanket `DivergenceMeasure` binder — only the two explicit φ⁴ measures. -/
theorem phi4_contract_self_isDivergent_iff (hGWF : G.WellFormed) (γ : FeynmanSubgraph G) :
    @FeynmanSubgraph.IsDivergent γ.contract (phi4DivergenceMeasure γ.contract)
        (FeynmanSubgraph.self γ.contract (FeynmanSubgraph.wellFormed_contract hGWF))
      ↔
    @FeynmanSubgraph.IsDivergent G (phi4DivergenceMeasure G)
        (FeynmanSubgraph.self G hGWF) := by
  rw [phi4_isDivergent_iff, phi4_isDivergent_iff,
      FeynmanSubgraph.self_physicalExternalLegCount, FeynmanSubgraph.self_physicalExternalLegCount,
      FeynmanSubgraph.contract_externalLegs, Multiset.card_map]

/-- **R-6c-QFT-R1-body-562 — the correct physical `hQDiv` leaf.**  If the full ambient `G` is φ⁴-divergent,
so is the full quotient `G/γ`.  This is exactly the quotient-divergence witness that body-560's
`contractToHopfGen_of_isDivergent` consumes — supplied here without any single-contraction preservation
class, and without `IsAmbientInvariantDivergence`. -/
theorem phi4_contract_self_isDivergent_of_ambient (hGWF : G.WellFormed) (γ : FeynmanSubgraph G)
    (hGDiv : @FeynmanSubgraph.IsDivergent G (phi4DivergenceMeasure G) (FeynmanSubgraph.self G hGWF)) :
    @FeynmanSubgraph.IsDivergent γ.contract (phi4DivergenceMeasure γ.contract)
      (FeynmanSubgraph.self γ.contract (FeynmanSubgraph.wellFormed_contract hGWF)) :=
  (phi4_contract_self_isDivergent_iff hGWF γ).mpr hGDiv

/-! ## Step 6 — safe-stop

The forest analogue and the wiring into body-560's `contractToHopfGen_of_isDivergent` are **deliberately
not done here** (see the module docstring's verdict).  `hQDiv` is CONSTRUCTED (Step 5); the obstruction is
that `IsAmbientInvariantDivergence` is FALSE for boundaryful subgraphs (Step 4), and body-560's constructor
still carries that global binder.  The genuine remaining QFT work is a boundary-completed intrinsic subgraph
graph (or a resolved boundary-aware generator) for the left factor — not a discharge of the current
`toFeynmanGraph`. -/

end GaugeGeometry.QFT.Combinatorial
