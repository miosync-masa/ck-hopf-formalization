import GaugeGeometry.QFT.Combinatorial.Phi4PermutationInvariance

/-!
# QFT-R1-body-565 — coherent divergence-measure family interface + φ⁴ inhabitant

Body-564 showed that no adapter to the existing `IsPermInvariantDivergence` can exist: its field
re-quantifies the *target* measure `[DivergenceMeasure (G.mapPerm π)]` as an arbitrary instance, so a
coherent φ⁴ family cannot inhabit it.  Rather than force the old class, this body builds the **correct**
parallel interface — a family `D : (G : FeynmanGraph) → DivergenceMeasure G` whose rename coherence relates
`D (G.mapPerm π)` to `D G` (both endpoints selected by the *same* `D`) — and inhabits it for φ⁴.

This banks the graph-level rename well-definedness core.  Wiring the family-indexed class predicate /
generator to `HopfGen` is body-566 (the existing `HopfGen` is defined through the old class-level lift, so
no *direct* adapter to it is claimed here).

## Contents

* Step 1 `DivergenceMeasureFamily` — the family carrier (a plain function, not an instance family).
* Step 2 `PermInvariantDivergenceMeasureFamily` — the coherent rename interface (both endpoints via `D`;
  no independent `[DivergenceMeasure …]` binder; a `Prop` `structure`, consumed as an explicit argument).
* Step 3 `mapPerm_isDivergent_iff_of_family` — subgraph divergence rename transport from the interface.
* Step 4 `phi4DivergenceMeasureFamily` + `phi4PermInvariantDivergenceMeasureFamily` — the φ⁴ inhabitant
  (a `def`, not an instance), via body-564's family equality.
* Step 5 `mapPerm_isConnectedDivergent_iff_of_family` — graph-level CD rename invariance, family-explicit
  mirror of the existing `mapPerm_isConnectedDivergent_iff` (topology unchanged; divergence via Step 3).
* Step 6 `mapPerm_phi4_isConnectedDivergent_iff` — the φ⁴ corollary (the well-definedness certificate that
  body-566's `Quotient.lift` will consume).

## Scope verdict

```text
Old interface : IsPermInvariantDivergence — target measure independently rebound; NOT realizable from a
                coherent family.
Parallel      : PermInvariantDivergenceMeasureFamily D — both endpoints selected by the same D; φ⁴
                inhabitant constructed.
```

No *direct* adapter to the existing `HopfGen` is claimed: `FeynmanGraphClass.IsConnectedDivergent` /
`HopfGen` are themselves defined through the old class-level lift.  Body-566 issues the family-indexed
class predicate and generator in parallel.

Per the HALT: the old `IsPermInvariantDivergence` is not edited and not inhabited; nothing is made an
`instance`; iso invariance is not entered; the quotient/class/`HopfGen` layer is not entered; the right
factor is not wired; boundary completion is not entered; the coproduct/coassociativity/final theorem are
untouched; no φ⁴ numerical theorem is re-proved.  Exactly one new `structure`
(`PermInvariantDivergenceMeasureFamily`); no new `class`/`instance`; no HopfAlgebra import.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable {G : FeynmanGraph}

/-! ## Step 1 — coherent family carrier -/

/-- A **divergence-measure family**: an explicit choice of measure per graph.  This is an ordinary
function, deliberately *not* an instance family. -/
abbrev DivergenceMeasureFamily := (G : FeynmanGraph) → DivergenceMeasure G

/-! ## Step 2 — correct permutation-coherence interface -/

/-- **R-6c-QFT-R1-body-565 — coherent rename interface.**  Both the source and target measures are the
*same* family `D` evaluated at `G` and `G.mapPerm π` respectively — no independently re-bound
`[DivergenceMeasure (G.mapPerm π)]`.  A `Prop` structure consumed as an explicit argument, never a
`class`. -/
structure PermInvariantDivergenceMeasureFamily (D : DivergenceMeasureFamily) : Prop where
  degree_mapPerm :
    ∀ {G : FeynmanGraph} (π : Equiv.Perm VertexId) (γ : FeynmanSubgraph G),
      @DivergenceMeasure.degree (G.mapPerm π) (D (G.mapPerm π)) (γ.mapPerm π)
        = @DivergenceMeasure.degree G (D G) γ

/-! ## Step 3 — family-level subgraph divergence transport -/

/-- **R-6c-QFT-R1-body-565 — subgraph divergence is rename-invariant for a coherent family.** -/
theorem FeynmanSubgraph.mapPerm_isDivergent_iff_of_family
    (D : DivergenceMeasureFamily) (Inv : PermInvariantDivergenceMeasureFamily D)
    (π : Equiv.Perm VertexId) (γ : FeynmanSubgraph G) :
    @FeynmanSubgraph.IsDivergent (G.mapPerm π) (D (G.mapPerm π)) (γ.mapPerm π)
      ↔ @FeynmanSubgraph.IsDivergent G (D G) γ := by
  unfold FeynmanSubgraph.IsDivergent FeynmanSubgraph.divergenceDegree
  rw [Inv.degree_mapPerm π γ]

/-! ## Step 4 — φ⁴ family inhabitant -/

/-- The φ⁴ divergence-measure family.  `@[reducible]` only satisfies the class-valued-`def` linter (the
codomain `DivergenceMeasure G` is a class); it is **not** an `instance`, so instance resolution never
picks it up. -/
@[reducible] def phi4DivergenceMeasureFamily : DivergenceMeasureFamily := fun G => phi4DivergenceMeasure G

@[simp] theorem phi4DivergenceMeasureFamily_apply (G : FeynmanGraph) :
    phi4DivergenceMeasureFamily G = phi4DivergenceMeasure G := rfl

/-- **R-6c-QFT-R1-body-565 — the φ⁴ family is permutation-coherent.**  A `def`, not an `instance` —
inhabited directly by body-564's family equality `phi4DivergenceMeasure_degree_mapPerm`. -/
def phi4PermInvariantDivergenceMeasureFamily :
    PermInvariantDivergenceMeasureFamily phi4DivergenceMeasureFamily where
  degree_mapPerm π γ := phi4DivergenceMeasure_degree_mapPerm π γ

/-! ## Step 5 — graph-level CD rename invariance (family-explicit, Combinatorial `∃`-form)

The graph-level predicate `FeynmanGraph.IsConnectedDivergent` lives in the HopfAlgebra layer
(`StrictGenerators.lean`), which the HALT forbids importing.  But it is *definitionally*
`∃ hWF, (FeynmanSubgraph.self G hWF).IsConnectedDivergent`, and that unfolded form is pure Combinatorial.
So the graph-level rename core is stated here in the `∃`-form — defeq to the HopfAlgebra predicate, hence
directly consumable by body-566 (which does import that layer). -/

/-- **R-6c-QFT-R1-body-565 — graph-level connected-divergence is rename-invariant for a coherent family**
(Combinatorial `∃`-form, defeq to `FeynmanGraph.IsConnectedDivergent` rename).  Well-formedness /
connectivity / 1PI transport are the existing topological facts; divergence transports via Step 3 on the
self-subgraph.  The old `IsPermInvariantDivergence` is not used. -/
theorem FeynmanGraph.mapPerm_exists_self_isConnectedDivergent_iff_of_family
    (D : DivergenceMeasureFamily) (Inv : PermInvariantDivergenceMeasureFamily D)
    (π : Equiv.Perm VertexId) (G : FeynmanGraph) :
    (∃ hWF : (G.mapPerm π).WellFormed,
        @FeynmanSubgraph.IsConnectedDivergent (G.mapPerm π) (D (G.mapPerm π))
          (FeynmanSubgraph.self (G.mapPerm π) hWF))
      ↔ (∃ hWF : G.WellFormed,
        @FeynmanSubgraph.IsConnectedDivergent G (D G) (FeynmanSubgraph.self G hWF)) := by
  constructor
  · rintro ⟨hWFπ, hConn, hOPI, hDiv⟩
    -- forward WellFormed transport via the inverse permutation (Combinatorial only)
    have hWF : G.WellFormed := by
      have h := FeynmanGraph.mapPerm_wellFormed (π := π⁻¹) hWFπ
      rw [← FeynmanGraph.mapPerm_mul, inv_mul_cancel, FeynmanGraph.mapPerm_one] at h
      exact h
    refine ⟨hWF, ?_, ?_, ?_⟩
    · have hConn' : (G.mapPerm π).IsSupportConnected := hConn
      exact (FeynmanGraph.mapPerm_isSupportConnected_iff π G).mp hConn'
    · have hOPI' : (G.mapPerm π).IsOnePI := hOPI
      exact (FeynmanGraph.mapPerm_isOnePI_iff π G).mp hOPI'
    · -- divergence transports via the family bridge on the self-subgraph
      -- ((self G hWF).mapPerm π = self (G.mapPerm π) hWFπ definitionally, WellFormed proof-irrelevant)
      exact (FeynmanSubgraph.mapPerm_isDivergent_iff_of_family D Inv π
        (FeynmanSubgraph.self G hWF)).mp hDiv
  · rintro ⟨hWF, hConn, hOPI, hDiv⟩
    have hWFπ : (G.mapPerm π).WellFormed := FeynmanGraph.mapPerm_wellFormed hWF
    refine ⟨hWFπ, ?_, ?_, ?_⟩
    · have hConn' : G.IsSupportConnected := hConn
      exact (FeynmanGraph.mapPerm_isSupportConnected_iff π G).mpr hConn'
    · have hOPI' : G.IsOnePI := hOPI
      exact (FeynmanGraph.mapPerm_isOnePI_iff π G).mpr hOPI'
    · exact (FeynmanSubgraph.mapPerm_isDivergent_iff_of_family D Inv π
        (FeynmanSubgraph.self G hWF)).mpr hDiv

/-! ## Step 6 — φ⁴ graph corollary (body-566 well-definedness certificate) -/

/-- **R-6c-QFT-R1-body-565 — φ⁴ graph-level CD is rename-invariant** (Combinatorial `∃`-form).  This is the
`Quotient.lift` well-definedness certificate that body-566 will consume (after wrapping in the HopfAlgebra
`FeynmanGraph.IsConnectedDivergent`, to which it is defeq) to issue the family-indexed class predicate. -/
theorem FeynmanGraph.mapPerm_phi4_exists_self_isConnectedDivergent_iff
    (π : Equiv.Perm VertexId) (G : FeynmanGraph) :
    (∃ hWF : (G.mapPerm π).WellFormed,
        @FeynmanSubgraph.IsConnectedDivergent (G.mapPerm π) (phi4DivergenceMeasureFamily (G.mapPerm π))
          (FeynmanSubgraph.self (G.mapPerm π) hWF))
      ↔ (∃ hWF : G.WellFormed,
        @FeynmanSubgraph.IsConnectedDivergent G (phi4DivergenceMeasureFamily G)
          (FeynmanSubgraph.self G hWF)) :=
  FeynmanGraph.mapPerm_exists_self_isConnectedDivergent_iff_of_family
    phi4DivergenceMeasureFamily phi4PermInvariantDivergenceMeasureFamily π G

end GaugeGeometry.QFT.Combinatorial
