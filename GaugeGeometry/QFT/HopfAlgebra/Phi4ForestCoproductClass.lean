import GaugeGeometry.QFT.HopfAlgebra.Phi4ForestCoproductInvariant

/-!
# QFT-R1-body-582 — φ⁴ forest coproduct class descent + algebra hom

Body-581 proved the representative-level φ⁴ **forest** coproduct `coproductGen_forest_phi4` is
isomorphism-invariant.  This body uses that as the literal `Quotient.lift` well-definedness certificate:
it descends the forest coproduct from graph representatives to `FeynmanGraphClass`, lifts it to the
generator `Phi4HopfGen`, and packages the whole thing as an `MvPolynomial.aeval` ℚ-algebra homomorphism
`coproduct_phi4` on `Phi4HopfH`.  This is a faithful mirror of body-571's connected class descent, with
the connected representative formula replaced by body-574's full forest formula throughout.

`Quotient.lift` needs a *total* payload (its domain is all of `FeynmanGraph`), so Step 1 totalizes the
graph-level forest formula by a `dite` on connected-divergence (`0` off the generator locus); the
generator locus always hits the positive branch.

## Contents

* Step 1 `phi4ForestCoproductPayload` (private, total) + `phi4ForestCoproductPayload_of_cd`.
* Step 2 `phi4ForestCoproductPayload_isomorphism_invariant` (branch-synced by body-565's ∃-iff; positive
  branch is body-581's `coproductGen_forest_phi4_mapPerm`).
* Step 3 `FeynmanGraphClass.coproductForestPhi4` = `Quotient.lift` + `_toClass` anchor.
* Step 4 `coproductGenClass_forest_phi4` (generator map) + `coproductGenClass_forest_phi4_of_graph`.
* Step 5 `coproduct_phi4 := MvPolynomial.aeval coproductGenClass_forest_phi4` + `_X`
  / `_phi4Gen_of_graph` / `_one` / `_mul`.

The connected-only `coproduct_strict_phi4` (body-571) is kept as a separate name for the single-subgraph
scope; **no** equality / bridge between `coproduct_phi4` and `coproduct_strict_phi4` is built here.

## Reaching

```text
representative forest formula     DERIVED (574)
representative forest invariance  DERIVED (581)
forest class descent              CONSTRUCTED (582)
Phi4HopfGen forest map            CONSTRUCTED
forest algebra hom coproduct_phi4 CONSTRUCTED via aeval
coassociativity                   NOT CLAIMED
```

Per the HALT: no equality / `Equiv` with `coproduct_strict_phi4`; no `Quotient.out` / cast / dependent
`HEq`; zero new `class`/`structure`/`instance`; zero forbidden divergence classes; no counit / coassoc /
bialgebra / antipode; no W″ / reflection; the Hopf-algebra is **not** claimed complete.  The only instance
binder is `[∀ G, Fintype (FeynmanSubgraph G)]` — finite-sum infrastructure, not physics.
-/

open scoped TensorProduct

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]

/-! ## Step 1 — total representative forest payload -/

open Classical in
/-- The graph-level φ⁴ forest coproduct, totalized to every graph (`0` off the connected-divergent locus)
so it can feed `Quotient.lift`. -/
private noncomputable def FeynmanGraph.phi4ForestCoproductPayload (G : FeynmanGraph) :
    Phi4HopfH ⊗[ℚ] Phi4HopfH :=
  if hCD : ∃ hWF : G.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent G (phi4DivergenceMeasureFamily G)
        (FeynmanSubgraph.self G hWF) then
    G.coproductGen_forest_phi4 hCD.choose hCD.choose_spec.2.1 hCD.choose_spec.2.2
  else 0

/-- **body-582 — forest payload on the generator locus.**  For any well-formed 1PI divergent witness, the
total forest payload is exactly body-574's representative forest formula (witness differences are
proof-irrelevant). -/
theorem FeynmanGraph.phi4ForestCoproductPayload_of_cd (G : FeynmanGraph) (hWF : G.WellFormed)
    (h1PI : G.IsOnePI)
    (hDiv : @FeynmanSubgraph.IsDivergent G (phi4DivergenceMeasureFamily G)
      (FeynmanSubgraph.self G hWF)) :
    G.phi4ForestCoproductPayload = G.coproductGen_forest_phi4 hWF h1PI hDiv := by
  have hCD : ∃ hWF : G.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent G (phi4DivergenceMeasureFamily G)
        (FeynmanSubgraph.self G hWF) :=
    ⟨hWF, h1PI.isSupportConnected, h1PI, hDiv⟩
  rw [FeynmanGraph.phi4ForestCoproductPayload, dif_pos hCD]

/-! ## Step 2 — forest payload invariance -/

/-- **body-582 — the total forest payload is isomorphism-invariant** (the `Quotient.lift` well-definedness
certificate).  Branches synced by body-565's ∃-iff; positive branch is body-581's
`coproductGen_forest_phi4_mapPerm`; negative branch is `0 = 0`.  No old Perm/Iso divergence class. -/
theorem FeynmanGraph.phi4ForestCoproductPayload_isomorphism_invariant {G₁ G₂ : FeynmanGraph}
    (hIso : G₁.IsIso G₂) : G₁.phi4ForestCoproductPayload = G₂.phi4ForestCoproductPayload := by
  obtain ⟨π, rfl⟩ := hIso
  have hsync := FeynmanGraph.mapPerm_exists_self_isConnectedDivergent_iff_of_family
    phi4DivergenceMeasureFamily phi4PermInvariantDivergenceMeasureFamily π G₁
  by_cases hCD : ∃ hWF : G₁.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent G₁ (phi4DivergenceMeasureFamily G₁)
        (FeynmanSubgraph.self G₁ hWF)
  · obtain ⟨hWF, hcd⟩ := hCD
    obtain ⟨hWFπ, hcdπ⟩ := hsync.mpr ⟨hWF, hcd⟩
    rw [FeynmanGraph.phi4ForestCoproductPayload_of_cd G₁ hWF hcd.2.1 hcd.2.2,
      FeynmanGraph.phi4ForestCoproductPayload_of_cd (G₁.mapPerm π) hWFπ hcdπ.2.1 hcdπ.2.2]
    exact (FeynmanGraph.coproductGen_forest_phi4_mapPerm G₁ π hWF hcd.2.1 hcd.2.2).symm
  · have hCDπ : ¬ ∃ hWF : (G₁.mapPerm π).WellFormed,
        @FeynmanSubgraph.IsConnectedDivergent (G₁.mapPerm π)
          (phi4DivergenceMeasureFamily (G₁.mapPerm π))
          (FeynmanSubgraph.self (G₁.mapPerm π) hWF) := fun h => hCD (hsync.mp h)
    rw [FeynmanGraph.phi4ForestCoproductPayload, dif_neg hCD,
      FeynmanGraph.phi4ForestCoproductPayload, dif_neg hCDπ]

/-! ## Step 3 — literal quotient descent -/

/-- **body-582 — the φ⁴ forest coproduct on graph *classes*.**  Descends the total forest payload through
the isomorphism quotient; well-definedness is body-582 Step 2. -/
noncomputable def FeynmanGraphClass.coproductForestPhi4 :
    FeynmanGraphClass → Phi4HopfH ⊗[ℚ] Phi4HopfH :=
  Quotient.lift FeynmanGraph.phi4ForestCoproductPayload
    (fun _ _ h => FeynmanGraph.phi4ForestCoproductPayload_isomorphism_invariant h)

/-- **body-582 — quotient-unfold anchor** (`rfl`; no `Quotient.out`). -/
@[simp] theorem FeynmanGraphClass.coproductForestPhi4_toClass (G : FeynmanGraph) :
    FeynmanGraphClass.coproductForestPhi4 G.toClass = G.phi4ForestCoproductPayload := rfl

/-! ## Step 4 — generator map -/

/-- **body-582 — the φ⁴ forest coproduct on generators.** -/
noncomputable def coproductGenClass_forest_phi4 (g : Phi4HopfGen) : Phi4HopfH ⊗[ℚ] Phi4HopfH :=
  FeynmanGraphClass.coproductForestPhi4 g.val

/-- **body-582 — forest generator map on an ambient graph generator.**  The generator property forces the
total payload's positive branch, recovering body-574's full forest formula. -/
theorem coproductGenClass_forest_phi4_of_graph (G : FeynmanGraph) (hWF : G.WellFormed) (h1PI : G.IsOnePI)
    (hDiv : @FeynmanSubgraph.IsDivergent G (phi4DivergenceMeasureFamily G)
      (FeynmanSubgraph.self G hWF)) :
    coproductGenClass_forest_phi4 (G.toPhi4HopfGen hWF h1PI hDiv)
      = G.coproductGen_forest_phi4 hWF h1PI hDiv := by
  unfold coproductGenClass_forest_phi4
  rw [FeynmanGraph.toPhi4HopfGen_val, FeynmanGraphClass.coproductForestPhi4_toClass,
    FeynmanGraph.phi4ForestCoproductPayload_of_cd G hWF h1PI hDiv]

/-! ## Step 5 — the φ⁴ forest coproduct algebra hom -/

/-- **body-582 (TARGET) — the φ⁴ forest coproduct as a ℚ-algebra homomorphism.**  The unqualified
`coproduct_phi4`: the genuine forest coproduct (body-574 formula), descended to classes and lifted to the
generators via `MvPolynomial.aeval`.  Kept distinct from body-571's connected `coproduct_strict_phi4`; no
equality between them is claimed. -/
noncomputable def coproduct_phi4 : Phi4HopfH →ₐ[ℚ] Phi4HopfH ⊗[ℚ] Phi4HopfH :=
  MvPolynomial.aeval coproductGenClass_forest_phi4

@[simp] theorem coproduct_phi4_X (g : Phi4HopfGen) :
    coproduct_phi4 (MvPolynomial.X g) = coproductGenClass_forest_phi4 g := by
  unfold coproduct_phi4
  rw [MvPolynomial.aeval_X]

@[simp] theorem coproduct_phi4_phi4Gen_of_graph (G : FeynmanGraph) (hWF : G.WellFormed)
    (h1PI : G.IsOnePI)
    (hDiv : @FeynmanSubgraph.IsDivergent G (phi4DivergenceMeasureFamily G)
      (FeynmanSubgraph.self G hWF)) :
    coproduct_phi4 (phi4Gen (G.toPhi4HopfGen hWF h1PI hDiv))
      = G.coproductGen_forest_phi4 hWF h1PI hDiv := by
  unfold phi4Gen
  rw [coproduct_phi4_X, coproductGenClass_forest_phi4_of_graph]

@[simp] theorem coproduct_phi4_one :
    coproduct_phi4 (1 : Phi4HopfH) = 1 :=
  map_one _

@[simp] theorem coproduct_phi4_mul (a b : Phi4HopfH) :
    coproduct_phi4 (a * b) = coproduct_phi4 a * coproduct_phi4 b :=
  map_mul _ _ _

end GaugeGeometry.QFT.Combinatorial
