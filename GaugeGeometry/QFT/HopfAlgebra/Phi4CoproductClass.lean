import GaugeGeometry.QFT.HopfAlgebra.Phi4CoproductInvariant

/-!
# QFT-R1-body-571 — φ⁴ class descent + connected coproduct algebra hom

Body-570 proved the representative-level φ⁴ coproduct is isomorphism-invariant.  This body uses that as
the literal `Quotient.lift` well-definedness certificate: it descends the coproduct from graph
representatives to `FeynmanGraphClass`, lifts it to the generator `Phi4HopfGen`, and packages the whole
thing as an `MvPolynomial.aeval` algebra homomorphism on `Phi4HopfH`.

`Quotient.lift` needs a *total* payload (its domain is all of `FeynmanGraph`), so Step 1 totalizes the
graph-level formula by a `dite` on connected-divergence (`0` off the generator locus); the generator locus
always hits the positive branch.

## Contents

* Step 1 `phi4CoproductPayload` (private, total) + `phi4CoproductPayload_of_cd`.
* Step 2 `phi4CoproductPayload_isomorphism_invariant` (branch-synced by body-565's ∃-iff + body-570).
* Step 3 `FeynmanGraphClass.coproductConnectedPhi4` = `Quotient.lift` + `_toClass` anchor.
* Step 4 `coproductGenClass_phi4` (generator map) + `coproductGenClass_phi4_of_graph`.
* Step 5 `coproduct_strict_phi4 := MvPolynomial.aeval coproductGenClass_phi4` + `_X` / `_phi4Gen_of_graph`
  / `_one` / `_mul`.

The name `coproduct_strict_phi4` keeps the *connected*-only scope honest; the unqualified `coproduct_phi4`
is reserved for the forest version.

## Reaching

```text
representative formula     DERIVED (569)
representative invariance  DERIVED (570)
class descent              CONSTRUCTED (571)
Phi4HopfGen map            CONSTRUCTED
connected algebra hom      CONSTRUCTED via aeval
forest coproduct           NOT ENTERED
coassociativity            NOT CLAIMED
```

Per the HALT: no old `HopfH` / old generators / old coproduct; zero forbidden divergence classes; no
`Quotient.out` / cast / dependent `HEq`; zero new `class`/`structure`/`instance`; no forest / W″ / counit /
bialgebra / coassociativity; this is **not** claimed to be the final CK coproduct.  The only instance binder
is `[∀ G, Fintype (FeynmanSubgraph G)]` — finite-sum infrastructure, not physics.
-/

open scoped TensorProduct

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]

/-! ## Step 1 — total representative payload -/

open Classical in
/-- The graph-level φ⁴ coproduct, totalized to every graph (`0` off the connected-divergent locus) so it can
feed `Quotient.lift`. -/
private noncomputable def FeynmanGraph.phi4CoproductPayload (G : FeynmanGraph) :
    Phi4HopfH ⊗[ℚ] Phi4HopfH :=
  if hCD : ∃ hWF : G.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent G (phi4DivergenceMeasureFamily G)
        (FeynmanSubgraph.self G hWF) then
    G.coproductGen_phi4 hCD.choose hCD.choose_spec.2.1 hCD.choose_spec.2.2
  else 0

/-- **R-6c-QFT-R1-body-571 — payload on the generator locus.**  For any well-formed 1PI divergent witness,
the total payload is exactly body-569's representative formula (witness differences are proof-irrelevant). -/
theorem FeynmanGraph.phi4CoproductPayload_of_cd (G : FeynmanGraph) (hWF : G.WellFormed)
    (h1PI : G.IsOnePI)
    (hDiv : @FeynmanSubgraph.IsDivergent G (phi4DivergenceMeasureFamily G)
      (FeynmanSubgraph.self G hWF)) :
    G.phi4CoproductPayload = G.coproductGen_phi4 hWF h1PI hDiv := by
  have hCD : ∃ hWF : G.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent G (phi4DivergenceMeasureFamily G)
        (FeynmanSubgraph.self G hWF) :=
    ⟨hWF, h1PI.isSupportConnected, h1PI, hDiv⟩
  rw [FeynmanGraph.phi4CoproductPayload, dif_pos hCD]

/-! ## Step 2 — payload invariance -/

/-- **R-6c-QFT-R1-body-571 — the total payload is isomorphism-invariant** (the `Quotient.lift`
well-definedness certificate).  Branches synced by body-565's ∃-iff; positive branch is body-570; negative
branch is `0 = 0`.  No old Perm/Iso divergence class. -/
theorem FeynmanGraph.phi4CoproductPayload_isomorphism_invariant {G₁ G₂ : FeynmanGraph}
    (hIso : G₁.IsIso G₂) : G₁.phi4CoproductPayload = G₂.phi4CoproductPayload := by
  obtain ⟨π, rfl⟩ := hIso
  have hsync := FeynmanGraph.mapPerm_exists_self_isConnectedDivergent_iff_of_family
    phi4DivergenceMeasureFamily phi4PermInvariantDivergenceMeasureFamily π G₁
  by_cases hCD : ∃ hWF : G₁.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent G₁ (phi4DivergenceMeasureFamily G₁)
        (FeynmanSubgraph.self G₁ hWF)
  · obtain ⟨hWF, hcd⟩ := hCD
    obtain ⟨hWFπ, hcdπ⟩ := hsync.mpr ⟨hWF, hcd⟩
    rw [FeynmanGraph.phi4CoproductPayload_of_cd G₁ hWF hcd.2.1 hcd.2.2,
      FeynmanGraph.phi4CoproductPayload_of_cd (G₁.mapPerm π) hWFπ hcdπ.2.1 hcdπ.2.2]
    exact (FeynmanGraph.coproductGen_phi4_mapPerm G₁ π hWF hcd.2.1 hcd.2.2).symm
  · have hCDπ : ¬ ∃ hWF : (G₁.mapPerm π).WellFormed,
        @FeynmanSubgraph.IsConnectedDivergent (G₁.mapPerm π)
          (phi4DivergenceMeasureFamily (G₁.mapPerm π))
          (FeynmanSubgraph.self (G₁.mapPerm π) hWF) := fun h => hCD (hsync.mp h)
    rw [FeynmanGraph.phi4CoproductPayload, dif_neg hCD,
      FeynmanGraph.phi4CoproductPayload, dif_neg hCDπ]

/-! ## Step 3 — literal quotient descent -/

/-- **R-6c-QFT-R1-body-571 — the connected φ⁴ coproduct on graph *classes*.**  Descends the total payload
through the isomorphism quotient; well-definedness is body-571 Step 2. -/
noncomputable def FeynmanGraphClass.coproductConnectedPhi4 :
    FeynmanGraphClass → Phi4HopfH ⊗[ℚ] Phi4HopfH :=
  Quotient.lift FeynmanGraph.phi4CoproductPayload
    (fun _ _ h => FeynmanGraph.phi4CoproductPayload_isomorphism_invariant h)

/-- **R-6c-QFT-R1-body-571 — quotient-unfold anchor** (`rfl`; no `Quotient.out`). -/
@[simp] theorem FeynmanGraphClass.coproductConnectedPhi4_toClass (G : FeynmanGraph) :
    FeynmanGraphClass.coproductConnectedPhi4 G.toClass = G.phi4CoproductPayload := rfl

/-! ## Step 4 — generator map -/

/-- **R-6c-QFT-R1-body-571 — the connected φ⁴ coproduct on generators.** -/
noncomputable def coproductGenClass_phi4 (g : Phi4HopfGen) : Phi4HopfH ⊗[ℚ] Phi4HopfH :=
  FeynmanGraphClass.coproductConnectedPhi4 g.val

/-- **R-6c-QFT-R1-body-571 — generator map on an ambient graph generator.**  The generator property forces
the total payload's positive branch, recovering body-569's formula. -/
theorem coproductGenClass_phi4_of_graph (G : FeynmanGraph) (hWF : G.WellFormed) (h1PI : G.IsOnePI)
    (hDiv : @FeynmanSubgraph.IsDivergent G (phi4DivergenceMeasureFamily G)
      (FeynmanSubgraph.self G hWF)) :
    coproductGenClass_phi4 (G.toPhi4HopfGen hWF h1PI hDiv) = G.coproductGen_phi4 hWF h1PI hDiv := by
  unfold coproductGenClass_phi4
  rw [FeynmanGraph.toPhi4HopfGen_val, FeynmanGraphClass.coproductConnectedPhi4_toClass,
    FeynmanGraph.phi4CoproductPayload_of_cd G hWF h1PI hDiv]

/-! ## Step 5 — the connected coproduct algebra hom -/

/-- **R-6c-QFT-R1-body-571 — the connected φ⁴ coproduct as a ℚ-algebra homomorphism.**  `strict` /
`Connected` scope kept in the name; the forest version is reserved for `coproduct_phi4`. -/
noncomputable def coproduct_strict_phi4 : Phi4HopfH →ₐ[ℚ] Phi4HopfH ⊗[ℚ] Phi4HopfH :=
  MvPolynomial.aeval coproductGenClass_phi4

@[simp] theorem coproduct_strict_phi4_X (g : Phi4HopfGen) :
    coproduct_strict_phi4 (MvPolynomial.X g) = coproductGenClass_phi4 g := by
  unfold coproduct_strict_phi4
  rw [MvPolynomial.aeval_X]

@[simp] theorem coproduct_strict_phi4_phi4Gen_of_graph (G : FeynmanGraph) (hWF : G.WellFormed)
    (h1PI : G.IsOnePI)
    (hDiv : @FeynmanSubgraph.IsDivergent G (phi4DivergenceMeasureFamily G)
      (FeynmanSubgraph.self G hWF)) :
    coproduct_strict_phi4 (phi4Gen (G.toPhi4HopfGen hWF h1PI hDiv))
      = G.coproductGen_phi4 hWF h1PI hDiv := by
  unfold phi4Gen
  rw [coproduct_strict_phi4_X, coproductGenClass_phi4_of_graph]

@[simp] theorem coproduct_strict_phi4_one :
    coproduct_strict_phi4 (1 : Phi4HopfH) = 1 :=
  map_one _

@[simp] theorem coproduct_strict_phi4_mul (a b : Phi4HopfH) :
    coproduct_strict_phi4 (a * b) = coproduct_strict_phi4 a * coproduct_strict_phi4 b :=
  map_mul _ _ _

end GaugeGeometry.QFT.Combinatorial
