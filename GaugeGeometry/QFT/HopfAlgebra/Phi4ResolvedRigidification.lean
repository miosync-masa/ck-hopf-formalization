import GaugeGeometry.QFT.HopfAlgebra.Phi4ResolvedHopfCarrier
import GaugeGeometry.QFT.Combinatorial.ResolvedUniqueIdLift

/-!
# QFT-R1-body-585 — choice-based unique-ID rigidification section

Body-584 built the resolved φ⁴ carrier and the canonical `forgetPhi4Hopf : ResolvedPhi4HopfH →ₐ Phi4HopfH`,
leaving the reverse `flat → resolved` lift open because it must **choose** `edgeId`/`legId` data.  The
existing `ResolvedUniqueIdLift.lean` already supplies the allocator (`ofFlatGraphWithUniqueIds`), the exact
forget round-trip (`forget_ofFlatGraphWithUniqueIds`), and id-uniqueness
(`edgeIdsUnique_/legIdsUnique_ofFlatGraphWithUniqueIds`).  This body **promotes that allocator to a chosen
section**: pick a flat representative with `Quotient.out`, rigidify it, and lift the whole thing to a
ℚ-algebra section `rigidifyPhi4Hopf` that is a **right inverse** of `forgetPhi4Hopf`.

The asymmetry is honest: **forgetting coordinates is natural; giving coordinates is choice data.**  The
`zipIdx` ids depend on the chosen representative and its list order, so this is a *non-canonical* section
built on `Quotient.out` — **not** a `Quotient.lift` and **not** an `Equiv`.  Only `forget ∘ rigidify = id`
is proved; the other composite and naturality are not claimed.

## Contents

* Step 1 `phi4RigidifiedGraph` (`ofFlatGraphWithUniqueIds ∘ Quotient.out`) + forget-class round-trip +
  id-uniqueness.
* Step 2 `rigidifyPhi4Gen` (generator section) + `_val` + `forget_rigidifyPhi4Gen` (`Subtype.ext`).
* Step 3 `rigidifyPhi4Hopf` (aeval algebra section) + `_X`.
* Step 4 `forgetPhi4Hopf_comp_rigidifyPhi4Hopf` (`= AlgHom.id`) + pointwise corollary.

## Exact verdict

```text
forget ∘ rigidify = id       PROVED (this body)
rigidify ∘ forget = id       NOT CLAIMED (non-canonical section; ids depend on chosen rep/order)
rigidification naturality    NOT CLAIMED
W″ membership                OPEN (body-586+)
```

Per the HALT: no ID allocator re-implementation (reuses `ResolvedUniqueIdLift`); the rigidification is a
`Quotient.out`-based section, **never** a `Quotient.lift`; no flat/resolved `Equiv`; no `rigidify ∘ forget`
inverse; no W″ / saturation / Measure / E / rep*; no resolved coproduct / coassoc; zero new
`class` / `structure` / `instance`.
-/

namespace GaugeGeometry.QFT.Combinatorial

/-! ## Step 1 — chosen resolved representative -/

/-- **body-585 — the chosen unique-ID resolved representative of a φ⁴ generator.**  Pick a flat graph with
`Quotient.out`, then tag it with position-index ids (`ofFlatGraphWithUniqueIds`).  Non-canonical: depends on
the chosen representative and its list order. -/
noncomputable def phi4RigidifiedGraph (x : Phi4HopfGen) : ResolvedFeynmanGraph :=
  ofFlatGraphWithUniqueIds (Quotient.out x.val)

/-- **body-585 — the rigidified graph forgets back to the generator's class** (`forget` round-trip on the
unique-ID lift + `Quotient.out_eq`). -/
@[simp] theorem phi4RigidifiedGraph_forget_toClass (x : Phi4HopfGen) :
    (phi4RigidifiedGraph x).forget.toClass = x.val := by
  unfold phi4RigidifiedGraph
  rw [forget_ofFlatGraphWithUniqueIds]
  exact Quotient.out_eq x.val

/-- **body-585 — the rigidified graph has unique edge ids.** -/
theorem phi4RigidifiedGraph_edgeIdsUnique (x : Phi4HopfGen) :
    (phi4RigidifiedGraph x).EdgeIdsUnique :=
  edgeIdsUnique_ofFlatGraphWithUniqueIds (Quotient.out x.val)

/-- **body-585 — the rigidified graph has unique leg ids.** -/
theorem phi4RigidifiedGraph_legIdsUnique (x : Phi4HopfGen) :
    (phi4RigidifiedGraph x).LegIdsUnique :=
  legIdsUnique_ofFlatGraphWithUniqueIds (Quotient.out x.val)

/-! ## Step 2 — generator section -/

/-- **body-585 — the φ⁴ generator rigidification section.**  A φ⁴ generator lifted to the resolved φ⁴
generator of its chosen unique-ID representative.  The family-CD property transports through
`toFlatClass_mk` + the forget round-trip back to `x.property`. -/
noncomputable def rigidifyPhi4Gen (x : Phi4HopfGen) : ResolvedPhi4HopfGen :=
  ⟨(phi4RigidifiedGraph x).toResolvedClass, by
    unfold ResolvedFeynmanGraphClass.IsConnectedDivergentFor
    rw [ResolvedFeynmanGraphClass.toFlatClass_mk, phi4RigidifiedGraph_forget_toClass]
    exact x.property⟩

@[simp] theorem rigidifyPhi4Gen_val (x : Phi4HopfGen) :
    (rigidifyPhi4Gen x).val = (phi4RigidifiedGraph x).toResolvedClass := rfl

/-- **body-585 — the section is a right inverse at the generator level.**  Forgetting the rigidified
generator recovers the original φ⁴ generator.  `Subtype.ext` + `toFlatClass_mk` + the forget round-trip. -/
@[simp] theorem forget_rigidifyPhi4Gen (x : Phi4HopfGen) :
    (rigidifyPhi4Gen x).forget = x := by
  apply Subtype.ext
  show ResolvedFeynmanGraphClass.toFlatClass (rigidifyPhi4Gen x).val = x.val
  rw [rigidifyPhi4Gen_val, ResolvedFeynmanGraphClass.toFlatClass_mk,
    phi4RigidifiedGraph_forget_toClass]

/-! ## Step 3 — algebra section -/

/-- **body-585 — the φ⁴ rigidification algebra section** `Phi4HopfH →ₐ ResolvedPhi4HopfH`.  Extends
`rigidifyPhi4Gen` to the polynomial algebra by `aeval`.  A section, not an isomorphism. -/
noncomputable def rigidifyPhi4Hopf : Phi4HopfH →ₐ[ℚ] ResolvedPhi4HopfH :=
  MvPolynomial.aeval (fun x : Phi4HopfGen => MvPolynomial.X (rigidifyPhi4Gen x))

@[simp] theorem rigidifyPhi4Hopf_X (x : Phi4HopfGen) :
    rigidifyPhi4Hopf (MvPolynomial.X x) = MvPolynomial.X (rigidifyPhi4Gen x) := by
  simp [rigidifyPhi4Hopf]

/-! ## Step 4 — right inverse -/

/-- **body-585 (TARGET) — `forgetPhi4Hopf ∘ rigidifyPhi4Hopf = id`.**  The rigidification section is a right
inverse of the forgetful morphism: forgetting the chosen coordinates recovers the flat algebra element.
`MvPolynomial.algHom_ext` reduces to the generator identity `forget_rigidifyPhi4Gen`.  The reverse composite
is **not** claimed. -/
theorem forgetPhi4Hopf_comp_rigidifyPhi4Hopf :
    forgetPhi4Hopf.comp rigidifyPhi4Hopf = AlgHom.id ℚ Phi4HopfH := by
  apply MvPolynomial.algHom_ext
  intro x
  rw [AlgHom.comp_apply, rigidifyPhi4Hopf_X, forgetPhi4Hopf_X, forget_rigidifyPhi4Gen,
    AlgHom.id_apply]

/-- **body-585 — pointwise right inverse.**  `forgetPhi4Hopf (rigidifyPhi4Hopf p) = p`. -/
@[simp] theorem forgetPhi4Hopf_rigidifyPhi4Hopf (p : Phi4HopfH) :
    forgetPhi4Hopf (rigidifyPhi4Hopf p) = p := by
  have h := AlgHom.congr_fun forgetPhi4Hopf_comp_rigidifyPhi4Hopf p
  rwa [AlgHom.comp_apply, AlgHom.id_apply] at h

end GaugeGeometry.QFT.Combinatorial
