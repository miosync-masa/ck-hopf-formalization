import GaugeGeometry.QFT.HopfAlgebra.DivergenceFamilyForestReflection
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCarrier

/-!
# QFT-R1-body-584 — family-indexed resolved Hopf carrier

Type-level discovery: the existing `ResolvedHopfGen` (R-6a, `ResolvedHopfCarrier.lean`) is
`{ c : ResolvedFeynmanGraphClass // (toFlatClass c).IsConnectedDivergent }` — pinned to the **old**
class-fixed `FeynmanGraphClass.IsConnectedDivergent`, which lives under the file-level blanket
`[∀ G, DivergenceMeasure G] [∀ G, IsPermInvariantDivergence G]` (uninhabitable in the φ⁴ family world,
body-564).  So before W″ can be re-keyed, the φ⁴ family needs a resolved carrier it can actually inhabit.

This body builds exactly that, **reusing the entirely instance-free identity-preserving quotient
machinery** (`toResolvedClass` / `toFlatClass` / `toResolvedClass_mapPerm` / `forget_mapPerm`, all defined
*before* `ResolvedHopfCarrier`'s divergence-class section), and pairing it with body-566's family-explicit
class predicate `FeynmanGraphClass.IsConnectedDivergentFor D Inv`.

The asymmetry is the point: **forget is natural, but rigidification is data.**  Step 3 gives the canonical
`resolved → flat` forget; the inverse `flat → resolved` lift is deliberately *not* built here (it must
choose `edgeId`/`legId` and prove W″ membership — body-585+).

## Contents

* Step 1 `ResolvedFeynmanGraphClass.IsConnectedDivergentFor` (via `toFlatClass`; no new `Quotient.lift`)
  + `isConnectedDivergentFor_toResolvedClass` anchor.
* Step 2 `ResolvedHopfGenFor D Inv` (subtype) + `ResolvedHopfHFor` + `ResolvedFeynmanGraph
  .toResolvedHopfGenFor` + `_val` + `_mapPerm` (via `Subtype.ext` + `toResolvedClass_mapPerm`).
* Step 3 `ResolvedHopfGenFor.forget` + `forgetHopfFor` (aeval) + `forget_toResolvedHopfGenFor`
  + `forgetHopfFor_X`.
* Step 4 `ResolvedPhi4HopfGen` / `ResolvedPhi4HopfH` / `forgetPhi4Hopf` + `_X` + constructor anchor.

## One-way verdict

```text
resolved → flat forget     CANONICAL / CONSTRUCTED (this body)
flat → resolved lift       OPEN / NOT CANONICAL (needs edgeId/legId choice + W″ membership, body-585+)
```

Per the HALT: no bridge / cast / equality to the old `ResolvedHopfGen` / `ResolvedHopfH`; the old
divergence classes are neither inhabited nor consumed (only the instance-free quotient machinery is used);
no `Quotient.out` / choice-based lift; no W″ membership / Measure / E / rep*; no resolved coproduct /
coassoc; the `flat → resolved` inverse is **not** asserted; zero new `class` / `structure` / `instance`
(every generator carrier is a subtype `def`/`abbrev`).
-/

namespace GaugeGeometry.QFT.Combinatorial

/-! ## Step 1 — family-indexed resolved class predicate -/

/-- **body-584 — family-indexed connected-divergence predicate on *resolved* classes.**  Read on the
forgotten flat class through body-566's family-explicit `FeynmanGraphClass.IsConnectedDivergentFor`; no new
`Quotient.lift` (`toFlatClass` already descended, R-6a). -/
def ResolvedFeynmanGraphClass.IsConnectedDivergentFor
    (D : DivergenceMeasureFamily) (Inv : PermInvariantDivergenceMeasureFamily D)
    (c : ResolvedFeynmanGraphClass) : Prop :=
  FeynmanGraphClass.IsConnectedDivergentFor D Inv c.toFlatClass

/-- **body-584 — resolved-class predicate representative anchor.**  On a resolved graph's class, the
family CD reduces to the explicit-family graph-level CD of the forgotten graph `G.forget`. -/
@[simp] theorem ResolvedFeynmanGraphClass.isConnectedDivergentFor_toResolvedClass
    (D : DivergenceMeasureFamily) (Inv : PermInvariantDivergenceMeasureFamily D)
    (G : ResolvedFeynmanGraph) :
    ResolvedFeynmanGraphClass.IsConnectedDivergentFor D Inv G.toResolvedClass
      ↔ ∃ hWF : G.forget.WellFormed,
          @FeynmanSubgraph.IsConnectedDivergent G.forget (D G.forget)
            (FeynmanSubgraph.self G.forget hWF) := by
  unfold ResolvedFeynmanGraphClass.IsConnectedDivergentFor
  rw [ResolvedFeynmanGraphClass.toFlatClass_mk]
  exact FeynmanGraphClass.isConnectedDivergentFor_toClass D Inv G.forget

/-! ## Step 2 — family-indexed resolved carrier -/

/-- **body-584 — family-indexed resolved-native Hopf generators.**  Id-preserving classes of resolved
graphs whose flat shadow is a family generator.  A *separate* type from the old `ResolvedHopfGen`; correctly
indexed by the coherent family `D`. -/
def ResolvedHopfGenFor
    (D : DivergenceMeasureFamily) (Inv : PermInvariantDivergenceMeasureFamily D) : Type :=
  { c : ResolvedFeynmanGraphClass // c.IsConnectedDivergentFor D Inv }

/-- **body-584 — the family-indexed resolved Hopf polynomial algebra.** -/
noncomputable abbrev ResolvedHopfHFor
    (D : DivergenceMeasureFamily) (Inv : PermInvariantDivergenceMeasureFamily D) : Type :=
  MvPolynomial (ResolvedHopfGenFor D Inv) ℚ

/-- **body-584 — generic resolved family generator constructor.** -/
def ResolvedFeynmanGraph.toResolvedHopfGenFor
    (D : DivergenceMeasureFamily) (Inv : PermInvariantDivergenceMeasureFamily D)
    (G : ResolvedFeynmanGraph)
    (hCD : ∃ hWF : G.forget.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent G.forget (D G.forget)
        (FeynmanSubgraph.self G.forget hWF)) :
    ResolvedHopfGenFor D Inv :=
  ⟨G.toResolvedClass,
    (ResolvedFeynmanGraphClass.isConnectedDivergentFor_toResolvedClass D Inv G).mpr hCD⟩

@[simp] theorem ResolvedFeynmanGraph.toResolvedHopfGenFor_val
    (D : DivergenceMeasureFamily) (Inv : PermInvariantDivergenceMeasureFamily D)
    (G : ResolvedFeynmanGraph)
    (hCD : ∃ hWF : G.forget.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent G.forget (D G.forget)
        (FeynmanSubgraph.self G.forget hWF)) :
    (G.toResolvedHopfGenFor D Inv hCD).val = G.toResolvedClass := rfl

/-- **body-584 — resolved family generator is `mapPerm`-invariant.**  `mapPerm σ` is an id-preserving
isomorphism, so a resolved graph and its relabeling carry the same resolved family generator.  `Subtype.ext`
+ `toResolvedClass_mapPerm`; the CD witnesses enter proof-irrelevantly. -/
theorem ResolvedFeynmanGraph.toResolvedHopfGenFor_mapPerm
    (D : DivergenceMeasureFamily) (Inv : PermInvariantDivergenceMeasureFamily D)
    (G : ResolvedFeynmanGraph) (σ : Equiv.Perm VertexId)
    (hCD : ∃ hWF : G.forget.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent G.forget (D G.forget)
        (FeynmanSubgraph.self G.forget hWF))
    (hCDσ : ∃ hWF : (G.mapPerm σ).forget.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent (G.mapPerm σ).forget (D (G.mapPerm σ).forget)
        (FeynmanSubgraph.self (G.mapPerm σ).forget hWF)) :
    (G.mapPerm σ).toResolvedHopfGenFor D Inv hCDσ = G.toResolvedHopfGenFor D Inv hCD := by
  apply Subtype.ext
  show (G.mapPerm σ).toResolvedClass = G.toResolvedClass
  exact ResolvedFeynmanGraph.toResolvedClass_mapPerm G σ

/-! ## Step 3 — the canonical forget -/

/-- **body-584 — forget a resolved family generator to its flat family generator.**  Forgets the ids on
the class; the family CD property transports by definitional unfolding (`IsConnectedDivergentFor` on the
resolved class *is* the flat predicate on `toFlatClass`). -/
def ResolvedHopfGenFor.forget
    {D : DivergenceMeasureFamily} {Inv : PermInvariantDivergenceMeasureFamily D}
    (x : ResolvedHopfGenFor D Inv) : HopfGenFor D Inv :=
  ⟨ResolvedFeynmanGraphClass.toFlatClass x.val, x.property⟩

/-- **body-584 — forgetting a resolved-graph generator yields the flat family generator of the forgotten
graph** (body-566's `toHopfGenFor`).  `Subtype.ext` + `toFlatClass_mk`. -/
theorem ResolvedFeynmanGraph.forget_toResolvedHopfGenFor
    (D : DivergenceMeasureFamily) (Inv : PermInvariantDivergenceMeasureFamily D)
    (G : ResolvedFeynmanGraph)
    (hCD : ∃ hWF : G.forget.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent G.forget (D G.forget)
        (FeynmanSubgraph.self G.forget hWF)) :
    (G.toResolvedHopfGenFor D Inv hCD).forget = G.forget.toHopfGenFor D Inv hCD := by
  apply Subtype.ext
  show ResolvedFeynmanGraphClass.toFlatClass G.toResolvedClass = G.forget.toClass
  exact ResolvedFeynmanGraphClass.toFlatClass_mk G

/-- **body-584 — the family-indexed forgetful algebra morphism** `ResolvedHopfHFor D Inv →ₐ HopfHFor D Inv`,
sending each resolved family generator to its flat family shadow.  No cast / equality to the old
`forgetHopf`. -/
noncomputable def forgetHopfFor
    (D : DivergenceMeasureFamily) (Inv : PermInvariantDivergenceMeasureFamily D) :
    ResolvedHopfHFor D Inv →ₐ[ℚ] HopfHFor D Inv :=
  MvPolynomial.aeval (fun x : ResolvedHopfGenFor D Inv => MvPolynomial.X x.forget)

@[simp] theorem forgetHopfFor_X
    (D : DivergenceMeasureFamily) (Inv : PermInvariantDivergenceMeasureFamily D)
    (x : ResolvedHopfGenFor D Inv) :
    forgetHopfFor D Inv (MvPolynomial.X x) = MvPolynomial.X x.forget := by
  simp [forgetHopfFor]

/-! ## Step 4 — φ⁴ specialization -/

/-- **body-584 — the canonical φ⁴ resolved generator.** -/
abbrev ResolvedPhi4HopfGen : Type :=
  ResolvedHopfGenFor phi4DivergenceMeasureFamily phi4PermInvariantDivergenceMeasureFamily

/-- **body-584 — the canonical φ⁴ resolved Hopf polynomial algebra.** -/
noncomputable abbrev ResolvedPhi4HopfH : Type :=
  MvPolynomial ResolvedPhi4HopfGen ℚ

/-- **body-584 (TARGET) — the φ⁴ forgetful algebra morphism** `ResolvedPhi4HopfH →ₐ Phi4HopfH`.  The φ⁴
family finally has a resolved carrier and a canonical forget to the flat φ⁴ algebra.  No `flat → resolved`
inverse is claimed. -/
noncomputable def forgetPhi4Hopf : ResolvedPhi4HopfH →ₐ[ℚ] Phi4HopfH :=
  forgetHopfFor phi4DivergenceMeasureFamily phi4PermInvariantDivergenceMeasureFamily

@[simp] theorem forgetPhi4Hopf_X (x : ResolvedPhi4HopfGen) :
    forgetPhi4Hopf (MvPolynomial.X x) = MvPolynomial.X x.forget := by
  unfold forgetPhi4Hopf
  rw [forgetHopfFor_X]

/-- **body-584 — φ⁴ resolved generator from a resolved graph** (constructor anchor for body-585+). -/
noncomputable def ResolvedFeynmanGraph.toResolvedPhi4HopfGen
    (G : ResolvedFeynmanGraph)
    (hCD : ∃ hWF : G.forget.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent G.forget (phi4DivergenceMeasureFamily G.forget)
        (FeynmanSubgraph.self G.forget hWF)) :
    ResolvedPhi4HopfGen :=
  G.toResolvedHopfGenFor phi4DivergenceMeasureFamily phi4PermInvariantDivergenceMeasureFamily hCD

@[simp] theorem ResolvedFeynmanGraph.toResolvedPhi4HopfGen_val
    (G : ResolvedFeynmanGraph)
    (hCD : ∃ hWF : G.forget.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent G.forget (phi4DivergenceMeasureFamily G.forget)
        (FeynmanSubgraph.self G.forget hWF)) :
    (G.toResolvedPhi4HopfGen hCD).val = G.toResolvedClass := rfl

end GaugeGeometry.QFT.Combinatorial
