import GaugeGeometry.QFT.HopfAlgebra.QFTRightFactorDirect
import GaugeGeometry.QFT.Combinatorial.DivergenceMeasureFamily

/-!
# QFT-R1-body-566 — family-indexed strict generator + φ⁴ right factor COMPLETE

Body-565 built the coherent measure-family interface and its φ⁴ inhabitant, and banked the graph-level
rename well-definedness core (as a Combinatorial `∃`-form).  This body lifts that certificate through the
isomorphism quotient to a **family-indexed** connected-divergence class predicate and generator, and
assembles the φ⁴ right factor end-to-end.

The landing point is deliberately **not** an adapter to the existing `HopfGen` (which is defined through
the old, over-strong class-level lift): `HopfGenFor D` is a *separate* subtype, correctly indexed by the
coherent family `D`.  No cast / equality / `Equiv` between the two is built.

## Contents

* Step 1 `FeynmanGraphClass.IsConnectedDivergentFor D Inv` — the family-indexed class predicate via
  `Quotient.lift`, well-defined by body-565's rename `∃`-form.
* Step 2 `isConnectedDivergentFor_toClass` — the sole quotient-unfold anchor (`Iff.rfl`).
* Step 3 `HopfGenFor D Inv` (subtype) + `FeynmanGraph.toHopfGenFor` generic constructor + value anchor.
* Step 4 `Phi4HopfGen` — the canonical φ⁴ generator (proof owner used once).
* Step 5 `contract_exists_self_isConnectedDivergent_of_family` — quotient CD assembly re-keyed to an
  explicit family `D` (body-560/563 topology, no old typeclass cast).
* Step 6 `FeynmanSubgraph.contractToPhi4HopfGen` — the φ⁴ right factor: ambient φ⁴-divergence ⟹ the
  `Phi4HopfGen` right factor `[Γ/γ]`, via body-562's `hQDiv` + Step 5 + `toHopfGenFor`.
* Step 7 value anchor (`= γ.contract.toClass`, `rfl`).

## Reaching statement

```text
φ⁴ quotient divergence       DERIVED (562)
direct graph assembly        DERIVED (563 / Step 5 re-key)
family rename coherence      DERIVED (564–565)
family quotient predicate    CONSTRUCTED (566)
φ⁴ right factor             CONSTRUCTED (566)
ambient invariance on right  ZERO
```

Iso invariance is not needed for the right graph-class quotient; it will be audited separately in the
future left subgraph-class / index ownership.

Per the HALT: no equality / `Equiv` / cast to the existing `HopfGen`; the old class predicate is not
edited; no old instance is assumed; no new `class` / `structure` / `instance` (`HopfGenFor` is a subtype
`def`); the left factor is not entered; no boundary completion; no coproduct / Hopf-algebra / coassociativity
is issued; no φ⁴ measure or topology is re-proved.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable {G : FeynmanGraph}

/-! ## Step 1 — family-indexed class predicate -/

/-- **R-6c-QFT-R1-body-566 — family-indexed connected-divergence class predicate.**  Lifts the coherent
family's graph-level CD (`∃ hWF, (self G hWF).IsConnectedDivergent` under `D G`) through the isomorphism
quotient; well-definedness is body-565's rename `∃`-form. -/
def FeynmanGraphClass.IsConnectedDivergentFor
    (D : DivergenceMeasureFamily) (Inv : PermInvariantDivergenceMeasureFamily D) :
    FeynmanGraphClass → Prop :=
  Quotient.lift
    (fun G => ∃ hWF : G.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent G (D G) (FeynmanSubgraph.self G hWF))
    (fun G₁ G₂ ⟨π, hπ⟩ => by
      subst hπ
      exact propext
        (FeynmanGraph.mapPerm_exists_self_isConnectedDivergent_iff_of_family D Inv π G₁).symm)

/-! ## Step 2 — representative anchor -/

/-- **R-6c-QFT-R1-body-566 — quotient-unfold anchor** (`Iff.rfl`). -/
@[simp] theorem FeynmanGraphClass.isConnectedDivergentFor_toClass
    (D : DivergenceMeasureFamily) (Inv : PermInvariantDivergenceMeasureFamily D) (G : FeynmanGraph) :
    FeynmanGraphClass.IsConnectedDivergentFor D Inv G.toClass
      ↔ ∃ hWF : G.WellFormed,
          @FeynmanSubgraph.IsConnectedDivergent G (D G) (FeynmanSubgraph.self G hWF) :=
  Iff.rfl

/-! ## Step 3 — family-indexed generator -/

/-- **R-6c-QFT-R1-body-566 — family-indexed strict CK generator.**  A subtype of `FeynmanGraphClass`,
indexed by the coherent family `D` — a *separate* type from the existing `HopfGen`. -/
def HopfGenFor
    (D : DivergenceMeasureFamily) (Inv : PermInvariantDivergenceMeasureFamily D) : Type :=
  { c : FeynmanGraphClass // c.IsConnectedDivergentFor D Inv }

/-- **R-6c-QFT-R1-body-566 — generic family generator constructor.** -/
def FeynmanGraph.toHopfGenFor
    (D : DivergenceMeasureFamily) (Inv : PermInvariantDivergenceMeasureFamily D) (G : FeynmanGraph)
    (hGCD : ∃ hWF : G.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent G (D G) (FeynmanSubgraph.self G hWF)) :
    HopfGenFor D Inv :=
  ⟨G.toClass, (FeynmanGraphClass.isConnectedDivergentFor_toClass D Inv G).mpr hGCD⟩

@[simp] theorem FeynmanGraph.toHopfGenFor_val
    (D : DivergenceMeasureFamily) (Inv : PermInvariantDivergenceMeasureFamily D) (G : FeynmanGraph)
    (hGCD : ∃ hWF : G.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent G (D G) (FeynmanSubgraph.self G hWF)) :
    (G.toHopfGenFor D Inv hGCD).val = G.toClass := rfl

/-! ## Step 4 — canonical φ⁴ generator -/

/-- **R-6c-QFT-R1-body-566 — the canonical φ⁴ strict generator.** -/
abbrev Phi4HopfGen : Type :=
  HopfGenFor phi4DivergenceMeasureFamily phi4PermInvariantDivergenceMeasureFamily

/-! ## Step 5 — family-explicit quotient CD assembly -/

/-- **R-6c-QFT-R1-body-566 — quotient CD, explicit family.**  Re-key of body-563 Step 2 to an explicit
family `D`: from the explicit quotient-divergence leaf, `γ.contract` is connected-divergent (as the
`∃`-form).  Connectivity / 1PI are the existing topology; no old typeclass theorem is cast. -/
theorem FeynmanSubgraph.contract_exists_self_isConnectedDivergent_of_family
    (D : DivergenceMeasureFamily) (hGWF : G.WellFormed) (hG1PI : G.IsOnePI)
    {γ : FeynmanSubgraph G} (hγ1PI : γ.IsOnePI) (hγNe : γ.IsNonempty)
    (hQDiv : @FeynmanSubgraph.IsDivergent γ.contract (D γ.contract)
      (FeynmanSubgraph.self γ.contract (FeynmanSubgraph.wellFormed_contract hGWF))) :
    ∃ hQWF : γ.contract.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent γ.contract (D γ.contract)
        (FeynmanSubgraph.self γ.contract hQWF) := by
  refine ⟨FeynmanSubgraph.wellFormed_contract hGWF, ?_, ?_, ?_⟩
  · show γ.contract.IsSupportConnected
    exact FeynmanSubgraph.IsConnected_contract_of_IsConnected hG1PI.isSupportConnected
      hγ1PI.isConnected hγNe
  · show γ.contract.IsOnePI
    exact FeynmanSubgraph.contract_isOnePI hG1PI hγ1PI hγNe
  · exact hQDiv

/-! ## Step 6 — φ⁴ right factor (target) -/

/-- **R-6c-QFT-R1-body-566 — the φ⁴ right factor `[Γ/γ]`.**  From ambient φ⁴-divergence, body-562 supplies
the quotient-divergence leaf `hQDiv`; Step 5 assembles the quotient CD; `toHopfGenFor` produces the
canonical `Phi4HopfGen`.  Consumes **no** `IsAmbientInvariantDivergence`, **no**
`IsDivergencePreservedByContract`, and no cast to the old `HopfGen`. -/
def FeynmanSubgraph.contractToPhi4HopfGen
    (hGWF : G.WellFormed) (hG1PI : G.IsOnePI) (γ : FeynmanSubgraph G)
    (hγ1PI : γ.IsOnePI) (hγNe : γ.IsNonempty)
    (hGDiv : @FeynmanSubgraph.IsDivergent G (phi4DivergenceMeasureFamily G)
      (FeynmanSubgraph.self G hGWF)) :
    Phi4HopfGen :=
  FeynmanGraph.toHopfGenFor phi4DivergenceMeasureFamily phi4PermInvariantDivergenceMeasureFamily
    γ.contract
    (FeynmanSubgraph.contract_exists_self_isConnectedDivergent_of_family
      phi4DivergenceMeasureFamily hGWF hG1PI hγ1PI hγNe
      (phi4_contract_self_isDivergent_of_ambient hGWF γ hGDiv))

/-! ## Step 7 — value anchor -/

/-- **R-6c-QFT-R1-body-566 — φ⁴ right-factor value.**  The underlying class is `γ.contract.toClass`
(`rfl`).  The φ⁴ right factor is now fully connected. -/
@[simp] theorem FeynmanSubgraph.contractToPhi4HopfGen_val
    (hGWF : G.WellFormed) (hG1PI : G.IsOnePI) (γ : FeynmanSubgraph G)
    (hγ1PI : γ.IsOnePI) (hγNe : γ.IsNonempty)
    (hGDiv : @FeynmanSubgraph.IsDivergent G (phi4DivergenceMeasureFamily G)
      (FeynmanSubgraph.self G hGWF)) :
    (γ.contractToPhi4HopfGen hGWF hG1PI hγ1PI hγNe hGDiv).val = γ.contract.toClass := rfl

end GaugeGeometry.QFT.Combinatorial
