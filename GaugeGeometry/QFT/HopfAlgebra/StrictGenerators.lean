import GaugeGeometry.QFT.HopfAlgebra.SubgraphClass
import GaugeGeometry.QFT.HopfAlgebra.Algebra
import GaugeGeometry.QFT.HopfAlgebra.ContractionPreservation
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Strict Connes–Kreimer generators and the `HopfH` artifact  [Sprint C1 — H3.6–3.9]

This file builds the **strict Connes–Kreimer artifact**

```
HopfH := MvPolynomial HopfGen ℚ
```

where `HopfGen` is the subtype of `FeynmanGraphClass` classes whose
representatives are *connected, 1PI, and superficially divergent*
(the Connes–Kreimer 1998 generator set).

## Plan-D Hybrid strategy (Sprint B' → Sprint C1)

Sprint B' built the scaffold `HopfH_temp` over `IsSupportConnected`
generators only. Here in Sprint C1 we build `HopfH` alongside it and
an algebra-embedding bridge `HopfH →ₐ[ℚ] HopfH_temp` via subtype
inclusion. The scaffold remains as internal infrastructure, mirroring
Sprint A's `contractWith → contract` alias pattern.

## Path-Sub strategy for `IsConnectedDivergent` at the graph-class level

The predicate "`[Γ]` is a Connes–Kreimer generator" is defined by
delegation to the subgraph layer via `FeynmanSubgraph.self`, which
views `G` as its own full subgraph. This re-uses the three-conjunct
`FeynmanSubgraph.IsConnectedDivergent` definition without introducing a
parallel `FeynmanGraph.IsOnePI ∧ ...` API.

## Path-W divergence supply (2026-04-24)

The class-level lift requires `DivergenceMeasure` and permutation-
invariance on *every* representative, not just one. We supply these
as global instance hypotheses:

```
variable [∀ G, DivergenceMeasure G]
         [∀ G, IsPermInvariantDivergence G]
         [∀ G, IsIsoInvariantDivergence G]
```

These are `variable` parameters, not global axioms — concrete
invocations will instantiate them. The design note's H3.6 calls for
this "representative-dependent `DivergenceMeasure` supplied externally"
pattern.

## Tag map (HOPF_DECOMPOSITION.md § H3 Sprint C)

* `[Def]` `FeynmanGraph.IsConnectedDivergent` — H3.6 delegation
* `[Algebra]` `FeynmanGraphClass.IsConnectedDivergent` — H3.6 lift
* `[Def]` `HopfGen` — H3.7
* `[Def]` `HopfH` — H3.8
* `[Algebra]` `bridge : HopfH →ₐ[ℚ] HopfH_temp` — H3.9
-/

open scoped TensorProduct

namespace GaugeGeometry.QFT.Combinatorial

/-! ### `FeynmanSubgraph.self` and its permutation transport -/

namespace FeynmanSubgraph

variable {G : FeynmanGraph}

/-- The full-subgraph `self` corresponds to the ambient graph itself
on every data field. -/
@[simp] theorem self_vertices (hG : G.WellFormed) :
    (FeynmanSubgraph.self G hG).vertices = G.vertices := rfl

@[simp] theorem self_internalEdges (hG : G.WellFormed) :
    (FeynmanSubgraph.self G hG).internalEdges = G.internalEdges := rfl

@[simp] theorem self_externalLegs (hG : G.WellFormed) :
    (FeynmanSubgraph.self G hG).externalLegs = G.externalLegs := rfl

/-- The underlying `FeynmanGraph` of `self G hG` is `G`. -/
@[simp] theorem self_toFeynmanGraph (hG : G.WellFormed) :
    (FeynmanSubgraph.self G hG).toFeynmanGraph = G := rfl

/-- `(self G hG).mapPerm π` coincides field-wise with
`self (G.mapPerm π) (mapPerm_wellFormed hG)`. Both are
`FeynmanSubgraph (G.mapPerm π)` and their three data fields agree
definitionally. -/
theorem mapPerm_self (π : Equiv.Perm VertexId) (hG : G.WellFormed) :
    (FeynmanSubgraph.self G hG).mapPerm π =
      FeynmanSubgraph.self (G.mapPerm π) (FeynmanGraph.mapPerm_wellFormed hG) := rfl

end FeynmanSubgraph

/-! ### Well-formedness under inverse permutation

`mapPerm_wellFormed` gives one direction; we also need its converse
`(G.mapPerm π).WellFormed → G.WellFormed` for the
reverse implication in `mapPerm_isConnectedDivergent_iff`.
-/

namespace FeynmanGraph

/-- `WellFormed` is stable under taking the inverse permutation: if
`G.mapPerm π` is well-formed then so is `G`. -/
theorem wellFormed_of_mapPerm {π : Equiv.Perm VertexId} {G : FeynmanGraph}
    (h : (G.mapPerm π).WellFormed) : G.WellFormed := by
  have hback : ((G.mapPerm π).mapPerm π⁻¹).WellFormed := mapPerm_wellFormed h
  have heq : (G.mapPerm π).mapPerm π⁻¹ = G := by
    rw [← FeynmanGraph.mapPerm_mul]; simp
  rw [heq] at hback
  exact hback

end FeynmanGraph

/-! ### H3.6 graph-level — `FeynmanGraph.IsConnectedDivergent` via delegation -/

namespace FeynmanGraph

variable {G : FeynmanGraph}

/--
**H3.6 (graph level)** — A Feynman graph is connected-divergent (i.e.
a Connes–Kreimer generator candidate) iff it is well-formed *and*
`FeynmanSubgraph.self` is connected-divergent as a subgraph of itself.

The `∃ hG : G.WellFormed` existential wrapper makes this a `Prop` on
`FeynmanGraph` alone, at the cost of carrying the proof in a propositional
wrapper; `G.WellFormed` is proof-irrelevant so no choice is made.
-/
def IsConnectedDivergent [DivergenceMeasure G] : Prop :=
  ∃ hG : G.WellFormed, (FeynmanSubgraph.self G hG).IsConnectedDivergent

theorem IsConnectedDivergent.wellFormed [DivergenceMeasure G]
    (h : G.IsConnectedDivergent) : G.WellFormed := h.1

theorem IsConnectedDivergent.self_isConnectedDivergent
    [DivergenceMeasure G] (h : G.IsConnectedDivergent) :
    (FeynmanSubgraph.self G h.wellFormed).IsConnectedDivergent := h.2

end FeynmanGraph

/-! ### Path-W: global `DivergenceMeasure` supply

For the class-lift we need the invariance to hold for any pair of
representatives. We supply `DivergenceMeasure` and both invariance
classes as *family* instance hypotheses at the `section` level;
concrete instances are substituted at use sites.
-/

section PathW

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
         [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
         [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]

namespace FeynmanGraph

variable {G : FeynmanGraph}

omit [∀ G : FeynmanGraph, IsIsoInvariantDivergence G] in
/-- Permutation-invariance of `IsConnectedDivergent` at the graph level.
The three conjuncts are handled by Sprint A `mapPerm_isSupportConnected_iff`,
`mapPerm_isOnePI_iff`, and `IsPermInvariantDivergence.degree_mapPerm` on
the `self` subgraphs (the Path-Sub commutation of `self` and `mapPerm`
is `rfl`). -/
theorem mapPerm_isConnectedDivergent_iff (π : Equiv.Perm VertexId) (G : FeynmanGraph) :
    (G.mapPerm π).IsConnectedDivergent ↔ G.IsConnectedDivergent := by
  constructor
  · rintro ⟨hWFπ, hConn, hOPI, hDiv⟩
    have hWF : G.WellFormed := FeynmanGraph.wellFormed_of_mapPerm hWFπ
    refine ⟨hWF, ?_, ?_, ?_⟩
    · -- IsConnected: subgraph-level `self.IsConnected` is graph-level
      -- `IsSupportConnected` definitionally.
      show G.IsSupportConnected
      have hConn' : (G.mapPerm π).IsSupportConnected := hConn
      exact (FeynmanGraph.mapPerm_isSupportConnected_iff π G).mp hConn'
    · show G.IsOnePI
      have hOPI' : (G.mapPerm π).IsOnePI := hOPI
      exact (FeynmanGraph.mapPerm_isOnePI_iff π G).mp hOPI'
    · -- IsDivergent: transport via `IsPermInvariantDivergence` on `self`.
      -- `(self G hWF).mapPerm π = self (G.mapPerm π) hWFπ` (rfl), and
      -- `IsPermInvariantDivergence G` says the degrees agree.
      show (FeynmanSubgraph.self G hWF).IsDivergent
      unfold FeynmanSubgraph.IsDivergent FeynmanSubgraph.divergenceDegree
      have hdeg :
          (DivergenceMeasure.degree
              ((FeynmanSubgraph.self G hWF).mapPerm π) : Int) =
            DivergenceMeasure.degree (FeynmanSubgraph.self G hWF) :=
        IsPermInvariantDivergence.degree_mapPerm π (FeynmanSubgraph.self G hWF)
      -- RHS of hdeg is the divergenceDegree we want.
      -- LHS: (self G hWF).mapPerm π = self (G.mapPerm π) hWFπ (rfl),
      -- so its degree equals `hDiv`-witnessed nonneg.
      have hDiv' :
          (0 : Int) ≤ DivergenceMeasure.degree
            ((FeynmanSubgraph.self G hWF).mapPerm π) := by
        rw [show (FeynmanSubgraph.self G hWF).mapPerm π
              = FeynmanSubgraph.self (G.mapPerm π)
                  (FeynmanGraph.mapPerm_wellFormed hWF) from rfl]
        -- Nonneg for self on G.mapPerm π, witnessed by hDiv at (perhaps different)
        -- hWFπ — but proof-irrelevance of WellFormed makes the subgraphs equal.
        have : FeynmanSubgraph.self (G.mapPerm π)
                (FeynmanGraph.mapPerm_wellFormed hWF) =
               FeynmanSubgraph.self (G.mapPerm π) hWFπ := rfl
        rw [this]
        exact hDiv
      rw [← hdeg]
      exact hDiv'
  · rintro ⟨hWF, hConn, hOPI, hDiv⟩
    have hWFπ : (G.mapPerm π).WellFormed := FeynmanGraph.mapPerm_wellFormed hWF
    refine ⟨hWFπ, ?_, ?_, ?_⟩
    · show (G.mapPerm π).IsSupportConnected
      exact (FeynmanGraph.mapPerm_isSupportConnected_iff π G).mpr hConn
    · show (G.mapPerm π).IsOnePI
      exact (FeynmanGraph.mapPerm_isOnePI_iff π G).mpr hOPI
    · -- Symmetric direction: transport (self G hWF).IsDivergent via
      -- IsPermInvariantDivergence π to (self G hWF).mapPerm π, which is
      -- definitionally self (G.mapPerm π) hWFπ.
      show (FeynmanSubgraph.self (G.mapPerm π) hWFπ).IsDivergent
      have hMapDiv : ((FeynmanSubgraph.self G hWF).mapPerm π).IsDivergent :=
        FeynmanSubgraph.mapPerm_isDivergent hDiv
      -- (self G hWF).mapPerm π = self (G.mapPerm π) hWFπ by rfl.
      exact hMapDiv

end FeynmanGraph

/-! ### H3.6 class level — `FeynmanGraphClass.IsConnectedDivergent` -/

namespace FeynmanGraphClass

/--
**H3.6 (class level)** — `IsConnectedDivergent` lifts to
`FeynmanGraphClass` via `Quotient.lift`; well-definedness is
`mapPerm_isConnectedDivergent_iff`.
-/
def IsConnectedDivergent : FeynmanGraphClass → Prop :=
  Quotient.lift (fun G : FeynmanGraph => G.IsConnectedDivergent)
    (fun G₁ G₂ ⟨π, hπ⟩ => by
      subst hπ
      exact propext (FeynmanGraph.mapPerm_isConnectedDivergent_iff π G₁).symm)

omit [∀ G : FeynmanGraph, IsIsoInvariantDivergence G] in
@[simp] theorem isConnectedDivergent_toClass (G : FeynmanGraph) :
    IsConnectedDivergent G.toClass ↔ G.IsConnectedDivergent := Iff.rfl

omit [∀ G : FeynmanGraph, IsIsoInvariantDivergence G] in
/-- A connected-divergent class is in particular support-connected. -/
theorem IsConnectedDivergent.isSupportConnected
    {c : FeynmanGraphClass} (h : c.IsConnectedDivergent) :
    c.IsSupportConnected := by
  induction c using Quotient.inductionOn with
  | _ G =>
    change G.IsConnectedDivergent at h
    rcases h with ⟨_, hConn, _, _⟩
    exact hConn

end FeynmanGraphClass

/-! ### H3.7 — `HopfGen`, the strict Connes–Kreimer generator subtype -/

/--
**H3.7** — Connes–Kreimer 1998 strict generators: classes of Feynman
graphs that are connected, 1PI, and superficially divergent.

The generator is a subtype of `FeynmanGraphClass`, carrying the
connected-divergent witness.
-/
def HopfGen : Type :=
  { c : FeynmanGraphClass // c.IsConnectedDivergent }

/-- A connected-divergent class automatically passes the
`HopfGenTemp` entry criterion (`IsSupportConnected`). This is the
bridge's underlying fact at the subtype level. -/
def HopfGen.toTemp (g : HopfGen) : HopfGenTemp :=
  ⟨g.val, g.property.isSupportConnected⟩

omit [∀ G : FeynmanGraph, IsIsoInvariantDivergence G] in
@[simp] theorem HopfGen.toTemp_val (g : HopfGen) :
    g.toTemp.val = g.val := rfl

/-! ### H3.8 — `HopfH` polynomial algebra -/

/--
**H3.8** — The strict Connes–Kreimer Hopf algebra carrier: a free
commutative ℚ-algebra on the generators `HopfGen`. Mathlib provides
the `CommRing` and `Algebra ℚ` instances automatically.
-/
noncomputable abbrev HopfH : Type := MvPolynomial HopfGen ℚ

/-- The generator of `HopfH` corresponding to a connected-divergent
graph class. -/
noncomputable def gen (g : HopfGen) : HopfH := MvPolynomial.X g

noncomputable example : CommRing HopfH := inferInstance
noncomputable example : Algebra ℚ HopfH := inferInstance
noncomputable example : CommRing (HopfH ⊗[ℚ] HopfH) := inferInstance
noncomputable example : Algebra ℚ (HopfH ⊗[ℚ] HopfH) := inferInstance

/-! ### H3.9 — Bridge `HopfH →ₐ[ℚ] HopfH_temp` -/

/--
**H3.9** — Algebra embedding from the strict artifact `HopfH` into the
Sprint B' scaffold `HopfH_temp`. Defined via the universal property of
`MvPolynomial` (`aeval`) applied to the subtype inclusion
`HopfGen → HopfGenTemp`.

Mirrors Sprint A's `contractWith → contract` alias pattern: the strict
artifact and the scaffold coexist; `HopfH` carries the Connes–Kreimer
claim, `HopfH_temp` is internal infrastructure.
-/
noncomputable def bridge : HopfH →ₐ[ℚ] HopfH_temp :=
  MvPolynomial.aeval (fun g => gen_temp (HopfGen.toTemp g))

omit [∀ G : FeynmanGraph, IsIsoInvariantDivergence G] in
@[simp] theorem bridge_X (g : HopfGen) :
    bridge (MvPolynomial.X g) = gen_temp (HopfGen.toTemp g) := by
  unfold bridge
  rw [MvPolynomial.aeval_X]

/-! ### Subgraph → strict CK generator lift (Sprint D, Path-B prep)

Two subgraph-to-`HopfGen` constructions used by `coproductGen_strict`
in `Coproduct.lean`:

* `FeynmanSubgraph.toHopfGen` — γ as a `HopfGen` element (left tensor
  factor `[γ]`). Requires `γ.IsConnectedDivergent` (subgraph level)
  and uses `IsAmbientInvariantDivergence` to lift to the graph-level
  predicate `γ.toFeynmanGraph.IsConnectedDivergent`.

* `FeynmanSubgraph.contractToHopfGen` — `γ.contract` as a `HopfGen`
  element (right tensor factor `[Γ/γ]`). Requires the Sprint D prep
  preservation lemma `contract_isConnectedDivergent` (which itself
  consumes `IsDivergencePreservedByContract`) plus
  `IsAmbientInvariantDivergence` for the lift. -/

namespace FeynmanSubgraph

variable {G : FeynmanGraph}

omit [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
     [∀ G : FeynmanGraph, IsIsoInvariantDivergence G] in
/-- **Subgraph CD ⇒ graph-level CD** — Lift a subgraph-level
`IsConnectedDivergent` to the graph-level predicate
`γ.toFeynmanGraph.IsConnectedDivergent`. Uses
`IsAmbientInvariantDivergence` (Path-W typeclass #4). -/
theorem toFeynmanGraph_isConnectedDivergent
    [IsAmbientInvariantDivergence]
    {γ : FeynmanSubgraph G} (hγCD : γ.IsConnectedDivergent) :
    γ.toFeynmanGraph.IsConnectedDivergent := by
  refine ⟨γ.toFeynmanGraph_wellFormed, ?_, ?_, ?_⟩
  · -- IsConnected at the self level = γ.toFeynmanGraph.IsSupportConnected
    -- = γ.IsConnected (defn).
    exact hγCD.isConnected
  · -- IsOnePI at the self level = γ.toFeynmanGraph.IsOnePI = γ.IsOnePI.
    exact hγCD.isOnePI
  · -- IsDivergent at the self level: ambient invariance gives equality
    -- of degrees with γ's degree, which is hγCD.isDivergent.
    exact self_toFeynmanGraph_isDivergent hγCD.isDivergent

/-- The `HopfGen` element corresponding to a subgraph that is
connected, 1PI, and divergent in its ambient. -/
def toHopfGen [IsAmbientInvariantDivergence]
    (γ : FeynmanSubgraph G) (hγCD : γ.IsConnectedDivergent) : HopfGen :=
  ⟨γ.toFeynmanGraph.toClass,
    (FeynmanGraphClass.isConnectedDivergent_toClass γ.toFeynmanGraph).mpr
      (γ.toFeynmanGraph_isConnectedDivergent hγCD)⟩

omit [∀ G : FeynmanGraph, IsIsoInvariantDivergence G] in
@[simp] theorem toHopfGen_val [IsAmbientInvariantDivergence]
    {γ : FeynmanSubgraph G} (hγCD : γ.IsConnectedDivergent) :
    (γ.toHopfGen hγCD).val = γ.toFeynmanGraph.toClass := rfl

end FeynmanSubgraph

/-- The `HopfGen` element corresponding to `γ.contract` (right tensor
factor `[Γ/γ]` in the Connes–Kreimer coproduct sum). Requires the full
Sprint D-prep preservation chain. -/
def FeynmanSubgraph.contractToHopfGen
    [IsDivergencePreservedByContract] [IsAmbientInvariantDivergence]
    {G : FeynmanGraph} (hG : G.WellFormed) (hG1PI : G.IsOnePI)
    (γ : FeynmanSubgraph G) (hγCD : γ.IsConnectedDivergent)
    (hγNe : γ.IsNonempty) :
    HopfGen :=
  -- (self γ.contract _).IsConnectedDivergent from contract_isConnectedDivergent.
  -- Lift to γ.contract.IsConnectedDivergent (graph level) via toFeynmanGraph_isConnectedDivergent
  -- on `self`-subgraph (note: `(self _).toFeynmanGraph = γ.contract`, so the lift
  -- is essentially trivial).
  let hSelfCD : (FeynmanSubgraph.self γ.contract
      (FeynmanSubgraph.wellFormed_contract hG)).IsConnectedDivergent :=
    FeynmanSubgraph.contract_isConnectedDivergent hG hG1PI hγCD.isOnePI hγNe hγCD.isDivergent
  -- Now the self-subgraph's data fields are γ.contract's, so its toFeynmanGraph
  -- is γ.contract. Lift via Path-Sub.
  (FeynmanSubgraph.self γ.contract
      (FeynmanSubgraph.wellFormed_contract hG)).toHopfGen hSelfCD

omit [∀ G : FeynmanGraph, IsIsoInvariantDivergence G] in
@[simp] theorem FeynmanSubgraph.contractToHopfGen_val
    [IsDivergencePreservedByContract] [IsAmbientInvariantDivergence]
    {G : FeynmanGraph} (hG : G.WellFormed) (hG1PI : G.IsOnePI)
    (γ : FeynmanSubgraph G) (hγCD : γ.IsConnectedDivergent) (hγNe : γ.IsNonempty) :
    (γ.contractToHopfGen hG hG1PI hγCD hγNe).val = γ.contract.toClass := rfl

end PathW

end GaugeGeometry.QFT.Combinatorial
