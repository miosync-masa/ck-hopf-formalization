import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocElementNonempty

/-!
# R-6c-body-1 — component nonemptiness reduced to the CD-nonempty graph fact

First genuine-body step.  `ResolvedInputOuterElementNonemptySupply.component_nonempty` (leaf-11, powering the
survivor `hne` and Product `hLP` / `hPD`) needs every input-outer component to have nonempty vertices.

**Scout finding (why this is not free).**  `IsConnectedDivergent γ = γ.IsConnected ∧ γ.IsOnePI ∧ γ.IsDivergent`
(SubGraph:1358); `IsConnected = toFeynmanGraph.IsSupportConnected` which is `∀ ⦃u v⦄, u ∈ vertices → v ∈
vertices → SupportReachable u v` (SupportGraph:119) — VACUOUSLY true on empty vertices; and `IsDivergent =
0 ≤ divergenceDegree` with `divergenceDegree = DivergenceMeasure.degree` an ARBITRARY `Int` of the abstract
typeclass.  So `IsConnectedDivergent → vertices.Nonempty` is genuinely NOT provable from the abstract
`DivergenceMeasure` (an empty subgraph could be vacuously connected/1PI and divergent under some measure).

Hence the minimal honest obligation is the graph-theoretic fact `cd_nonempty : γ.forget.IsConnectedDivergent
→ γ.vertices.Nonempty` (a property of the divergence measure — that divergent components are nonempty), from
which `component_nonempty` follows via the admissible forest's `isConnectedDivergent`.

Per the HALT, `cd_nonempty` is the supply field (the DivergenceMeasure-level obligation); Sector / Transport
untouched.

Landed:

* `ResolvedConnectedDivergentNonemptySupply G` — `cd_nonempty`;
* `.toInputOuterElementNonemptySupply` — the leaf-11 nonemptiness supply (for any `D`).

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {G : ResolvedFeynmanGraph}

/-- **R-6c-body-1 — the CD-nonempty graph fact.**  Every connected-divergent subgraph has nonempty vertices —
a property of the divergence measure (not derivable from the abstract `DivergenceMeasure`). -/
structure ResolvedConnectedDivergentNonemptySupply (G : ResolvedFeynmanGraph) where
  /-- A connected-divergent subgraph has nonempty vertices. -/
  cd_nonempty : ∀ (γ : ResolvedFeynmanSubgraph G),
    γ.forget.IsConnectedDivergent → γ.vertices.Nonempty

/-- **R-6c-body-1 — the input-outer element nonemptiness supply (leaf-11) from the CD-nonempty fact. -/
def ResolvedConnectedDivergentNonemptySupply.toInputOuterElementNonemptySupply
    {D : ResolvedCoproductProperForestData}
    (N : ResolvedConnectedDivergentNonemptySupply G) :
    ResolvedInputOuterElementNonemptySupply D G where
  component_nonempty := fun s γ => N.cd_nonempty γ.1 (s.1.1.isConnectedDivergent γ.1 γ.2)

end GaugeGeometry.QFT.Combinatorial
