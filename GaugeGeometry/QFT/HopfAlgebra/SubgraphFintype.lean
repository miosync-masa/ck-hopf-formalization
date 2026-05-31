import GaugeGeometry.QFT.Combinatorial.SubGraph
import Mathlib.Data.Multiset.Powerset
import Mathlib.Data.Fintype.Powerset

/-!
# Concrete `Fintype (FeynmanSubgraph G)` instance  [Sprint D, Path-cut discharge]

This file supplies the concrete `Fintype (FeynmanSubgraph G)` instance
that has been carried as a Path-W `variable` hypothesis since Sprint
C2 Phase A. It discharges the supply commitment recorded in
`HOPF_DECOMPOSITION.md § H4`.

## Strategy: triple-injection into ambient-finite types

A `FeynmanSubgraph G` is determined (up to proof irrelevance) by the
triple `(γ.vertices, γ.internalEdges, γ.externalLegs)`. Each component
is bounded:

* `γ.vertices ⊆ G.vertices` — lives in `G.vertices.powerset`
* `γ.internalEdges ≤ G.internalEdges` — lives in `G.internalEdges.powerset`
* `γ.externalLegs ≤ G.externalLegs` — lives in `G.externalLegs.powerset`

`Multiset.powerset : Multiset α → Multiset (Multiset α)` (Mathlib) plus
`DecidableEq` on `FeynmanEdge` / `ExternalLeg` give us a finite codomain.
`FeynmanSubgraph.ext_iff`-style injectivity (proof fields are
proof-irrelevant) lets us conclude `Fintype` via `Fintype.ofInjective`.

## Surface compliance

`Multiset.powerset` is computable (Mathlib); `Fintype.ofInjective` is
not. We mark the resulting instance `noncomputable` accordingly. Axiom
audit footprint: `[propext, Classical.choice, Quot.sound]` — same as
the rest of the project.
-/

namespace GaugeGeometry.QFT.Combinatorial

namespace FeynmanSubgraph

variable {G : FeynmanGraph}

/-- Three-field injection used for `Fintype` derivation. -/
private def toTriple (γ : FeynmanSubgraph G) :
    Finset VertexId × Multiset FeynmanEdge × Multiset ExternalLeg :=
  (γ.vertices, γ.internalEdges, γ.externalLegs)

private theorem toTriple_injective :
    Function.Injective (toTriple : FeynmanSubgraph G → _) := by
  intro γ₁ γ₂ h
  cases γ₁; cases γ₂
  simp [toTriple] at h
  obtain ⟨hV, hI, hE⟩ := h
  subst hV; subst hI; subst hE
  rfl

end FeynmanSubgraph

namespace FeynmanGraph

variable (G : FeynmanGraph)

/-- The finite set of all triples that can possibly arise from a
`FeynmanSubgraph G` data triple. The vertices component is `G.vertices.powerset`;
the multiset components are toFinset'd `Multiset.powerset` of the
corresponding ambient. -/
private noncomputable def subgraphTripleFinset :
    Finset (Finset VertexId × Multiset FeynmanEdge × Multiset ExternalLeg) :=
  G.vertices.powerset ×ˢ
    (G.internalEdges.powerset.toFinset ×ˢ G.externalLegs.powerset.toFinset)

private theorem mem_subgraphTripleFinset (γ : FeynmanSubgraph G) :
    γ.toTriple ∈ G.subgraphTripleFinset := by
  unfold subgraphTripleFinset FeynmanSubgraph.toTriple
  simp [Finset.mem_product, Multiset.mem_toFinset, Multiset.mem_powerset]
  exact ⟨γ.vertices_subset, γ.internalEdges_le, γ.externalLegs_le⟩

end FeynmanGraph

/-- Inject a subgraph into the Finset-subtype of admissible triples. -/
private def FeynmanSubgraph.toTripleSubtype (γ : FeynmanSubgraph G) :
    { t // t ∈ G.subgraphTripleFinset } :=
  ⟨γ.toTriple, FeynmanGraph.mem_subgraphTripleFinset G γ⟩

private theorem FeynmanSubgraph.toTripleSubtype_injective :
    Function.Injective (FeynmanSubgraph.toTripleSubtype : FeynmanSubgraph G → _) := by
  intro γ₁ γ₂ h
  apply FeynmanSubgraph.toTriple_injective
  exact congrArg Subtype.val h

/-- **Concrete `Fintype (FeynmanSubgraph G)` instance.** Discharges the
Path-cut hypothesis that was carried since Sprint C2 Phase A.

Built via `Fintype.ofInjective` on a subgraph → `{t // t ∈ subgraphTripleFinset}`
injection. The codomain has automatic `Fintype` because it is a
subtype of a `Finset.attach`-style subset. -/
noncomputable instance FeynmanSubgraph.fintype (G : FeynmanGraph) :
    Fintype (FeynmanSubgraph G) :=
  Fintype.ofInjective FeynmanSubgraph.toTripleSubtype
    FeynmanSubgraph.toTripleSubtype_injective

end GaugeGeometry.QFT.Combinatorial
