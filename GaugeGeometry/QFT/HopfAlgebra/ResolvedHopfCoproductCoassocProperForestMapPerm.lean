import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSubgraphFintype

/-!
# R-6c-body-416 — `mapPerm`-naturality of `IsProperForest` (PROVED)

Four-hundred-and-sixteenth genuine-body step — the naturality half of the saturated-carrier programme.  Body-415 built
the finiteness floor (`Fintype (ResolvedFeynmanSubgraph G)`) and the ambient-parametric `saturatedProperForestIndex`;
its `carrier_mapPerm` needs to know that `IsProperForest` is stable under relabeling.  This body proves exactly that,
as a two-sided `iff`.

Each of the five `IsProperForest` conjuncts transports because relabeling preserves the relevant cardinalities /
nonemptiness:

* `A.IsNonempty` (`A.elements.Nonempty`) — `mapPerm_elements` + `Finset.image_nonempty`;
* `A.HasNonemptyComponents` (`∀ γ ∈ elements, 0 < γ.vertexCount`) — `Finset.forall_mem_image` + `mapPerm_vertices` +
  `Finset.card_image_of_injective σ.injective`;
* `0 < A.internalEdges.card` — `mapPerm_internalEdges` + `Multiset.card_map`;
* `A.HasPositiveInternalEdgesComponents` — `forall_mem_image` + `mapPerm_internalEdges` (component level);
* `0 < A.complementEdges.card` — `mapPerm_complementEdges` + `Multiset.card_map`.

The `iff` is proved DIRECTLY, conjunct-by-conjunct (`simp only` bridges the `DecidableEq ResolvedFeynmanSubgraph`
diamond) — no `σ.symm` round-trip and NO dependent graph-cancel is needed here.

* `isProperForest_mapPerm_iff` — `(A.mapPerm σ).IsProperForest ↔ A.IsProperForest`;
* `isProperForest_mapPerm` — the forward transport (the `.mpr`, banked for readability).

Per the HALT: `saturatedProperForestIndex`'s `carrier_mapPerm` is NOT built here — it additionally needs the
`ResolvedAdmissibleSubgraph.mapPerm` SURJECTIVITY (`∃ B, B.mapPerm σ = A`), i.e. the dependent graph-cancel
`(G.mapPerm σ).mapPerm σ.symm = G` transported through the subgraph — a substantial step bundled with the RawW
assembly (body-417).  `hCD` / the CD-emptying (`cdSupportedIndex`) are also body-417.  No facade, no flat term, no
`forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

set_option linter.unusedSectionVars false

/-- **R-6c-body-416 ∎ — `IsProperForest` is `mapPerm`-invariant.**  Proved directly, conjunct-by-conjunct; each of the
five properness conditions is a cardinality / nonemptiness that relabeling preserves. -/
theorem isProperForest_mapPerm_iff {G : ResolvedFeynmanGraph} (σ : Equiv.Perm VertexId)
    (A : ResolvedAdmissibleSubgraph G) :
    (A.mapPerm σ).IsProperForest ↔ A.IsProperForest := by
  simp only [ResolvedAdmissibleSubgraph.IsProperForest, ResolvedAdmissibleSubgraph.IsNonempty,
    ResolvedAdmissibleSubgraph.HasNonemptyComponents,
    ResolvedAdmissibleSubgraph.HasPositiveInternalEdgesComponents,
    ResolvedAdmissibleSubgraph.mapPerm_elements, ResolvedAdmissibleSubgraph.mapPerm_internalEdges,
    ResolvedAdmissibleSubgraph.mapPerm_complementEdges, Multiset.card_map,
    Finset.image_nonempty, Finset.forall_mem_image, ResolvedFeynmanSubgraph.IsNonempty,
    ResolvedFeynmanSubgraph.vertexCount, ResolvedFeynmanSubgraph.mapPerm_vertices,
    ResolvedFeynmanSubgraph.mapPerm_internalEdges,
    Finset.card_image_of_injective _ σ.injective]

/-- **R-6c-body-416 — the forward properness transport** (`.mpr` of the naturality `iff`). -/
theorem isProperForest_mapPerm {G : ResolvedFeynmanGraph} (σ : Equiv.Perm VertexId)
    {A : ResolvedAdmissibleSubgraph G} (h : A.IsProperForest) : (A.mapPerm σ).IsProperForest :=
  (isProperForest_mapPerm_iff σ A).mpr h

end GaugeGeometry.QFT.Combinatorial
