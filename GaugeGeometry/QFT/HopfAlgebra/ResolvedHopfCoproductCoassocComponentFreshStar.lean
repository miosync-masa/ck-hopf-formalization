import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCanonicalStarFacts

/-!
# R-6c-body-414 — the canonical resolved component-fresh star allocator (PROVED)

Four-hundred-and-fourteenth genuine-body step — the first *actual inhabitant* on the raw-`W` side.  Bodies 405–413
closed the strict-star no-go repair arc: the correcting permutation `τ` absorbs any component-ordering relabeling, so the
star allocator no longer has to be `mapPerm`-natural.  This body banks the concrete allocator that exploits exactly that
freedom: the resolved mirror of the flat `AdmissibleSubgraph.componentFreshStar` — place each component's star just above
the ambient vertex range, indexed by the component's position in the finite carrier.

* `resolvedComponentFreshStar` — `freshVertex G.vertices + (position of γ in A.elements.toList)`;
* `resolvedComponentFreshStar_not_mem_vertices` — freshness (ambient vertices are `< freshVertex`, stars are `≥`);
* `resolvedComponentFreshStar_injective_on_elements` — injectivity (`Nat.add_left_cancel` → `List.idxOf_inj`);
* `ResolvedCanonicalRawStarAllocatorSupply` — the standalone (`R`-free) star-allocator package;
* `canonicalResolvedStarAllocator` — the canonical inhabitant.

**Payoff (why this is only possible post-405).**  This allocator is deliberately NOT `mapPerm`-natural — the fresh
offset depends on the ambient `sup` and the carrier's list order, both of which move under relabeling.  Before body-405
that would have been unusable (the coproduct needed strict star equivariance); now the pipeline is `local fresh/injective
allocator → correcting permutation τ → rightTerm_mapPerm`, so a relabeling-sensitive ordering is harmless.  This is the
concrete dividend of the alpha migration.

Per the HALT: the raw-`W` `index` / `hCD` / `carrier_mapPerm` are NOT built; `canonicalCover` is NOT fabricated to
`∀ G`; NO claim that raw `W` is complete.  This body delivers only the `starOf` half (a genuine inhabitant).  No facade,
no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

set_option linter.unusedSectionVars false

/-- **R-6c-body-414 — the canonical resolved component-star allocator.**  Places each component's star just above the
ambient vertex range, indexed by its position in the finite carrier's list. -/
noncomputable def resolvedComponentFreshStar (G : ResolvedFeynmanGraph)
    (A : ResolvedAdmissibleSubgraph G) (γ : ResolvedFeynmanSubgraph G) : VertexId :=
  FeynmanGraph.freshVertex G.vertices + A.elements.toList.idxOf γ

/-- **R-6c-body-414 — the allocated star is fresh** (outside the ambient vertices). -/
theorem resolvedComponentFreshStar_not_mem_vertices (G : ResolvedFeynmanGraph)
    (A : ResolvedAdmissibleSubgraph G) (γ : ResolvedFeynmanSubgraph G) :
    resolvedComponentFreshStar G A γ ∉ G.vertices := by
  intro hmem
  have hlt : resolvedComponentFreshStar G A γ < FeynmanGraph.freshVertex G.vertices := by
    unfold resolvedComponentFreshStar
    exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hmem)
  have hle : FeynmanGraph.freshVertex G.vertices ≤ resolvedComponentFreshStar G A γ := by
    unfold resolvedComponentFreshStar
    exact Nat.le_add_right _ _
  exact (Nat.not_lt_of_ge hle) hlt

/-- **R-6c-body-414 — distinct components get distinct stars.**  `Nat.add_left_cancel` strips the common fresh offset,
then `List.idxOf_inj` (on a member) gives injectivity of the list-position index. -/
theorem resolvedComponentFreshStar_injective_on_elements (G : ResolvedFeynmanGraph)
    (A : ResolvedAdmissibleSubgraph G) {η δ : ResolvedFeynmanSubgraph G}
    (hη : η ∈ A.elements) (_hδ : δ ∈ A.elements)
    (hstar : resolvedComponentFreshStar G A η = resolvedComponentFreshStar G A δ) : η = δ := by
  unfold resolvedComponentFreshStar at hstar
  have hidx : A.elements.toList.idxOf η = A.elements.toList.idxOf δ := Nat.add_left_cancel hstar
  exact (List.idxOf_inj (l := A.elements.toList) (x := η) (y := δ)
    (Finset.mem_toList.mpr hη)).mp hidx

/-- **R-6c-body-414 — the standalone raw star-allocator package.**  A per-`(G, A)` star assignment with the two
canonical-star facts (freshness + injectivity), NOT tied to any carrier `R` and NOT `mapPerm`-natural — exactly the shape
the correcting-permutation pipeline consumes. -/
structure ResolvedCanonicalRawStarAllocatorSupply where
  /-- The star assignment per forest. -/
  starOf : (G : ResolvedFeynmanGraph) → ResolvedAdmissibleSubgraph G →
    (ResolvedFeynmanSubgraph G → VertexId)
  /-- The allocated star is fresh for each component of `A`. -/
  starOf_fresh : ∀ (G : ResolvedFeynmanGraph) (A : ResolvedAdmissibleSubgraph G)
    (η : ResolvedFeynmanSubgraph G), η ∈ A.elements → starOf G A η ∉ G.vertices
  /-- Distinct components of `A` get distinct stars. -/
  starOf_injective : ∀ (G : ResolvedFeynmanGraph) (A : ResolvedAdmissibleSubgraph G)
    {η δ : ResolvedFeynmanSubgraph G}, η ∈ A.elements → δ ∈ A.elements →
      starOf G A η = starOf G A δ → η = δ

/-- **R-6c-body-414 ∎ — the canonical inhabitant** of the raw star allocator, from the component-fresh star. -/
noncomputable def canonicalResolvedStarAllocator : ResolvedCanonicalRawStarAllocatorSupply where
  starOf := fun G A => resolvedComponentFreshStar G A
  starOf_fresh := fun G A η _hη => resolvedComponentFreshStar_not_mem_vertices G A η
  starOf_injective := fun G A => resolvedComponentFreshStar_injective_on_elements G A

end GaugeGeometry.QFT.Combinatorial
