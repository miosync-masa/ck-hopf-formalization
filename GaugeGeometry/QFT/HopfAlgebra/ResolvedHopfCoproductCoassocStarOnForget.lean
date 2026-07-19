import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForgetInjOn
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocComponentFreshStar

/-!
# R-6c-body-420 — descending the resolved fresh star onto the flat forest (PROVED)

Four-hundred-and-twentieth genuine-body step — the resolved→flat structural correspondence for the `hCD` impedance
match.  Body-419 proved `forget` is injective on a proper forest's components, so the components of `A` correspond
bijectively to those of `A.forget`.  This body uses that bijection to DESCEND body-414's resolved fresh-star allocator
onto `A.forget`'s (flat) components, and records the two structural equalities that pin the descent — the honest
"same contraction, star names on the flat side" step, without yet touching the flat CANONICAL star.

* `resolvedStarOnForget` — the flat star `FeynmanSubgraph G.forget → VertexId` from the resolved allocator (defined on
  the component-membership branch via the unique preimage, extended by `dite`);
* `resolvedStarOnForget_spec` — the core spec `resolvedStarOnForget A δ.forget = resolvedComponentFreshStar G A δ`
  (uniqueness of the preimage is exactly body-419's injectivity);
* `forget_vertices_eq` — `A.forget.vertices = A.vertices` (`forget` preserves component vertices; `biUnion` over the
  image collapses back).

Per the HALT: the full graph equality `(A.contractWithStars resolvedStar).forget = A.forget.contractWithStars
resolvedStarOnForget` (the `retargetVertex` agreement via the `componentAt` correspondence + the three fields) is the
next body (421); the star-RENAMING to the flat canonical star (a `σ = id`-specialised correcting permutation between two
fresh flat allocators) and the final `hCD` + RawW assembly follow.  Responsibility here is limited to the component
correspondence + `forget` processing.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` /
singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

set_option linter.unusedSectionVars false

/-- **R-6c-body-420 — the resolved fresh star, descended onto `A.forget`'s components.**  On a flat component `η ∈
A.forget.elements` it returns the resolved star of `η`'s (unique, by body-419) resolved preimage; off the forest it is
irrelevant (`dite`). -/
noncomputable def resolvedStarOnForget {G : ResolvedFeynmanGraph} (A : ResolvedAdmissibleSubgraph G)
    (η : FeynmanSubgraph G.forget) : VertexId :=
  if h : η ∈ A.forget.elements then
    resolvedComponentFreshStar G A (Finset.mem_image.mp h).choose
  else 0

/-- **R-6c-body-420 — the core spec.**  On a forgotten component `δ.forget` the descended star is exactly the resolved
star of `δ` — the preimage is pinned by body-419's forget-injectivity. -/
theorem resolvedStarOnForget_spec {G : ResolvedFeynmanGraph} (A : ResolvedAdmissibleSubgraph G)
    (hpf : A.IsProperForest) {δ : ResolvedFeynmanSubgraph G} (hδ : δ ∈ A.elements) :
    resolvedStarOnForget A δ.forget = resolvedComponentFreshStar G A δ := by
  have hmem : δ.forget ∈ A.forget.elements := by
    rw [ResolvedAdmissibleSubgraph.forget_elements]; exact Finset.mem_image_of_mem _ hδ
  rw [resolvedStarOnForget, dif_pos hmem]
  congr 1
  obtain ⟨hchoose_mem, hchoose_eq⟩ := (Finset.mem_image.mp hmem).choose_spec
  exact forget_injOn_elements_of_isProperForest A hpf hchoose_mem hδ hchoose_eq

/-- **R-6c-body-420 — the forgotten forest covers the same vertices.**  `forget` preserves each component's vertices, and
the `biUnion` over the forgetful image collapses back to `A`'s. -/
theorem forget_vertices_eq {G : ResolvedFeynmanGraph} (A : ResolvedAdmissibleSubgraph G) :
    A.forget.vertices = A.vertices := by
  ext v
  simp only [AdmissibleSubgraph.vertices, ResolvedAdmissibleSubgraph.vertices, Finset.mem_biUnion,
    ResolvedAdmissibleSubgraph.forget_elements, Finset.mem_image]
  constructor
  · rintro ⟨η, ⟨γ, hγ, rfl⟩, hv⟩
    exact ⟨γ, hγ, by rwa [ResolvedFeynmanSubgraph.forget_vertices] at hv⟩
  · rintro ⟨γ, hγ, hv⟩
    exact ⟨γ.forget, ⟨γ, hγ, rfl⟩, by rwa [ResolvedFeynmanSubgraph.forget_vertices]⟩

end GaugeGeometry.QFT.Combinatorial
