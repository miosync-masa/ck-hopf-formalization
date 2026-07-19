import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCDSupportedIndex

/-!
# R-6c-body-419 — forget-injectivity on proper-forest components (PROVED, the matching crux)

Four-hundred-and-nineteenth genuine-body step — the first, load-bearing lemma of the resolved↔flat contraction
impedance-match that body-418 identified as the last obstacle to the raw-`W` `hCD`.  The `hCD` needs
`(A.contractWithStars (canonicalResolvedStarAllocator.starOf G A)).forget.toClass.IsConnectedDivergent`; the only
derivation is the FLAT `admissibleForestCanonicalContractGraph_hCD_of_ambient_preservation` over `A.forget` with the flat
canonical star.  Matching the resolved contraction to the flat one hinges on the components of `A` corresponding
bijectively to the components of `A.forget` — i.e. the forgetful map is INJECTIVE on `A.elements`.

That injectivity is NOT a blanket `forget`-injectivity assumption (the guard body-418 flagged): it is DERIVED from the
proper-forest data.  Two distinct components are `pairwiseDisjoint` (disjoint vertex sets), so if their forgets agreed
their (shared) vertex set would be both nonempty (`HasNonemptyComponents`) and self-disjoint — impossible.

* `forget_injOn_elements_of_isProperForest` — the pointwise statement (`γ.forget = δ.forget → γ = δ` on `A.elements`);
* `forget_setInjOn_elements_of_isProperForest` — the `Set.InjOn` repackaging (for `Finset.image` bijection lemmas
  downstream).

Per the HALT: this is only the component-correspondence crux.  The remaining match — `(A.contractWithStars resolvedStar)
.forget` reduced to a flat `A.forget.contractWithStars` (via `forget_contractWithStars`), the two fresh star sets
(`resolvedComponentFreshStar` vs flat `componentFreshStar`) related by a correcting permutation, the resulting class
equality, then the flat CD + iso-invariance giving `hCD`, and finally the RawW record assembly + real supported `W` — is
the continuation (body-420+).  It reuses the 403–413 correcting-permutation machinery, now between two fresh flat star
allocators.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

set_option linter.unusedSectionVars false

/-- **R-6c-body-419 — the forgetful map is injective on a proper forest's components.**  Derived from
`pairwiseDisjoint` + `HasNonemptyComponents` (NOT a blanket `forget`-injectivity): equal forgets force equal vertex
sets, which for disjoint nonempty components is a contradiction. -/
theorem forget_injOn_elements_of_isProperForest {G : ResolvedFeynmanGraph}
    (A : ResolvedAdmissibleSubgraph G) (h : A.IsProperForest)
    {γ δ : ResolvedFeynmanSubgraph G} (hγ : γ ∈ A.elements) (hδ : δ ∈ A.elements)
    (hfg : γ.forget = δ.forget) : γ = δ := by
  by_contra hne
  have hdisj : γ.Disjoint δ := A.pairwiseDisjoint hγ hδ hne
  have hv : γ.vertices = δ.vertices := by
    have := congrArg FeynmanSubgraph.vertices hfg
    simpa only [ResolvedFeynmanSubgraph.forget_vertices] using this
  have hδne : δ.vertices.Nonempty := by
    rw [← Finset.card_pos]; exact h.2.1 δ hδ
  obtain ⟨v, hvmem⟩ := hδne
  unfold ResolvedFeynmanSubgraph.Disjoint at hdisj
  rw [hv] at hdisj
  exact Finset.disjoint_left.mp hdisj hvmem hvmem

/-- **R-6c-body-419 — the `Set.InjOn` repackaging** (for `Finset.image` bijection lemmas: `A.elements ↔ A.forget`'s
components). -/
theorem forget_setInjOn_elements_of_isProperForest {G : ResolvedFeynmanGraph}
    (A : ResolvedAdmissibleSubgraph G) (h : A.IsProperForest) :
    Set.InjOn ResolvedFeynmanSubgraph.forget (A.elements : Set (ResolvedFeynmanSubgraph G)) :=
  fun _ hγ _ hδ hfg =>
    forget_injOn_elements_of_isProperForest A h (Finset.mem_coe.mp hγ) (Finset.mem_coe.mp hδ) hfg

end GaugeGeometry.QFT.Combinatorial
