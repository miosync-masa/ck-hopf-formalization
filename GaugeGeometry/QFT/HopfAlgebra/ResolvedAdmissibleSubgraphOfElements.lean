import GaugeGeometry.QFT.Combinatorial.ResolvedSubGraph

/-!
# R-6c-support-1 — resolved admissible-subgraph constructors (`ofElements`, `union`)

The missing resolved infrastructure for the coassoc de-contraction (R-6c-4f part 3c-1 scout): the flat
selected-outer forest is `AdmissibleSubgraph.ofElements (left.elements ∪ promoted)`, but the resolved
side lacked an `ofElements` constructor and a `union`.  This file supplies them.

`ResolvedAdmissibleSubgraph` is just `{ elements, isConnectedDivergent, pairwiseDisjoint }`, so
`ofElements` is the named constructor from a component set with its CD + pairwise-disjointness, and
`union` glues two forests whose cross components are disjoint.

Landed:

* `ResolvedAdmissibleSubgraph.ofElements` (+ `ofElements_elements` simp);
* `ResolvedAdmissibleSubgraph.union` (+ `union_elements` simp) — union of two forests with a
  cross-disjointness hypothesis.

No facade, no flat term, no `forgetHopf`.  The forest-promote analogue (the other missing block) is a
separate sub-track.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

variable [∀ H : FeynmanGraph, DivergenceMeasure H]

namespace ResolvedAdmissibleSubgraph

variable {G : ResolvedFeynmanGraph}

/-- **R-6c-support-1 — the resolved admissible subgraph from a component set.**  A finite set of
resolved subgraphs that are connected-divergent (under `forget`) and pairwise disjoint. -/
def ofElements (S : Finset (ResolvedFeynmanSubgraph G))
    (hCD : ∀ γ ∈ S, γ.forget.IsConnectedDivergent)
    (hDisj : ∀ ⦃γ⦄, γ ∈ S → ∀ ⦃δ⦄, δ ∈ S → γ ≠ δ → γ.Disjoint δ) :
    ResolvedAdmissibleSubgraph G where
  elements := S
  isConnectedDivergent := hCD
  pairwiseDisjoint := hDisj

@[simp] theorem ofElements_elements (S : Finset (ResolvedFeynmanSubgraph G))
    (hCD : ∀ γ ∈ S, γ.forget.IsConnectedDivergent)
    (hDisj : ∀ ⦃γ⦄, γ ∈ S → ∀ ⦃δ⦄, δ ∈ S → γ ≠ δ → γ.Disjoint δ) :
    (ofElements S hCD hDisj).elements = S := rfl

/-- **R-6c-support-1 — the union of two admissible subgraphs.**  Given that every component of `A` is
disjoint from every distinct component of `B`, the union of their component sets is admissible. -/
noncomputable def union (A B : ResolvedAdmissibleSubgraph G)
    (hCross : ∀ γ ∈ A.elements, ∀ δ ∈ B.elements, γ ≠ δ → γ.Disjoint δ) :
    ResolvedAdmissibleSubgraph G :=
  ofElements (A.elements ∪ B.elements)
    (by
      intro γ hγ
      rcases Finset.mem_union.mp hγ with h | h
      · exact A.isConnectedDivergent γ h
      · exact B.isConnectedDivergent γ h)
    (by
      intro γ hγ δ hδ hne
      rcases Finset.mem_union.mp hγ with hγA | hγB <;>
        rcases Finset.mem_union.mp hδ with hδA | hδB
      · exact A.pairwiseDisjoint hγA hδA hne
      · exact hCross γ hγA δ hδB hne
      · exact (hCross δ hδA γ hγB hne.symm).symm
      · exact B.pairwiseDisjoint hγB hδB hne)

@[simp] theorem union_elements (A B : ResolvedAdmissibleSubgraph G)
    (hCross : ∀ γ ∈ A.elements, ∀ δ ∈ B.elements, γ ≠ δ → γ.Disjoint δ) :
    (A.union B hCross).elements = A.elements ∪ B.elements := rfl

/-- **R-6c-support-3 — the sub-forest of `A` cut out by a predicate.**  The components of `A`
satisfying `P`; CD and pairwise-disjointness are inherited from `A`. -/
def filterElements (A : ResolvedAdmissibleSubgraph G) (P : ResolvedFeynmanSubgraph G → Prop)
    [DecidablePred P] : ResolvedAdmissibleSubgraph G :=
  ofElements (A.elements.filter P)
    (fun γ hγ => A.isConnectedDivergent γ (Finset.mem_of_mem_filter γ hγ))
    (fun _ hγ _ hδ hne =>
      A.pairwiseDisjoint (Finset.mem_of_mem_filter _ hγ) (Finset.mem_of_mem_filter _ hδ) hne)

@[simp] theorem filterElements_elements (A : ResolvedAdmissibleSubgraph G)
    (P : ResolvedFeynmanSubgraph G → Prop) [DecidablePred P] :
    (A.filterElements P).elements = A.elements.filter P := rfl

end ResolvedAdmissibleSubgraph

end GaugeGeometry.QFT.Combinatorial
