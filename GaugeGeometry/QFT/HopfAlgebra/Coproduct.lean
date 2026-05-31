import GaugeGeometry.QFT.HopfAlgebra.StrictGenerators
import GaugeGeometry.QFT.Combinatorial.SubGraph

/-!
# Coproduct on `HopfH`  [Sprint C2 Phase A]

This file sets up the Connes–Kreimer coproduct

```
Δ([Γ]) = [Γ] ⊗ 1 + 1 ⊗ [Γ] + ∑_{γ ⊊ Γ, γ ∈ ConnectedDivergentSubgraphs} [γ] ⊗ [Γ/γ]
```

extending multiplicatively via `MvPolynomial.aeval` to all of `HopfH`.

## Phase A / Phase B / Phase C split (Sprint C2, 2026-04-24)

* **Phase A** (this file — H4.1 / H4.2 / H4.3 body + H4.5 unfold):
  index set, recursion body, and a `coproductGen_eq` unfold equation.
* **Phase B** (H4.6, deferred pending strategist cost reassessment):
  isomorphism invariance of `coproductGen`.
* **Phase C** (H4.7–H4.11): class-lift + extend to
  `coproduct : HopfH →ₐ[ℚ] HopfH ⊗[ℚ] HopfH` via `MvPolynomial.aeval`.

## Path-cut: `Fintype (FeynmanSubgraph G)` carried as hypothesis

The concrete `Fintype (FeynmanSubgraph G)` instance (via triple-injection
into ambient-finite `(Finset × Multiset × Multiset)`) requires 30–50
lines of Mathlib-API wiring for Subtype-fintype combinators,
disproportionate to the mathematical triviality.

**Path-cut adopted (2026-04-24, strategist-approved):** carry
`[∀ G, Fintype (FeynmanSubgraph G)]` as a `variable` hypothesis at
the Phase A level, matching Sprint C1's Path-W pattern.

**Supply commitment (recorded in HOPF_DECOMPOSITION.md § H4):** the
concrete `Fintype` instance is supplied before Sprint D completion.

## Recursion target: `HopfH_temp ⊗[ℚ] HopfH_temp`

The recursion lands in the Sprint B' scaffold tensor square. Generators
`[γ]` for `γ : FeynmanSubgraph G` enter as `gen_temp` of a `HopfGenTemp`
element whose `IsSupportConnected` witness comes from γ's connectivity.

The strict `HopfH` version is obtained in Phase C via the bridge
`HopfH ↪ HopfH_temp` (Sprint C1's `bridge`, H3.9). This mirrors Sprint
A's `contractWith → contract` pattern.
-/

open scoped TensorProduct

namespace GaugeGeometry.QFT.Combinatorial

/-! ### Prep: `IsNonempty` from internal-edge count

A subgraph with at least one internal edge has at least one vertex
(the edge's endpoints are in the subgraph's vertices by
`edges_supported`). Mechanical helper used by `edgeMeasure_contract_lt`.
-/

namespace FeynmanSubgraph

variable {G : FeynmanGraph}

/-- A subgraph with `0 < internalEdges.card` is nonempty: an edge
pins its endpoints inside the subgraph's vertex set. -/
theorem isNonempty_of_internalEdges_pos {γ : FeynmanSubgraph G}
    (h : 0 < γ.internalEdges.card) : γ.IsNonempty := by
  rw [Multiset.card_pos] at h
  rcases Multiset.exists_mem_of_ne_zero h with ⟨e, he⟩
  have hsupp := γ.edges_supported e he
  unfold IsNonempty vertexCount
  rw [Finset.card_pos]
  refine ⟨e.source, ?_⟩
  simp [FeynmanEdge.SupportedOn] at hsupp
  exact hsupp.1

/-- Data-field equality implies subgraph equality (proof fields are
proof-irrelevant). -/
theorem ext_iff {γ₁ γ₂ : FeynmanSubgraph G} :
    γ₁ = γ₂ ↔
      γ₁.vertices = γ₂.vertices ∧
      γ₁.internalEdges = γ₂.internalEdges ∧
      γ₁.externalLegs = γ₂.externalLegs := by
  constructor
  · intro h; subst h; exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨hV, hI, hE⟩
    cases γ₁; cases γ₂
    simp_all

end FeynmanSubgraph

/-! ### H4.1 — the index set `properConnectedDivergentSubgraphs` -/

namespace FeynmanGraph

variable (G : FeynmanGraph)

/--
**H4.1** — The Connes–Kreimer coproduct sum ranges over *proper*
(i.e. strictly smaller than the ambient) connected 1PI divergent
subgraphs having at least one internal edge.

The "one internal edge" condition is the physical requirement
(divergent 1PI subgraphs with no internal lines are excluded) that
gives `edgeMeasure_contract_lt` (H1.WF.3 analogue) at every recursive
call via `isNonempty_of_internalEdges_pos`.  The complement-edge condition is
the literal properness requirement used by the strict forest summand: the
subgraph must leave a nonempty remnant in the ambient graph.

Carries `Fintype (FeynmanSubgraph G)` as an instance hypothesis —
see the module docstring.
-/
noncomputable def properConnectedDivergentSubgraphs
    [DivergenceMeasure G] [Fintype (FeynmanSubgraph G)] :
    Finset (FeynmanSubgraph G) :=
  (Finset.univ : Finset (FeynmanSubgraph G)).filter fun γ =>
    γ.IsConnectedDivergent ∧ 0 < γ.internalEdges.card ∧
      0 < γ.complementEdges.card

@[simp] theorem mem_properConnectedDivergentSubgraphs
    [DivergenceMeasure G] [Fintype (FeynmanSubgraph G)]
    (γ : FeynmanSubgraph G) :
    γ ∈ G.properConnectedDivergentSubgraphs ↔
      γ.IsConnectedDivergent ∧ 0 < γ.internalEdges.card ∧
        0 < γ.complementEdges.card := by
  unfold properConnectedDivergentSubgraphs
  simp

theorem properConnectedDivergentSubgraphs_isConnectedDivergent
    [DivergenceMeasure G] [Fintype (FeynmanSubgraph G)]
    {γ : FeynmanSubgraph G}
    (hγ : γ ∈ G.properConnectedDivergentSubgraphs) :
    γ.IsConnectedDivergent :=
  ((G.mem_properConnectedDivergentSubgraphs γ).mp hγ).1

theorem properConnectedDivergentSubgraphs_internalEdges_pos
    [DivergenceMeasure G] [Fintype (FeynmanSubgraph G)]
    {γ : FeynmanSubgraph G}
    (hγ : γ ∈ G.properConnectedDivergentSubgraphs) :
    0 < γ.internalEdges.card :=
  (((G.mem_properConnectedDivergentSubgraphs γ).mp hγ).2).1

theorem properConnectedDivergentSubgraphs_complementEdges_pos
    [DivergenceMeasure G] [Fintype (FeynmanSubgraph G)]
    {γ : FeynmanSubgraph G}
    (hγ : γ ∈ G.properConnectedDivergentSubgraphs) :
    0 < γ.complementEdges.card :=
  (((G.mem_properConnectedDivergentSubgraphs γ).mp hγ).2).2

/-! ### Full forest-admissible finite carrier

This is not yet the coproduct index: it includes all connected-divergent
forests and leaves nonempty/proper/disjoint-union refinements to later
passes. It gives the finite carrier that will replace the conservative
singleton-only index below.
-/

/-- Finite carrier of all admissible subgraphs represented by
connected-divergent forests. -/
noncomputable def admissibleDivergentSubgraphs
    [DivergenceMeasure G] [Fintype (FeynmanSubgraph G)] :
    Finset (AdmissibleSubgraph G) :=
  AdmissibleSubgraph.connectedDivergentIndex G

/-- Every currently-defined admissible subgraph belongs to the full finite
admissible carrier. -/
theorem mem_admissibleDivergentSubgraphs
    [DivergenceMeasure G] [Fintype (FeynmanSubgraph G)]
    (A : AdmissibleSubgraph G) :
    A ∈ G.admissibleDivergentSubgraphs := by
  unfold admissibleDivergentSubgraphs
  exact AdmissibleSubgraph.mem_connectedDivergentIndex G A

/-- Singleton connected-divergent subgraphs belong to the full finite
admissible carrier. -/
theorem singleton_mem_admissibleDivergentSubgraphs
    [DivergenceMeasure G] [Fintype (FeynmanSubgraph G)]
    {γ : FeynmanSubgraph G} (hγ : γ.IsConnectedDivergent) :
    AdmissibleSubgraph.singleton γ hγ ∈ G.admissibleDivergentSubgraphs :=
  G.mem_admissibleDivergentSubgraphs (AdmissibleSubgraph.singleton γ hγ)

/-- Finite carrier of disjoint admissible subgraphs. This is still not the
final coproduct index: nonempty/proper refinements are intentionally
separate filters for later passes. -/
noncomputable def disjointAdmissibleDivergentSubgraphs
    [DivergenceMeasure G] [Fintype (FeynmanSubgraph G)] :
    Finset (AdmissibleSubgraph G) := by
  classical
  exact G.admissibleDivergentSubgraphs.filter
    (fun A => A.IsPairwiseDisjoint)

@[simp] theorem mem_disjointAdmissibleDivergentSubgraphs
    [DivergenceMeasure G] [Fintype (FeynmanSubgraph G)]
    (A : AdmissibleSubgraph G) :
    A ∈ G.disjointAdmissibleDivergentSubgraphs ↔
      A ∈ G.admissibleDivergentSubgraphs ∧ A.IsPairwiseDisjoint := by
  classical
  unfold disjointAdmissibleDivergentSubgraphs
  simp

/-- Singleton connected-divergent subgraphs belong to the disjoint
admissible carrier. -/
theorem singleton_mem_disjointAdmissibleDivergentSubgraphs
    [DivergenceMeasure G] [Fintype (FeynmanSubgraph G)]
    {γ : FeynmanSubgraph G} (hγ : γ.IsConnectedDivergent) :
    AdmissibleSubgraph.singleton γ hγ ∈
      G.disjointAdmissibleDivergentSubgraphs := by
  rw [G.mem_disjointAdmissibleDivergentSubgraphs]
  exact ⟨G.singleton_mem_admissibleDivergentSubgraphs hγ,
    AdmissibleSubgraph.singleton_isPairwiseDisjoint γ hγ⟩

/-! ### Nonempty disjoint admissible finite carrier

This still does not impose the final properness condition, but it removes the
empty forest while keeping the index wide enough for disjoint unions.
-/

/-- Finite carrier of nonempty disjoint admissible subgraphs. Properness is
kept as a later filter. -/
noncomputable def nonemptyDisjointAdmissibleDivergentSubgraphs
    [DivergenceMeasure G] [Fintype (FeynmanSubgraph G)] :
    Finset (AdmissibleSubgraph G) := by
  classical
  exact G.disjointAdmissibleDivergentSubgraphs.filter
    (fun A => A.IsNonempty)

@[simp] theorem mem_nonemptyDisjointAdmissibleDivergentSubgraphs
    [DivergenceMeasure G] [Fintype (FeynmanSubgraph G)]
    (A : AdmissibleSubgraph G) :
    A ∈ G.nonemptyDisjointAdmissibleDivergentSubgraphs ↔
      A ∈ G.disjointAdmissibleDivergentSubgraphs ∧ A.IsNonempty := by
  classical
  unfold nonemptyDisjointAdmissibleDivergentSubgraphs
  simp

/-- Singleton connected-divergent subgraphs belong to the nonempty disjoint
admissible carrier. -/
theorem singleton_mem_nonemptyDisjointAdmissibleDivergentSubgraphs
    [DivergenceMeasure G] [Fintype (FeynmanSubgraph G)]
    {γ : FeynmanSubgraph G} (hγ : γ.IsConnectedDivergent) :
    AdmissibleSubgraph.singleton γ hγ ∈
      G.nonemptyDisjointAdmissibleDivergentSubgraphs := by
  rw [G.mem_nonemptyDisjointAdmissibleDivergentSubgraphs]
  exact ⟨G.singleton_mem_disjointAdmissibleDivergentSubgraphs hγ,
    AdmissibleSubgraph.singleton_isNonempty γ hγ⟩

/-! ### Proper disjoint admissible finite carrier

This is the first finite carrier with the intended forest shape for the
nontrivial CK summand: nonempty, pairwise-disjoint, connected-divergent
components, each component has a nonempty vertex carrier and at least one
internal edge, and the union has at least one internal edge. The old
`properAdmissibleDivergentSubgraphs` below remains the conservative
singleton-only subindex until the right tensor factor is upgraded fully.
-/

/-- Finite carrier of proper nonempty-component disjoint admissible subgraphs.
This is the target carrier for the genuine forest summand. -/
noncomputable def properDisjointAdmissibleDivergentSubgraphs
    [DivergenceMeasure G] [Fintype (FeynmanSubgraph G)] :
    Finset (AdmissibleSubgraph G) := by
  classical
  exact G.nonemptyDisjointAdmissibleDivergentSubgraphs.filter
    (fun A => A.HasNonemptyComponents ∧ 0 < A.internalEdges.card ∧
      A.HasPositiveInternalEdgesComponents)

@[simp] theorem mem_properDisjointAdmissibleDivergentSubgraphs
    [DivergenceMeasure G] [Fintype (FeynmanSubgraph G)]
    (A : AdmissibleSubgraph G) :
    A ∈ G.properDisjointAdmissibleDivergentSubgraphs ↔
      A ∈ G.nonemptyDisjointAdmissibleDivergentSubgraphs ∧
        A.HasNonemptyComponents ∧
        0 < A.internalEdges.card ∧
        A.HasPositiveInternalEdgesComponents := by
  classical
  unfold properDisjointAdmissibleDivergentSubgraphs
  simp

/-- Singleton connected-divergent subgraphs with at least one internal edge
belong to the proper disjoint admissible carrier. -/
theorem singleton_mem_properDisjointAdmissibleDivergentSubgraphs
    [DivergenceMeasure G] [Fintype (FeynmanSubgraph G)]
    {γ : FeynmanSubgraph G}
    (hγ : γ.IsConnectedDivergent) (hγEdges : 0 < γ.internalEdges.card) :
    AdmissibleSubgraph.singleton γ hγ ∈
      G.properDisjointAdmissibleDivergentSubgraphs := by
  rw [G.mem_properDisjointAdmissibleDivergentSubgraphs]
  exact ⟨G.singleton_mem_nonemptyDisjointAdmissibleDivergentSubgraphs hγ,
    AdmissibleSubgraph.singleton_hasNonemptyComponents
      (FeynmanSubgraph.isNonempty_of_internalEdges_pos hγEdges),
    by simpa using hγEdges,
    AdmissibleSubgraph.singleton_hasPositiveInternalEdgesComponents hγEdges⟩

theorem properDisjointAdmissibleDivergentSubgraphs_isPairwiseDisjoint
    [DivergenceMeasure G] [Fintype (FeynmanSubgraph G)]
    {A : AdmissibleSubgraph G}
    (hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs) :
    A.IsPairwiseDisjoint := by
  have hNonempty :
      A ∈ G.nonemptyDisjointAdmissibleDivergentSubgraphs :=
    ((G.mem_properDisjointAdmissibleDivergentSubgraphs A).mp hA).1
  have hDisjoint :
      A ∈ G.disjointAdmissibleDivergentSubgraphs :=
    ((G.mem_nonemptyDisjointAdmissibleDivergentSubgraphs A).mp hNonempty).1
  exact ((G.mem_disjointAdmissibleDivergentSubgraphs A).mp hDisjoint).2

theorem properDisjointAdmissibleDivergentSubgraphs_hasNonemptyComponents
    [DivergenceMeasure G] [Fintype (FeynmanSubgraph G)]
    {A : AdmissibleSubgraph G}
    (hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs) :
    A.HasNonemptyComponents :=
  (((G.mem_properDisjointAdmissibleDivergentSubgraphs A).mp hA).2).1

theorem properDisjointAdmissibleDivergentSubgraphs_hasPositiveInternalEdgesComponents
    [DivergenceMeasure G] [Fintype (FeynmanSubgraph G)]
    {A : AdmissibleSubgraph G}
    (hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs) :
    A.HasPositiveInternalEdgesComponents :=
  ((((G.mem_properDisjointAdmissibleDivergentSubgraphs A).mp hA).2).2).2

/-! ### Conservative admissible-subgraph index

This is the first finite index for the admissible-subgraph redesign. It
contains only singleton admissible subgraphs, obtained by embedding each
existing connected-divergent coproduct index element as a one-component
forest. The full disjoint finite carrier above is intentionally kept
separate until the summand is replaced by genuine forest contraction.
-/

/-- Conservative singleton-only admissible index, reusing the existing
connected-divergent coproduct index. -/
noncomputable def connectedIndexToAdmissible
    [DivergenceMeasure G] [Fintype (FeynmanSubgraph G)]
    (γ : {γ : FeynmanSubgraph G // γ ∈ G.properConnectedDivergentSubgraphs}) :
    AdmissibleSubgraph G :=
  AdmissibleSubgraph.singleton γ.1
    ((G.mem_properConnectedDivergentSubgraphs γ.1).mp γ.2).1

/-- The singleton embedding of the existing connected index into the
conservative admissible index is injective. -/
theorem connectedIndexToAdmissible_injective
    [DivergenceMeasure G] [Fintype (FeynmanSubgraph G)] :
    Function.Injective (connectedIndexToAdmissible G) := by
  intro γ₁ γ₂ h
  apply Subtype.ext
  exact AdmissibleSubgraph.singleton_injective h

/-- Conservative singleton-only admissible index, reusing the existing
connected-divergent coproduct index. -/
noncomputable def properAdmissibleDivergentSubgraphs
    [DivergenceMeasure G] [Fintype (FeynmanSubgraph G)] :
    Finset (AdmissibleSubgraph G) :=
  G.properConnectedDivergentSubgraphs.attach.image
    (connectedIndexToAdmissible G)

/-- Every existing connected-divergent index element embeds into the
conservative admissible index. -/
theorem singleton_mem_properAdmissibleDivergentSubgraphs
    [DivergenceMeasure G] [Fintype (FeynmanSubgraph G)]
    {γ : FeynmanSubgraph G}
    (hγ : γ ∈ G.properConnectedDivergentSubgraphs) :
    AdmissibleSubgraph.singleton γ
        ((G.mem_properConnectedDivergentSubgraphs γ).mp hγ).1
      ∈ G.properAdmissibleDivergentSubgraphs := by
  unfold properAdmissibleDivergentSubgraphs
  refine Finset.mem_image.mpr ?_
  exact ⟨⟨γ, hγ⟩, by simp, rfl⟩

/-- Membership in the conservative admissible index is witnessed by a
singleton connected-divergent index element. -/
theorem mem_properAdmissibleDivergentSubgraphs_exists_singleton
    [DivergenceMeasure G] [Fintype (FeynmanSubgraph G)]
    {A : AdmissibleSubgraph G}
    (hA : A ∈ G.properAdmissibleDivergentSubgraphs) :
    ∃ γ : FeynmanSubgraph G,
      ∃ hγ : γ ∈ G.properConnectedDivergentSubgraphs,
        A =
          AdmissibleSubgraph.singleton γ
            ((G.mem_properConnectedDivergentSubgraphs γ).mp hγ).1 := by
  unfold properAdmissibleDivergentSubgraphs at hA
  rcases Finset.mem_image.mp hA with ⟨γ, _hγattach, hAeq⟩
  exact ⟨γ.1, γ.2, hAeq.symm⟩

/-- The conservative singleton-only admissible index is contained in the
new finite disjoint admissible carrier. -/
theorem mem_disjointAdmissibleDivergentSubgraphs_of_mem_properAdmissibleDivergentSubgraphs
    [DivergenceMeasure G] [Fintype (FeynmanSubgraph G)]
    {A : AdmissibleSubgraph G}
    (hA : A ∈ G.properAdmissibleDivergentSubgraphs) :
    A ∈ G.disjointAdmissibleDivergentSubgraphs := by
  rcases G.mem_properAdmissibleDivergentSubgraphs_exists_singleton hA with
    ⟨γ, hγ, hAeq⟩
  rw [hAeq]
  exact G.singleton_mem_disjointAdmissibleDivergentSubgraphs
    ((G.mem_properConnectedDivergentSubgraphs γ).mp hγ).1

/-- The conservative singleton-only admissible index is a subindex of the
finite disjoint admissible carrier. -/
theorem properAdmissibleDivergentSubgraphs_subset_disjointAdmissibleDivergentSubgraphs
    [DivergenceMeasure G] [Fintype (FeynmanSubgraph G)] :
    G.properAdmissibleDivergentSubgraphs ⊆
      G.disjointAdmissibleDivergentSubgraphs := by
  intro A hA
  exact G.mem_disjointAdmissibleDivergentSubgraphs_of_mem_properAdmissibleDivergentSubgraphs hA

/-- The conservative singleton-only admissible index is a subindex of the
nonempty disjoint admissible carrier. -/
theorem properAdmissibleDivergentSubgraphs_subset_nonemptyDisjointAdmissibleDivergentSubgraphs
    [DivergenceMeasure G] [Fintype (FeynmanSubgraph G)] :
    G.properAdmissibleDivergentSubgraphs ⊆
      G.nonemptyDisjointAdmissibleDivergentSubgraphs := by
  intro A hA
  rcases G.mem_properAdmissibleDivergentSubgraphs_exists_singleton hA with
    ⟨γ, hγ, hAeq⟩
  rw [hAeq]
  exact G.singleton_mem_nonemptyDisjointAdmissibleDivergentSubgraphs
    ((G.mem_properConnectedDivergentSubgraphs γ).mp hγ).1

/-- The conservative singleton-only admissible index is a subindex of the
proper disjoint admissible carrier. This is the first inclusion into the
eventual forest summation carrier. -/
theorem properAdmissibleDivergentSubgraphs_subset_properDisjointAdmissibleDivergentSubgraphs
    [DivergenceMeasure G] [Fintype (FeynmanSubgraph G)] :
    G.properAdmissibleDivergentSubgraphs ⊆
      G.properDisjointAdmissibleDivergentSubgraphs := by
  intro A hA
  rcases G.mem_properAdmissibleDivergentSubgraphs_exists_singleton hA with
    ⟨γ, hγ, hAeq⟩
  rw [hAeq]
  exact G.singleton_mem_properDisjointAdmissibleDivergentSubgraphs
    (G.properConnectedDivergentSubgraphs_isConnectedDivergent hγ)
    (G.properConnectedDivergentSubgraphs_internalEdges_pos hγ)

/-- Extend a sum over the conservative singleton-only admissible index to the
finite disjoint admissible carrier, provided the added terms vanish. This is
the small bridge that lets later passes widen the index before replacing the
summand. -/
theorem sum_properAdmissibleDivergentSubgraphs_eq_sum_disjointAdmissibleDivergentSubgraphs
    [DivergenceMeasure G] [Fintype (FeynmanSubgraph G)]
    {β : Type*} [AddCommMonoid β]
    (f : AdmissibleSubgraph G → β)
    (hzero : ∀ A ∈ G.disjointAdmissibleDivergentSubgraphs,
      A ∉ G.properAdmissibleDivergentSubgraphs → f A = 0) :
    (∑ A ∈ G.properAdmissibleDivergentSubgraphs, f A)
      =
    ∑ A ∈ G.disjointAdmissibleDivergentSubgraphs, f A := by
  exact Finset.sum_subset
    (G.properAdmissibleDivergentSubgraphs_subset_disjointAdmissibleDivergentSubgraphs)
    hzero

/-- Extend a sum over the conservative singleton-only admissible index to the
finite nonempty disjoint admissible carrier, provided the added terms vanish. -/
theorem sum_properAdmissibleDivergentSubgraphs_eq_sum_nonemptyDisjointAdmissibleDivergentSubgraphs
    [DivergenceMeasure G] [Fintype (FeynmanSubgraph G)]
    {β : Type*} [AddCommMonoid β]
    (f : AdmissibleSubgraph G → β)
    (hzero : ∀ A ∈ G.nonemptyDisjointAdmissibleDivergentSubgraphs,
      A ∉ G.properAdmissibleDivergentSubgraphs → f A = 0) :
    (∑ A ∈ G.properAdmissibleDivergentSubgraphs, f A)
      =
    ∑ A ∈ G.nonemptyDisjointAdmissibleDivergentSubgraphs, f A := by
  exact Finset.sum_subset
    (G.properAdmissibleDivergentSubgraphs_subset_nonemptyDisjointAdmissibleDivergentSubgraphs)
    hzero

/-- Extend a sum over the conservative singleton-only admissible index to the
proper disjoint admissible carrier, provided the added terms vanish. -/
theorem sum_properAdmissibleDivergentSubgraphs_eq_sum_properDisjointAdmissibleDivergentSubgraphs
    [DivergenceMeasure G] [Fintype (FeynmanSubgraph G)]
    {β : Type*} [AddCommMonoid β]
    (f : AdmissibleSubgraph G → β)
    (hzero : ∀ A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
      A ∉ G.properAdmissibleDivergentSubgraphs → f A = 0) :
    (∑ A ∈ G.properAdmissibleDivergentSubgraphs, f A)
      =
    ∑ A ∈ G.properDisjointAdmissibleDivergentSubgraphs, f A := by
  exact Finset.sum_subset
    (G.properAdmissibleDivergentSubgraphs_subset_properDisjointAdmissibleDivergentSubgraphs)
    hzero

/-- Sum over the conservative admissible index as a sum over the existing
connected-divergent index. This is the basic "connected sum →
singleton-admissible sum" bridge. -/
theorem sum_properAdmissibleDivergentSubgraphs
    [DivergenceMeasure G] [Fintype (FeynmanSubgraph G)]
    {β : Type*} [AddCommMonoid β]
    (f : AdmissibleSubgraph G → β) :
    (∑ A ∈ G.properAdmissibleDivergentSubgraphs, f A)
      =
    ∑ γ ∈ G.properConnectedDivergentSubgraphs.attach,
      f (connectedIndexToAdmissible G γ) := by
  unfold properAdmissibleDivergentSubgraphs
  exact Finset.sum_image (connectedIndexToAdmissible_injective G).injOn

/-- Same bridge as `sum_properAdmissibleDivergentSubgraphs`, oriented
from the existing connected-divergent index toward the conservative
singleton admissible index. -/
theorem sum_connectedIndexToAdmissible_eq_sum_properAdmissibleDivergentSubgraphs
    [DivergenceMeasure G] [Fintype (FeynmanSubgraph G)]
    {β : Type*} [AddCommMonoid β]
    (f : AdmissibleSubgraph G → β) :
    (∑ γ ∈ G.properConnectedDivergentSubgraphs.attach,
      f (connectedIndexToAdmissible G γ))
      =
    ∑ A ∈ G.properAdmissibleDivergentSubgraphs, f A := by
  exact (sum_properAdmissibleDivergentSubgraphs G f).symm

/-- Conservative inverse for the singleton-only admissible index: every
admissible index element remembers the connected index element that
generated it. This is intentionally local to the conservative index; the
full forest version will replace it with a genuine contraction operation. -/
noncomputable def admissibleToConnectedIndex
    [DivergenceMeasure G] [Fintype (FeynmanSubgraph G)]
    (A : AdmissibleSubgraph G)
    (hA : A ∈ G.properAdmissibleDivergentSubgraphs) :
    {γ : FeynmanSubgraph G // γ ∈ G.properConnectedDivergentSubgraphs} :=
  Classical.choose (by
    unfold properAdmissibleDivergentSubgraphs at hA
    exact Finset.mem_image.mp hA)

/-- The conservative inverse maps back to the admissible index element
it came from. -/
theorem connectedIndexToAdmissible_admissibleToConnectedIndex
    [DivergenceMeasure G] [Fintype (FeynmanSubgraph G)]
    (A : AdmissibleSubgraph G)
    (hA : A ∈ G.properAdmissibleDivergentSubgraphs) :
    connectedIndexToAdmissible G (admissibleToConnectedIndex G A hA) = A := by
  unfold admissibleToConnectedIndex
  generalize_proofs h
  exact (Classical.choose_spec h).2

/-- On the image of the singleton embedding, the conservative inverse
recovers the original connected index element. -/
theorem admissibleToConnectedIndex_connectedIndexToAdmissible
    [DivergenceMeasure G] [Fintype (FeynmanSubgraph G)]
    (γ : {γ : FeynmanSubgraph G // γ ∈ G.properConnectedDivergentSubgraphs})
    (hA : connectedIndexToAdmissible G γ ∈
      G.properAdmissibleDivergentSubgraphs) :
    admissibleToConnectedIndex G (connectedIndexToAdmissible G γ) hA = γ := by
  apply connectedIndexToAdmissible_injective G
  exact connectedIndexToAdmissible_admissibleToConnectedIndex G
    (connectedIndexToAdmissible G γ) hA

end FeynmanGraph

/-! ### Section PathW — shared instance hypotheses -/

section PathW

set_option linter.unusedSectionVars false

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
         [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
         [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
         [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]

/-! ### Helper: generator embedding from a subgraph -/

namespace FeynmanSubgraph

variable {G : FeynmanGraph}

/-- The `HopfGenTemp` element corresponding to a subgraph whose
underlying graph class is support-connected (via `γ.IsConnected` ==
`γ.toFeynmanGraph.IsSupportConnected`).

Used for the left tensor factor `[γ]` in the Connes–Kreimer sum. -/
def toHopfGenTemp (γ : FeynmanSubgraph G) (hγ : γ.IsConnected) : HopfGenTemp :=
  ⟨γ.toFeynmanGraph.toClass,
    (FeynmanGraphClass.isSupportConnected_toClass γ.toFeynmanGraph).mpr hγ⟩

@[simp] theorem toHopfGenTemp_val {γ : FeynmanSubgraph G} (hγ : γ.IsConnected) :
    (γ.toHopfGenTemp hγ).val = γ.toFeynmanGraph.toClass := rfl

end FeynmanSubgraph

/-! ### H4.3 — `coproductGen` non-recursive definition (via direct formula)

**Design clarification (2026-04-24)**: The Connes–Kreimer coproduct is
*defined by an explicit formula on generators*, not by recursion. The
right-tensor factor `[Γ/γ]` is itself a generator (a `HopfGenTemp`
element built from `γ.contract.toClass`), not a recursive call to
`coproductGen(Γ/γ)`.

Re-reading HOPF_DECOMPOSITION.md line 279:
`coproductGen G = [G] ⊗ 1 + 1 ⊗ [G] + ∑ [γ] ⊗ [Γ/γ]` — both tensor
factors are generators.

`edgeRecursion` remains the formal scaffolding used by Phase B's
isomorphism-invariance induction (H4.6) and Sprint E's antipode
recursion (H6.1); the coproduct itself does not need a recursive body.

This aligns with the "recursion is for induction proofs, not for
definition" interpretation of Sprint A's `contractWith` design.
-/

/--
Right tensor factor `[Γ/γ]`: when `γ` is connected and nonempty,
`γ.contract` is support-connected by H1.16, so its class is a
`HopfGenTemp` element. -/
noncomputable def FeynmanSubgraph.contractToHopfGenTemp
    {G : FeynmanGraph} (hG : G.IsSupportConnected)
    (γ : FeynmanSubgraph G) (hγConn : γ.IsConnected) (hγNe : γ.IsNonempty) :
    HopfGenTemp :=
  ⟨γ.contract.toClass,
    (FeynmanGraphClass.isSupportConnected_toClass γ.contract).mpr
      (FeynmanSubgraph.IsConnected_contract_of_IsConnected hG hγConn hγNe)⟩

/--
**H4.3** — The coproduct on connected Feynman graphs, defined by an
explicit formula on generators.

Body: `[G] ⊗ 1 + 1 ⊗ [G] + Σ_{γ ∈ index} [γ] ⊗ [Γ/γ]`.

All three tensor factors (`[G]`, `[γ]`, `[Γ/γ]`) are `HopfGenTemp`
elements; no recursion on `coproductGen` itself.
-/
noncomputable def coproductGen (G : ConnectedFeynmanGraph) :
    HopfH_temp ⊗[ℚ] HopfH_temp :=
  let genG : HopfH_temp :=
    gen_temp ⟨G.toFeynmanGraph.toClass,
      (FeynmanGraphClass.isSupportConnected_toClass G.toFeynmanGraph).mpr
        G.isSupportConnected⟩
  (genG ⊗ₜ[ℚ] (1 : HopfH_temp))
  + ((1 : HopfH_temp) ⊗ₜ[ℚ] genG)
  + ∑ γ ∈ G.toFeynmanGraph.properConnectedDivergentSubgraphs,
      if hγ : γ.IsConnectedDivergent ∧ 0 < γ.internalEdges.card then
        let hγConn : γ.IsConnected := hγ.1.isConnected
        let hγNe : γ.IsNonempty :=
          FeynmanSubgraph.isNonempty_of_internalEdges_pos hγ.2
        (gen_temp (γ.toHopfGenTemp hγConn)) ⊗ₜ[ℚ]
          (gen_temp
            (FeynmanSubgraph.contractToHopfGenTemp G.isSupportConnected γ
              hγConn hγNe))
      else 0

/-! ### H4.5 — `coproductGen` is definitionally the body

Since `coproductGen` is a direct `def` (no wf-recursion), no separate
unfold lemma is needed: `coproductGen G` reduces to the body by
`rfl`/`unfold`. We expose the body formula for explicit use downstream.
-/

theorem coproductGen_eq (G : ConnectedFeynmanGraph) :
    coproductGen G =
      (let genG : HopfH_temp :=
        gen_temp ⟨G.toFeynmanGraph.toClass,
          (FeynmanGraphClass.isSupportConnected_toClass G.toFeynmanGraph).mpr
            G.isSupportConnected⟩
      (genG ⊗ₜ[ℚ] (1 : HopfH_temp))
      + ((1 : HopfH_temp) ⊗ₜ[ℚ] genG)
      + ∑ γ ∈ G.toFeynmanGraph.properConnectedDivergentSubgraphs,
          if hγ : γ.IsConnectedDivergent ∧ 0 < γ.internalEdges.card then
            let hγConn : γ.IsConnected := hγ.1.isConnected
            let hγNe : γ.IsNonempty :=
              FeynmanSubgraph.isNonempty_of_internalEdges_pos hγ.2
            (gen_temp (γ.toHopfGenTemp hγConn)) ⊗ₜ[ℚ]
              (gen_temp
                (FeynmanSubgraph.contractToHopfGenTemp G.isSupportConnected γ
                  hγConn hγNe))
          else 0) := rfl

/-! ### Phase B — H4.6 isomorphism invariance of `coproductGen`

Target:
```
coproductGen_isomorphism_invariant :
  ∀ {G₁ G₂ : ConnectedFeynmanGraph},
    G₁.toFeynmanGraph.IsIso G₂.toFeynmanGraph →
    coproductGen G₁ = coproductGen G₂
```

**Strategy** (refined per Phase A design clarification):
Since `coproductGen` is non-recursive (direct formula), no induction on
`edgeMeasure` is needed. Expand both sides via `coproductGen_eq`; the
three additive terms (`[G] ⊗ 1`, `1 ⊗ [G]`, `Σ [γ] ⊗ [G/γ]`) become
invariant separately:

* `[G] ⊗ 1` and `1 ⊗ [G]`: invariant via
  `toClass_eq_iff : G₁.toClass = G₂.toClass ↔ G₁.IsIso G₂`
  + Subtype / tensor congr.
* `Σ [γ] ⊗ [G/γ]`: invariant via a `Finset.sum_bij` with bijection
  `γ ↦ γ.mapPerm π` on `properConnectedDivergentSubgraphs`, plus
  per-term equalities `[γ].toClass = [γ.mapPerm π].toClass` and
  `[γ.contract].toClass = [(γ.mapPerm π).contract].toClass`.
-/

/-! #### Helpers: subgraph mapPerm preserves `IsConnectedDivergent` -/

namespace FeynmanSubgraph

variable {G : FeynmanGraph}

/-- `FeynmanSubgraph.IsConnected` is preserved by `mapPerm` (via
`FeynmanGraph.mapPerm_isSupportConnected_iff`). -/
theorem mapPerm_isConnected (π : Equiv.Perm VertexId)
    {γ : FeynmanSubgraph G} (h : γ.IsConnected) :
    (γ.mapPerm π).IsConnected := by
  unfold IsConnected at h ⊢
  have : (γ.mapPerm π).toFeynmanGraph = γ.toFeynmanGraph.mapPerm π := rfl
  rw [this, FeynmanGraph.mapPerm_isSupportConnected_iff]
  exact h

/-- `FeynmanSubgraph.IsOnePI` is preserved by `mapPerm`. -/
theorem mapPerm_isOnePI (π : Equiv.Perm VertexId)
    {γ : FeynmanSubgraph G} (h : γ.IsOnePI) :
    (γ.mapPerm π).IsOnePI := by
  unfold IsOnePI at h ⊢
  have : (γ.mapPerm π).toFeynmanGraph = γ.toFeynmanGraph.mapPerm π := rfl
  rw [this, FeynmanGraph.mapPerm_isOnePI_iff]
  exact h

end FeynmanSubgraph

namespace FeynmanSubgraph

variable {G : FeynmanGraph}

/-- `IsConnectedDivergent` is preserved by `mapPerm`. Sprint A
`IsPermInvariantDivergence` supplies the divergence transport. -/
theorem mapPerm_isConnectedDivergent (π : Equiv.Perm VertexId)
    {γ : FeynmanSubgraph G} (h : γ.IsConnectedDivergent) :
    (γ.mapPerm π).IsConnectedDivergent := by
  rcases h with ⟨hC, hO, hD⟩
  refine ⟨?_, ?_, ?_⟩
  · exact mapPerm_isConnected π hC
  · exact mapPerm_isOnePI π hO
  · exact mapPerm_isDivergent hD

/-- Reverse direction: `IsConnectedDivergent` is reflected by `mapPerm`.
The transport via π⁻¹ + the group-theoretic `(γ.mapPerm π).mapPerm π⁻¹ = γ`
cast. -/
theorem mapPerm_isConnectedDivergent_reverse
    {π : Equiv.Perm VertexId} {γ : FeynmanSubgraph G}
    (h : (γ.mapPerm π).IsConnectedDivergent) :
    γ.IsConnectedDivergent := by
  -- Work by inverse permutation. The ambient type changes:
  -- (γ.mapPerm π) : FeynmanSubgraph (G.mapPerm π).
  -- Apply mapPerm π⁻¹: target is FeynmanSubgraph ((G.mapPerm π).mapPerm π⁻¹).
  -- That ambient equals G by the group identity.
  have hback : ((γ.mapPerm π).mapPerm π⁻¹).IsConnectedDivergent :=
    mapPerm_isConnectedDivergent π⁻¹ h
  -- Now transport the IsConnectedDivergent statement across the ambient equality
  -- (γ.mapPerm π).mapPerm π⁻¹ = γ. Check field-wise equality.
  have hV : ((γ.mapPerm π).mapPerm π⁻¹).vertices = γ.vertices := by
    show Finset.image (⇑π⁻¹) (Finset.image (⇑π) γ.vertices) = γ.vertices
    rw [Finset.image_image]
    have : (⇑π⁻¹ ∘ ⇑π) = (id : VertexId → VertexId) := by
      funext x
      show π⁻¹ (π x) = x
      exact π.symm_apply_apply x
    rw [this, Finset.image_id]
  have hI : ((γ.mapPerm π).mapPerm π⁻¹).internalEdges = γ.internalEdges := by
    show Multiset.map (FeynmanEdge.map π⁻¹)
          (Multiset.map (FeynmanEdge.map π) γ.internalEdges) =
        γ.internalEdges
    rw [Multiset.map_map]
    have hcomp : (FeynmanEdge.map π⁻¹) ∘ (FeynmanEdge.map π) = id := by
      funext e
      cases e with
      | mk src tgt sec =>
        show FeynmanEdge.map π⁻¹ (FeynmanEdge.map π ⟨src, tgt, sec⟩) =
          ⟨src, tgt, sec⟩
        simp [FeynmanEdge.map, π.symm_apply_apply]
    rw [hcomp, Multiset.map_id]
  have hE : ((γ.mapPerm π).mapPerm π⁻¹).externalLegs = γ.externalLegs := by
    show Multiset.map (ExternalLeg.map π⁻¹)
          (Multiset.map (ExternalLeg.map π) γ.externalLegs) =
        γ.externalLegs
    rw [Multiset.map_map]
    have hcomp : (ExternalLeg.map π⁻¹) ∘ (ExternalLeg.map π) = id := by
      funext ℓ
      cases ℓ with
      | mk att sec =>
        show ExternalLeg.map π⁻¹ (ExternalLeg.map π ⟨att, sec⟩) =
          ⟨att, sec⟩
        simp [ExternalLeg.map, π.symm_apply_apply]
    rw [hcomp, Multiset.map_id]
  -- `IsConnectedDivergent` is a conjunction of predicates on toFeynmanGraph
  -- + divergenceDegree. These are computed from the three data fields only.
  -- Since the ambient type differs ((G.mapPerm π).mapPerm π⁻¹ vs G), strict
  -- type-casting is needed. Use the group identity on FeynmanGraph.
  have hGback : (G.mapPerm π).mapPerm π⁻¹ = G := by
    rw [← FeynmanGraph.mapPerm_mul]; simp
  -- Transport `hback` from `(γ.mapPerm π).mapPerm π⁻¹ : FeynmanSubgraph
  -- ((G.mapPerm π).mapPerm π⁻¹)` to `γ : FeynmanSubgraph G` via the
  -- ambient cast. Use field-wise equality to rewrite the IsConnectedDivergent
  -- claim.
  -- Concretely: `IsConnectedDivergent` equals
  --   γ.IsConnected ∧ γ.IsOnePI ∧ γ.IsDivergent
  -- Each is a Prop on γ's data fields (through toFeynmanGraph or
  -- DivergenceMeasure G). We rebuild it from hback's witnesses plus
  -- field equalities.
  rcases hback with ⟨hC, hO, hD⟩
  refine ⟨?_, ?_, ?_⟩
  · -- IsConnected: both are about the underlying FeynmanGraph's
    -- IsSupportConnected. The underlying graph of γ with fields rewritten
    -- via hV/hI/hE equals `{ vertices := γ.vertices, internalEdges := γ.internalEdges,
    -- externalLegs := γ.externalLegs }` = γ.toFeynmanGraph.
    show γ.toFeynmanGraph.IsSupportConnected
    have : ((γ.mapPerm π).mapPerm π⁻¹).toFeynmanGraph = γ.toFeynmanGraph := by
      apply FeynmanGraph.mk.injEq _ _ _ _ _ _ |>.mpr
      refine ⟨hV, hI, hE⟩
    rw [← this]; exact hC
  · show γ.toFeynmanGraph.IsOnePI
    have : ((γ.mapPerm π).mapPerm π⁻¹).toFeynmanGraph = γ.toFeynmanGraph := by
      apply FeynmanGraph.mk.injEq _ _ _ _ _ _ |>.mpr
      refine ⟨hV, hI, hE⟩
    rw [← this]; exact hO
  · -- IsDivergent: `divergenceDegree γ` depends on the DivergenceMeasure G
    -- instance, `divergenceDegree ((γ.mapPerm π).mapPerm π⁻¹)` depends on
    -- DivergenceMeasure ((G.mapPerm π).mapPerm π⁻¹). We transport via
    -- the ambient equality `hGback` and rely on IsPermInvariantDivergence
    -- chained across the composition (or simpler: same data field, so degree
    -- is the same up to typeclass cast).
    -- Path: use IsPermInvariantDivergence.degree_mapPerm twice.
    unfold IsDivergent divergenceDegree at hD ⊢
    have hEq1 : (DivergenceMeasure.degree (γ.mapPerm π) : Int) =
        DivergenceMeasure.degree γ :=
      IsPermInvariantDivergence.degree_mapPerm π γ
    have hEq2 : (DivergenceMeasure.degree ((γ.mapPerm π).mapPerm π⁻¹) : Int) =
        DivergenceMeasure.degree (γ.mapPerm π) :=
      IsPermInvariantDivergence.degree_mapPerm π⁻¹ (γ.mapPerm π)
    rw [← hEq1, ← hEq2]
    exact hD

end FeynmanSubgraph

/-! #### Finset bijection: properConnectedDivergentSubgraphs under mapPerm

For iso witness `π : G₂ = G₁.mapPerm π`, the map
`γ ↦ γ.mapPerm π : FeynmanSubgraph G₁ → FeynmanSubgraph G₂` restricts
to a bijection on `properConnectedDivergentSubgraphs`.
-/

/-- Image under `γ ↦ γ.mapPerm π` of a `properConnectedDivergentSubgraphs`
member, with its target ambient rewritten via `hπ` to `G₂`. -/
noncomputable def mapPermSubgraph {G₁ G₂ : FeynmanGraph}
    {π : Equiv.Perm VertexId} (hπ : G₂ = G₁.mapPerm π)
    (γ : FeynmanSubgraph G₁) : FeynmanSubgraph G₂ := hπ ▸ γ.mapPerm π

/-- The target of `mapPermSubgraph` has data fields matching
`γ.mapPerm π` (the ambient is definitionally equal via `hπ`). -/
theorem mapPermSubgraph_vertices {G₁ G₂ : FeynmanGraph}
    {π : Equiv.Perm VertexId} (hπ : G₂ = G₁.mapPerm π)
    (γ : FeynmanSubgraph G₁) :
    (mapPermSubgraph hπ γ).vertices = γ.vertices.image π := by
  unfold mapPermSubgraph
  subst hπ
  rfl

theorem mapPermSubgraph_internalEdges {G₁ G₂ : FeynmanGraph}
    {π : Equiv.Perm VertexId} (hπ : G₂ = G₁.mapPerm π)
    (γ : FeynmanSubgraph G₁) :
    (mapPermSubgraph hπ γ).internalEdges =
      γ.internalEdges.map (FeynmanEdge.map π) := by
  unfold mapPermSubgraph
  subst hπ
  rfl

theorem mapPermSubgraph_externalLegs {G₁ G₂ : FeynmanGraph}
    {π : Equiv.Perm VertexId} (hπ : G₂ = G₁.mapPerm π)
    (γ : FeynmanSubgraph G₁) :
    (mapPermSubgraph hπ γ).externalLegs =
      γ.externalLegs.map (ExternalLeg.map π) := by
  unfold mapPermSubgraph
  subst hπ
  rfl

/-- The toFeynmanGraph of the transported subgraph equals the mapPerm
of the original's toFeynmanGraph. Used to quote `mapPerm_*_iff`
lemmas at the class level. -/
theorem mapPermSubgraph_toFeynmanGraph {G₁ G₂ : FeynmanGraph}
    {π : Equiv.Perm VertexId} (hπ : G₂ = G₁.mapPerm π)
    (γ : FeynmanSubgraph G₁) :
    (mapPermSubgraph hπ γ).toFeynmanGraph = γ.toFeynmanGraph.mapPerm π := by
  apply FeynmanGraph.mk.injEq _ _ _ _ _ _ |>.mpr
  refine ⟨?_, ?_, ?_⟩
  · show (mapPermSubgraph hπ γ).vertices = γ.vertices.image π
    exact mapPermSubgraph_vertices hπ γ
  · show (mapPermSubgraph hπ γ).internalEdges =
      γ.internalEdges.map (FeynmanEdge.map π)
    exact mapPermSubgraph_internalEdges hπ γ
  · show (mapPermSubgraph hπ γ).externalLegs =
      γ.externalLegs.map (ExternalLeg.map π)
    exact mapPermSubgraph_externalLegs hπ γ

/-- `IsConnectedDivergent` is preserved by `mapPermSubgraph` (via
`mapPerm_isConnectedDivergent` + the ambient-type transport). -/
theorem mapPermSubgraph_isConnectedDivergent {G₁ G₂ : FeynmanGraph}
    {π : Equiv.Perm VertexId} (hπ : G₂ = G₁.mapPerm π)
    {γ : FeynmanSubgraph G₁} (h : γ.IsConnectedDivergent) :
    (mapPermSubgraph hπ γ).IsConnectedDivergent := by
  unfold mapPermSubgraph
  subst hπ
  exact FeynmanSubgraph.mapPerm_isConnectedDivergent π h

/-- Internal-edge count preserved. -/
theorem mapPermSubgraph_internalEdges_card {G₁ G₂ : FeynmanGraph}
    {π : Equiv.Perm VertexId} (hπ : G₂ = G₁.mapPerm π)
    (γ : FeynmanSubgraph G₁) :
    (mapPermSubgraph hπ γ).internalEdges.card =
      γ.internalEdges.card := by
  rw [mapPermSubgraph_internalEdges]
  simp

/-! #### Per-term isomorphism invariance

The Finset `sum_bij` needs, for each γ in the index set of G₁, a term
equality with the γ'-indexed term on G₂ side (γ' := mapPermSubgraph γ).

Each summand is `(gen_temp [γ]) ⊗ₜ (gen_temp [γ.contract])`. Both
`[γ].toClass` and `[γ.contract].toClass` are preserved by the
transport since `toClass` collapses `IsIso` in `GraphIsomorphism.lean`.
-/

/-- `[γ].toClass = [mapPermSubgraph γ].toClass`. Direct from the
`IsIso` witness `π` on the underlying graphs. -/
theorem mapPermSubgraph_toClass_eq {G₁ G₂ : FeynmanGraph}
    {π : Equiv.Perm VertexId} (hπ : G₂ = G₁.mapPerm π)
    (γ : FeynmanSubgraph G₁) :
    (mapPermSubgraph hπ γ).toFeynmanGraph.toClass =
      γ.toFeynmanGraph.toClass := by
  rw [mapPermSubgraph_toFeynmanGraph]
  symm
  exact (FeynmanGraph.toClass_eq_iff _ _).mpr ⟨π, rfl⟩

/-! #### Local helper: `Multiset.map` distributes over submultiset subtraction

Mirrors the `SubgraphClass.lean` private helper; redeclared here to
avoid cross-file scope issues. -/

private theorem map_sub_of_injective {α β : Type*}
    [DecidableEq α] [DecidableEq β] {f : α → β}
    (hf : Function.Injective f) {A B : Multiset α} (hle : B ≤ A) :
    (A - B).map f = A.map f - B.map f := by
  refine Multiset.ext.mpr (fun y => ?_)
  rw [Multiset.count_sub]
  by_cases hy : y ∈ A.map f
  · rcases Multiset.mem_map.mp hy with ⟨x, hxA, rfl⟩
    rw [Multiset.count_map_eq_count' _ _ hf,
        Multiset.count_map_eq_count' _ _ hf,
        Multiset.count_map_eq_count' _ _ hf,
        Multiset.count_sub]
  · have hBmap_le : B.map f ≤ A.map f := Multiset.map_le_map hle
    have hy_B : y ∉ B.map f := fun hyB => hy (Multiset.mem_of_le hBmap_le hyB)
    have hy_sub : y ∉ (A - B).map f := by
      intro h
      rcases Multiset.mem_map.mp h with ⟨x, hx, rfl⟩
      have hxA : x ∈ A := Multiset.mem_of_le (Multiset.sub_le_self _ _) hx
      exact hy (Multiset.mem_map.mpr ⟨x, hxA, rfl⟩)
    rw [Multiset.count_eq_zero_of_notMem hy_sub,
        Multiset.count_eq_zero_of_notMem hy,
        Multiset.count_eq_zero_of_notMem hy_B]

/-! #### Contract commutes with mapPerm up to iso

For `γ : FeynmanSubgraph G` and `π : Equiv.Perm VertexId`,
`(γ.mapPerm π).contract` and `γ.contract` are isomorphic as
`FeynmanGraph`s, hence equal in `FeynmanGraphClass`. The witness is

```
τ := swap s₂ (π s₁) * π
```

where `s₁ := freshVertex G.vertices` and
`s₂ := freshVertex (G.mapPerm π).vertices = freshVertex (G.vertices.image π)`.
This `τ` satisfies `τ s₁ = s₂` and agrees with `π` on `G.vertices`.

**Option X2 scope**: we only exhibit the `IsIso` witness, not a literal
equality. This matches what H4.6 needs (class-level equality) without
re-proving Sprint B' H2.1 in the ambient-moving case.
-/

namespace FeynmanSubgraph

variable {G : FeynmanGraph}

/-- `τ` built from `π` that carries `s₁ := freshVertex G.vertices` to
`s₂ := freshVertex (G.mapPerm π).vertices` while preserving `π`'s
action on `G.vertices`. -/
private noncomputable def freshAlignedPerm
    (G : FeynmanGraph) (π : Equiv.Perm VertexId) : Equiv.Perm VertexId :=
  Equiv.swap (FeynmanGraph.freshVertex (G.mapPerm π).vertices) (π (FeynmanGraph.freshVertex G.vertices)) * π

private theorem freshAlignedPerm_apply_s₁
    (G : FeynmanGraph) (π : Equiv.Perm VertexId) :
    freshAlignedPerm G π (FeynmanGraph.freshVertex G.vertices) =
      FeynmanGraph.freshVertex (G.mapPerm π).vertices := by
  unfold freshAlignedPerm
  simp [Equiv.swap_apply_right]

/-- `π` maps `G.vertices` to `(G.mapPerm π).vertices` (definitionally). -/
private theorem vertices_mapPerm (G : FeynmanGraph) (π : Equiv.Perm VertexId) :
    (G.mapPerm π).vertices = G.vertices.image π := rfl

/-- For `v ∈ G.vertices`, `π v ∈ (G.mapPerm π).vertices`. -/
private theorem mem_vertices_mapPerm {G : FeynmanGraph} {π : Equiv.Perm VertexId}
    {v : VertexId} (hv : v ∈ G.vertices) : π v ∈ (G.mapPerm π).vertices := by
  rw [vertices_mapPerm]
  exact Finset.mem_image.mpr ⟨v, hv, rfl⟩

/-- `freshVertex (G.mapPerm π).vertices ∉ (G.mapPerm π).vertices`. -/
private theorem freshVertex_mapPerm_not_mem
    (G : FeynmanGraph) (π : Equiv.Perm VertexId) :
    FeynmanGraph.freshVertex (G.mapPerm π).vertices ∉ (G.mapPerm π).vertices :=
  FeynmanGraph.freshVertex_not_mem _

/-- On `G.vertices`, `freshAlignedPerm G π` agrees with `π`. Key fact
for pointwise vertex-field equality in the contract. -/
private theorem freshAlignedPerm_apply_of_mem
    {G : FeynmanGraph} {π : Equiv.Perm VertexId}
    {v : VertexId} (hv : v ∈ G.vertices) :
    freshAlignedPerm G π v = π v := by
  unfold freshAlignedPerm
  show Equiv.swap (FeynmanGraph.freshVertex (G.mapPerm π).vertices)
        (π (FeynmanGraph.freshVertex G.vertices)) (π v) = π v
  have hπv_mem : π v ∈ (G.mapPerm π).vertices := mem_vertices_mapPerm hv
  have hs₁_notmem : FeynmanGraph.freshVertex G.vertices ∉ G.vertices :=
    FeynmanGraph.freshVertex_not_mem _
  have hπs₁_notmem : π (FeynmanGraph.freshVertex G.vertices) ∉ (G.mapPerm π).vertices := by
    rw [vertices_mapPerm]
    intro h
    rcases Finset.mem_image.mp h with ⟨w, hw, hwπ⟩
    have : w = FeynmanGraph.freshVertex G.vertices := π.injective hwπ
    exact hs₁_notmem (this ▸ hw)
  have hne_s₂ : π v ≠ FeynmanGraph.freshVertex (G.mapPerm π).vertices := fun h =>
    (freshVertex_mapPerm_not_mem G π) (h ▸ hπv_mem)
  have hne_πs₁ : π v ≠ π (FeynmanGraph.freshVertex G.vertices) := fun h =>
    hπs₁_notmem (h ▸ hπv_mem)
  rw [Equiv.swap_apply_of_ne_of_ne hne_s₂ hne_πs₁]

/-! ##### Field-wise equality `γ.contract.mapPerm τ = (γ.mapPerm π).contract` -/

/-- Vertices field. Both sides simplify to
`((G.mapPerm π).vertices \ (γ.mapPerm π).vertices) ∪ {freshVertex …}`. -/
private theorem contract_mapPerm_vertices_eq
    {G : FeynmanGraph} (_hGwf : G.WellFormed)
    (γ : FeynmanSubgraph G) (π : Equiv.Perm VertexId) :
    (γ.contract.mapPerm (freshAlignedPerm G π)).vertices =
      (γ.mapPerm π).contract.vertices := by
  -- LHS: ((G.vertices \ γ.vertices) ∪ {freshVertex G.vertices}).image τ
  -- RHS: ((G.mapPerm π).vertices \ (γ.mapPerm π).vertices) ∪ {freshVertex (G.mapPerm π).vertices}
  show ((G.vertices \ γ.vertices) ∪
          {FeynmanGraph.freshVertex G.vertices}).image
        (freshAlignedPerm G π) =
      ((G.mapPerm π).vertices \ (γ.mapPerm π).vertices) ∪
        {FeynmanGraph.freshVertex (G.mapPerm π).vertices}
  rw [Finset.image_union, Finset.image_singleton, freshAlignedPerm_apply_s₁]
  congr 1
  -- (G.vertices \ γ.vertices).image τ = (G.vertices.image π) \ (γ.vertices.image π)
  ext w
  constructor
  · intro hw
    rw [Finset.mem_image] at hw
    rcases hw with ⟨v, hv_sdiff, hτv⟩
    rw [Finset.mem_sdiff] at hv_sdiff
    obtain ⟨hvG, hvγ⟩ := hv_sdiff
    have hτeqπ : freshAlignedPerm G π v = π v := freshAlignedPerm_apply_of_mem hvG
    rw [hτeqπ] at hτv
    subst hτv
    rw [Finset.mem_sdiff, vertices_mapPerm]
    refine ⟨mem_vertices_mapPerm hvG, ?_⟩
    intro h
    rcases Finset.mem_image.mp h with ⟨u, hu, huπ⟩
    have : u = v := π.injective huπ
    exact hvγ (this ▸ hu)
  · intro hw
    rw [Finset.mem_sdiff, vertices_mapPerm] at hw
    obtain ⟨hwG, hwγ⟩ := hw
    rcases Finset.mem_image.mp hwG with ⟨v, hvG, rfl⟩
    rw [Finset.mem_image]
    refine ⟨v, Finset.mem_sdiff.mpr ⟨hvG, ?_⟩, ?_⟩
    · intro hv
      apply hwγ
      show π v ∈ (γ.mapPerm π).vertices
      exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
    · exact freshAlignedPerm_apply_of_mem hvG

/-- The underlying `FeynmanGraph` iso between `(γ.mapPerm π).contract` and
`γ.contract`. -/
private theorem contract_mapPerm_isIso
    {G : FeynmanGraph} (hGwf : G.WellFormed)
    (γ : FeynmanSubgraph G) (π : Equiv.Perm VertexId) :
    γ.contract.IsIso (γ.mapPerm π).contract := by
  refine ⟨freshAlignedPerm G π, ?_⟩
  -- (γ.mapPerm π).contract = γ.contract.mapPerm (freshAlignedPerm G π)
  apply FeynmanGraph.mk.injEq _ _ _ _ _ _ |>.mpr
  refine ⟨?_, ?_, ?_⟩
  · -- vertices
    show (γ.mapPerm π).contract.vertices =
      (γ.contract.mapPerm (freshAlignedPerm G π)).vertices
    exact (contract_mapPerm_vertices_eq hGwf γ π).symm
  · -- internalEdges
    -- LHS: (γ.mapPerm π).complementEdges.map (retarget (γ.mapPerm π).vertices
    --        (freshVertex (G.mapPerm π).vertices))
    -- RHS: γ.complementEdges.map (retarget γ.vertices (freshVertex G.vertices))
    --        .map (FeynmanEdge.map τ)
    show (γ.mapPerm π).contract.internalEdges =
      γ.contract.internalEdges.map (FeynmanEdge.map (freshAlignedPerm G π))
    show (γ.mapPerm π).complementEdges.map
          (FeynmanEdge.retarget (γ.mapPerm π).vertices
            (FeynmanGraph.freshVertex (G.mapPerm π).vertices)) =
      (γ.complementEdges.map
          (FeynmanEdge.retarget γ.vertices
            (FeynmanGraph.freshVertex G.vertices))).map
        (FeynmanEdge.map (freshAlignedPerm G π))
    -- complementEdges_mapPerm: (γ.mapPerm π).complementEdges =
    --   γ.complementEdges.map (FeynmanEdge.map π)
    have hcomp : (γ.mapPerm π).complementEdges =
        γ.complementEdges.map (FeynmanEdge.map π) := by
      unfold FeynmanSubgraph.complementEdges
      show ((G.mapPerm π).internalEdges - (γ.mapPerm π).internalEdges) =
        (G.internalEdges - γ.internalEdges).map (FeynmanEdge.map π)
      -- (G.mapPerm π).internalEdges = G.internalEdges.map (FeynmanEdge.map π)
      -- (γ.mapPerm π).internalEdges = γ.internalEdges.map (FeynmanEdge.map π)
      -- by def; hence subtraction distributes along an injective map.
      show G.internalEdges.map (FeynmanEdge.map π) -
          γ.internalEdges.map (FeynmanEdge.map π) =
        (G.internalEdges - γ.internalEdges).map (FeynmanEdge.map π)
      symm
      exact map_sub_of_injective
        (FeynmanGraph.FeynmanEdge_map_injective π) γ.internalEdges_le
    rw [hcomp, Multiset.map_map, Multiset.map_map]
    apply Multiset.map_congr rfl
    intro e he
    -- pointwise: retarget (γ.mapPerm π).vertices s₂ (FeynmanEdge.map π e)
    --          = FeynmanEdge.map τ (retarget γ.vertices s₁ e)
    have he_inG : e ∈ G.internalEdges :=
      Multiset.mem_of_le (Multiset.sub_le_self _ _) he
    have hsupp := hGwf.1 e he_inG
    have hsrc_G : e.source ∈ G.vertices := by
      simp [FeynmanEdge.SupportedOn] at hsupp; exact hsupp.1
    have htgt_G : e.target ∈ G.vertices := by
      simp [FeynmanEdge.SupportedOn] at hsupp; exact hsupp.2
    show (FeynmanEdge.retarget (γ.mapPerm π).vertices
            (FeynmanGraph.freshVertex (G.mapPerm π).vertices))
          ((FeynmanEdge.map π) e) =
        (FeynmanEdge.map (freshAlignedPerm G π))
          ((FeynmanEdge.retarget γ.vertices
            (FeynmanGraph.freshVertex G.vertices)) e)
    -- Bridge between "src ∈ γ.vertices" and "π src ∈ (γ.mapPerm π).vertices".
    -- The subgraph-level `mapPerm_vertices` gives (γ.mapPerm π).vertices = γ.vertices.image π.
    have hsrc_iff : e.source ∈ γ.vertices ↔
        π e.source ∈ (γ.mapPerm π).vertices := by
      show e.source ∈ γ.vertices ↔ π e.source ∈ γ.vertices.image π
      constructor
      · intro h; exact Finset.mem_image.mpr ⟨e.source, h, rfl⟩
      · intro h
        rcases Finset.mem_image.mp h with ⟨v, hv, hvπ⟩
        have : v = e.source := π.injective hvπ
        exact this ▸ hv
    have htgt_iff : e.target ∈ γ.vertices ↔
        π e.target ∈ (γ.mapPerm π).vertices := by
      show e.target ∈ γ.vertices ↔ π e.target ∈ γ.vertices.image π
      constructor
      · intro h; exact Finset.mem_image.mpr ⟨e.target, h, rfl⟩
      · intro h
        rcases Finset.mem_image.mp h with ⟨v, hv, hvπ⟩
        have : v = e.target := π.injective hvπ
        exact this ▸ hv
    -- Decompose FeynmanEdge equality into field-wise equalities.
    apply FeynmanEdge.mk.injEq _ _ _ _ _ _ |>.mpr
    refine ⟨?_, ?_, ?_⟩
    · -- source field
      show (FeynmanEdge.retarget (γ.mapPerm π).vertices
              (FeynmanGraph.freshVertex (G.mapPerm π).vertices)
              ((FeynmanEdge.map π) e)).source =
          ((FeynmanEdge.map (freshAlignedPerm G π))
            (FeynmanEdge.retarget γ.vertices
              (FeynmanGraph.freshVertex G.vertices) e)).source
      simp only [FeynmanEdge.retarget, FeynmanEdge.map]
      -- Goal now: (if π e.source ∈ (γ.mapPerm π).vertices then freshVertex (G.mapPerm π).vertices else π e.source) = (freshAlignedPerm G π) (if e.source ∈ γ.vertices then freshVertex G.vertices else e.source)
      by_cases hsγ : e.source ∈ γ.vertices
      · rw [if_pos hsγ, if_pos (hsrc_iff.mp hsγ)]
        exact (freshAlignedPerm_apply_s₁ G π).symm
      · rw [if_neg hsγ, if_neg (fun h => hsγ (hsrc_iff.mpr h))]
        exact (freshAlignedPerm_apply_of_mem hsrc_G).symm
    · -- target field
      show (FeynmanEdge.retarget (γ.mapPerm π).vertices
              (FeynmanGraph.freshVertex (G.mapPerm π).vertices)
              ((FeynmanEdge.map π) e)).target =
          ((FeynmanEdge.map (freshAlignedPerm G π))
            (FeynmanEdge.retarget γ.vertices
              (FeynmanGraph.freshVertex G.vertices) e)).target
      simp only [FeynmanEdge.retarget, FeynmanEdge.map]
      by_cases htγ : e.target ∈ γ.vertices
      · rw [if_pos htγ, if_pos (htgt_iff.mp htγ)]
        exact (freshAlignedPerm_apply_s₁ G π).symm
      · rw [if_neg htγ, if_neg (fun h => htγ (htgt_iff.mpr h))]
        exact (freshAlignedPerm_apply_of_mem htgt_G).symm
    · -- sector field
      rfl
  · -- externalLegs: similar pattern
    show (γ.mapPerm π).contract.externalLegs =
      γ.contract.externalLegs.map (ExternalLeg.map (freshAlignedPerm G π))
    show (G.mapPerm π).externalLegs.map
          (ExternalLeg.retarget (γ.mapPerm π).vertices
            (FeynmanGraph.freshVertex (G.mapPerm π).vertices)) =
      (G.externalLegs.map
          (ExternalLeg.retarget γ.vertices
            (FeynmanGraph.freshVertex G.vertices))).map
        (ExternalLeg.map (freshAlignedPerm G π))
    show (G.externalLegs.map (ExternalLeg.map π)).map
          (ExternalLeg.retarget (γ.mapPerm π).vertices
            (FeynmanGraph.freshVertex (G.mapPerm π).vertices)) = _
    rw [Multiset.map_map, Multiset.map_map]
    apply Multiset.map_congr rfl
    intro ℓ hℓ
    have hsupp := hGwf.2 ℓ hℓ
    have hatt_G : ℓ.attachedTo ∈ G.vertices := by
      simp [ExternalLeg.SupportedOn] at hsupp; exact hsupp
    show (ExternalLeg.retarget (γ.mapPerm π).vertices
            (FeynmanGraph.freshVertex (G.mapPerm π).vertices))
          ((ExternalLeg.map π) ℓ) =
        (ExternalLeg.map (freshAlignedPerm G π))
          ((ExternalLeg.retarget γ.vertices
            (FeynmanGraph.freshVertex G.vertices)) ℓ)
    have hatt_iff : ℓ.attachedTo ∈ γ.vertices ↔
        π ℓ.attachedTo ∈ (γ.mapPerm π).vertices := by
      show ℓ.attachedTo ∈ γ.vertices ↔ π ℓ.attachedTo ∈ γ.vertices.image π
      constructor
      · intro h; exact Finset.mem_image.mpr ⟨ℓ.attachedTo, h, rfl⟩
      · intro h
        rcases Finset.mem_image.mp h with ⟨v, hv, hvπ⟩
        have : v = ℓ.attachedTo := π.injective hvπ
        exact this ▸ hv
    apply ExternalLeg.mk.injEq _ _ _ _ |>.mpr
    refine ⟨?_, rfl⟩
    -- attachedTo field
    show (ExternalLeg.retarget (γ.mapPerm π).vertices
            (FeynmanGraph.freshVertex (G.mapPerm π).vertices)
            ((ExternalLeg.map π) ℓ)).attachedTo =
        ((ExternalLeg.map (freshAlignedPerm G π))
          (ExternalLeg.retarget γ.vertices
            (FeynmanGraph.freshVertex G.vertices) ℓ)).attachedTo
    simp only [ExternalLeg.retarget, ExternalLeg.map]
    by_cases hattγ : ℓ.attachedTo ∈ γ.vertices
    · rw [if_pos hattγ, if_pos (hatt_iff.mp hattγ)]
      exact (freshAlignedPerm_apply_s₁ G π).symm
    · rw [if_neg hattγ, if_neg (fun h => hattγ (hatt_iff.mpr h))]
      exact (freshAlignedPerm_apply_of_mem hatt_G).symm

end FeynmanSubgraph

/-- Class-level version: `(mapPermSubgraph γ).contract.toClass =
γ.contract.toClass`. -/
theorem mapPermSubgraph_contract_toClass_eq {G₁ G₂ : FeynmanGraph}
    (hG₁wf : G₁.WellFormed)
    {π : Equiv.Perm VertexId} (hπ : G₂ = G₁.mapPerm π)
    (γ : FeynmanSubgraph G₁) :
    (mapPermSubgraph hπ γ).contract.toClass = γ.contract.toClass := by
  subst hπ
  show (γ.mapPerm π).contract.toClass = γ.contract.toClass
  symm
  exact Quotient.sound (FeynmanSubgraph.contract_mapPerm_isIso hG₁wf γ π)

/-! ### H4.6 — Main theorem: isomorphism invariance of `coproductGen` -/

/-- Index-set preservation under `mapPermSubgraph`: γ is in the
index set iff its image is. -/
theorem mapPermSubgraph_mem_index_iff {G₁ G₂ : FeynmanGraph}
    {π : Equiv.Perm VertexId} (hπ : G₂ = G₁.mapPerm π)
    (γ : FeynmanSubgraph G₁) :
    mapPermSubgraph hπ γ ∈ G₂.properConnectedDivergentSubgraphs ↔
      γ ∈ G₁.properConnectedDivergentSubgraphs := by
  rw [FeynmanGraph.mem_properConnectedDivergentSubgraphs,
      FeynmanGraph.mem_properConnectedDivergentSubgraphs]
  -- With `hπ` absorbed via `subst`, `mapPermSubgraph rfl γ = γ.mapPerm π`.
  subst hπ
  unfold mapPermSubgraph
  have hInternalCard :
      (γ.mapPerm π).internalEdges.card = γ.internalEdges.card := by
    show (γ.internalEdges.map (FeynmanEdge.map π)).card =
      γ.internalEdges.card
    simp
  have hComplementCard :
      (γ.mapPerm π).complementEdges.card = γ.complementEdges.card := by
    unfold FeynmanSubgraph.complementEdges
    show (G₁.internalEdges.map (FeynmanEdge.map π) -
        γ.internalEdges.map (FeynmanEdge.map π)).card =
      (G₁.internalEdges - γ.internalEdges).card
    rw [← map_sub_of_injective
      (FeynmanGraph.FeynmanEdge_map_injective π) γ.internalEdges_le]
    simp
  constructor
  · rintro ⟨hCD, hCard, hComplement⟩
    refine ⟨FeynmanSubgraph.mapPerm_isConnectedDivergent_reverse hCD, ?_, ?_⟩
    · rwa [hInternalCard] at hCard
    · rwa [hComplementCard] at hComplement
  · rintro ⟨hCD, hCard, hComplement⟩
    refine ⟨FeynmanSubgraph.mapPerm_isConnectedDivergent π hCD, ?_, ?_⟩
    · rwa [hInternalCard]
    · rwa [hComplementCard]

/-! #### Surjective preimage helper

Rather than define a full inverse `mapPermSubgraph_symm : FeynmanSubgraph G₂ →
FeynmanSubgraph G₁` (which requires delicate cast handling through the
group identity), we directly build the preimage witness element-wise
inside the `Finset.sum_bij` surjectivity argument.

Given `γ' ∈ G₂.properConnectedDivergentSubgraphs` and
`hπ : G₂ = G₁.mapPerm π`, applying `mapPermSubgraph hπ.symm_via_π_inv γ'`
lands in `FeynmanSubgraph G₁` through `(G₁.mapPerm π).mapPerm π⁻¹ = G₁`.

We formulate this via `mapPermSubgraph` applied with the inverse
ambient equality obtained from the group identity. -/

/-- Preimage of `γ' : FeynmanSubgraph G₂` under `mapPermSubgraph hπ`,
using `π⁻¹` and the group identity `(G₁.mapPerm π).mapPerm π⁻¹ = G₁`. -/
noncomputable def mapPermSubgraph_preimage {G₁ G₂ : FeynmanGraph}
    {π : Equiv.Perm VertexId} (hπ : G₂ = G₁.mapPerm π)
    (γ' : FeynmanSubgraph G₂) : FeynmanSubgraph G₁ :=
  have h₁ : G₁ = G₂.mapPerm π⁻¹ := by
    subst hπ; rw [← FeynmanGraph.mapPerm_mul]; simp
  mapPermSubgraph h₁ γ'

/-- Applying `mapPermSubgraph` to the preimage recovers the original subgraph
up to field equality. This is used directly inside `Finset.sum_bij` for the
surjectivity witness. -/
theorem mapPermSubgraph_preimage_vertices {G₁ G₂ : FeynmanGraph}
    {π : Equiv.Perm VertexId} (hπ : G₂ = G₁.mapPerm π)
    (γ' : FeynmanSubgraph G₂) :
    (mapPermSubgraph hπ (mapPermSubgraph_preimage hπ γ')).vertices = γ'.vertices := by
  rw [mapPermSubgraph_vertices, mapPermSubgraph_preimage, mapPermSubgraph_vertices]
  rw [Finset.image_image]
  have hcomp : (⇑π ∘ ⇑π⁻¹) = (id : VertexId → VertexId) := by
    funext x; exact π.apply_symm_apply x
  rw [hcomp, Finset.image_id]

theorem mapPermSubgraph_preimage_internalEdges {G₁ G₂ : FeynmanGraph}
    {π : Equiv.Perm VertexId} (hπ : G₂ = G₁.mapPerm π)
    (γ' : FeynmanSubgraph G₂) :
    (mapPermSubgraph hπ (mapPermSubgraph_preimage hπ γ')).internalEdges =
      γ'.internalEdges := by
  rw [mapPermSubgraph_internalEdges, mapPermSubgraph_preimage,
    mapPermSubgraph_internalEdges]
  rw [Multiset.map_map]
  have hcomp : (FeynmanEdge.map π) ∘ (FeynmanEdge.map π⁻¹) = id := by
    funext e
    cases e with
    | mk src tgt sec =>
      show FeynmanEdge.map π (FeynmanEdge.map π⁻¹ ⟨src, tgt, sec⟩) =
        ⟨src, tgt, sec⟩
      simp [FeynmanEdge.map, π.apply_symm_apply]
  rw [hcomp, Multiset.map_id]

theorem mapPermSubgraph_preimage_externalLegs {G₁ G₂ : FeynmanGraph}
    {π : Equiv.Perm VertexId} (hπ : G₂ = G₁.mapPerm π)
    (γ' : FeynmanSubgraph G₂) :
    (mapPermSubgraph hπ (mapPermSubgraph_preimage hπ γ')).externalLegs =
      γ'.externalLegs := by
  rw [mapPermSubgraph_externalLegs, mapPermSubgraph_preimage,
    mapPermSubgraph_externalLegs]
  rw [Multiset.map_map]
  have hcomp : (ExternalLeg.map π) ∘ (ExternalLeg.map π⁻¹) = id := by
    funext ℓ
    cases ℓ with
    | mk att sec =>
      show ExternalLeg.map π (ExternalLeg.map π⁻¹ ⟨att, sec⟩) = ⟨att, sec⟩
      simp [ExternalLeg.map, π.apply_symm_apply]
  rw [hcomp, Multiset.map_id]

/-- `mapPermSubgraph hπ (mapPermSubgraph_preimage hπ γ') = γ'` via
`FeynmanSubgraph.ext_iff` (data-field equality). -/
theorem mapPermSubgraph_preimage_eq {G₁ G₂ : FeynmanGraph}
    {π : Equiv.Perm VertexId} (hπ : G₂ = G₁.mapPerm π)
    (γ' : FeynmanSubgraph G₂) :
    mapPermSubgraph hπ (mapPermSubgraph_preimage hπ γ') = γ' :=
  FeynmanSubgraph.ext_iff.mpr
    ⟨mapPermSubgraph_preimage_vertices hπ γ',
     mapPermSubgraph_preimage_internalEdges hπ γ',
     mapPermSubgraph_preimage_externalLegs hπ γ'⟩

/-- **H4.6 (main theorem)** — `coproductGen` is invariant under graph
isomorphism of the underlying `FeynmanGraph`s.

The `WellFormed` hypothesis enters through
`mapPermSubgraph_contract_toClass_eq`'s reliance on
`contract_mapPerm_isIso`, which needs `G`-well-formedness for the
support-on fields.  `ConnectedFeynmanGraph` does not carry a
`WellFormed` witness; class-lift sites (Phase C) will supply it. -/
theorem coproductGen_isomorphism_invariant
    {G₁ G₂ : ConnectedFeynmanGraph}
    (hG₁wf : G₁.toFeynmanGraph.WellFormed)
    (h : G₁.toFeynmanGraph.IsIso G₂.toFeynmanGraph) :
    coproductGen G₁ = coproductGen G₂ := by
  obtain ⟨π, hπ⟩ := h
  rw [coproductGen_eq, coproductGen_eq]
  have hClass : G₁.toFeynmanGraph.toClass = G₂.toFeynmanGraph.toClass :=
    (FeynmanGraph.toClass_eq_iff _ _).mpr ⟨π, hπ⟩
  -- Split the three-additive-term equality into (boundary terms) + (sum).
  -- Unify the "genG" locally defined on each side via hClass.
  have hGen : (⟨G₁.toFeynmanGraph.toClass,
      (FeynmanGraphClass.isSupportConnected_toClass G₁.toFeynmanGraph).mpr
        G₁.isSupportConnected⟩ : HopfGenTemp) =
      ⟨G₂.toFeynmanGraph.toClass,
       (FeynmanGraphClass.isSupportConnected_toClass G₂.toFeynmanGraph).mpr
         G₂.isSupportConnected⟩ := Subtype.ext hClass
  -- Unfold `gen_temp` references (all are `MvPolynomial.X` of HopfGenTemp).
  simp only [gen_temp]
  -- Rewrite the two `G₁.toFeynmanGraph`-based generators to `G₂.toFeynmanGraph`.
  rw [hGen]
  -- The boundary terms are now identical on both sides. Only the sum differs.
  congr 1
  · -- Sum terms: reindex via mapPermSubgraph.
    -- After `rw [coproductGen_eq]`, the goal is
    -- `∑ γ ∈ index(G₁), if_body` = `∑ γ ∈ index(G₂), if_body`.
    apply Finset.sum_bij (fun γ _ => mapPermSubgraph hπ γ)
    · -- maps-into
      intro γ hγ
      exact (mapPermSubgraph_mem_index_iff hπ γ).mpr hγ
    · -- injective: mapPermSubgraph hπ is injective on subgraphs since
      -- its three data fields are images/maps of γ's under an injective π.
      intro γ₁ _ γ₂ _ heq
      apply FeynmanSubgraph.ext_iff.mpr
      have hELInj : Function.Injective (ExternalLeg.map π) := by
        intro ℓ₁ ℓ₂ h
        cases ℓ₁ with
        | mk a₁ s₁ =>
          cases ℓ₂ with
          | mk a₂ s₂ =>
            -- h : ExternalLeg.map π ⟨a₁,s₁⟩ = ExternalLeg.map π ⟨a₂,s₂⟩
            -- i.e. ⟨π a₁, s₁⟩ = ⟨π a₂, s₂⟩
            have hπa : π a₁ = π a₂ := congrArg ExternalLeg.attachedTo h
            have hs : s₁ = s₂ := congrArg ExternalLeg.sector h
            have : a₁ = a₂ := π.injective hπa
            subst this; subst hs; rfl
      refine ⟨?_, ?_, ?_⟩
      · have h := congrArg FeynmanSubgraph.vertices heq
        rw [mapPermSubgraph_vertices, mapPermSubgraph_vertices] at h
        exact Finset.image_injective π.injective h
      · have h := congrArg FeynmanSubgraph.internalEdges heq
        rw [mapPermSubgraph_internalEdges, mapPermSubgraph_internalEdges] at h
        exact Multiset.map_injective
          (FeynmanGraph.FeynmanEdge_map_injective π) h
      · have h := congrArg FeynmanSubgraph.externalLegs heq
        rw [mapPermSubgraph_externalLegs, mapPermSubgraph_externalLegs] at h
        exact Multiset.map_injective hELInj h
    · -- surjective: use mapPermSubgraph_preimage.
      intro γ' hγ'
      refine ⟨mapPermSubgraph_preimage hπ γ', ?_,
        mapPermSubgraph_preimage_eq hπ γ'⟩
      -- Need: mapPermSubgraph_preimage hπ γ' ∈ G₁.properConnectedDivergentSubgraphs.
      -- Apply mapPermSubgraph_mem_index_iff to `mapPermSubgraph_preimage hπ γ'`:
      -- its image under mapPermSubgraph hπ is γ' (by mapPermSubgraph_preimage_eq),
      -- which is in G₂.index by hγ'.
      have := (mapPermSubgraph_mem_index_iff hπ
        (mapPermSubgraph_preimage hπ γ')).mp
      rw [mapPermSubgraph_preimage_eq] at this
      exact this hγ'
    · -- per-term equality
      intro γ hγ
      have hγ'full := (G₁.toFeynmanGraph.mem_properConnectedDivergentSubgraphs γ).mp hγ
      have hγ''full := (G₂.toFeynmanGraph.mem_properConnectedDivergentSubgraphs
          (mapPermSubgraph hπ γ)).mp
        ((mapPermSubgraph_mem_index_iff hπ γ).mpr hγ)
      have hγ' : γ.IsConnectedDivergent ∧ 0 < γ.internalEdges.card :=
        ⟨hγ'full.1, hγ'full.2.1⟩
      have hγ'' : (mapPermSubgraph hπ γ).IsConnectedDivergent ∧
          0 < (mapPermSubgraph hπ γ).internalEdges.card :=
        ⟨hγ''full.1, hγ''full.2.1⟩
      rw [dif_pos hγ', dif_pos hγ'']
      -- Build subtype equalities for both tensor factors.
      have hLeft : (γ.toHopfGenTemp hγ'.1.isConnected) =
          (mapPermSubgraph hπ γ).toHopfGenTemp hγ''.1.isConnected :=
        Subtype.ext (mapPermSubgraph_toClass_eq hπ γ).symm
      have hRight :
          (FeynmanSubgraph.contractToHopfGenTemp G₁.isSupportConnected γ
            hγ'.1.isConnected
            (FeynmanSubgraph.isNonempty_of_internalEdges_pos hγ'.2)) =
          (FeynmanSubgraph.contractToHopfGenTemp G₂.isSupportConnected
            (mapPermSubgraph hπ γ) hγ''.1.isConnected
            (FeynmanSubgraph.isNonempty_of_internalEdges_pos hγ''.2)) :=
        Subtype.ext (mapPermSubgraph_contract_toClass_eq hG₁wf hπ γ).symm
      rw [hLeft, hRight]

/-! ### Phase C — H4.7/H4.8 class-lift + `MvPolynomial.aeval` extension

Phase B built `coproductGen : ConnectedFeynmanGraph → HopfH_temp ⊗ HopfH_temp`
and proved isomorphism invariance (H4.6). Phase C lifts this to the
generator subtype `HopfGen` (via picking a well-formed connected
representative) and extends multiplicatively to `HopfH` via
`MvPolynomial.aeval`.

## H4.7 design

`HopfGen := { c : FeynmanGraphClass // c.IsConnectedDivergent }` where
`FeynmanGraphClass.IsConnectedDivergent` delegates (Sprint C1 H3.6) to
`FeynmanGraph.IsConnectedDivergent`, which is
`∃ hG : G.WellFormed, (self G hG).IsConnectedDivergent`. So every
`HopfGen` element carries (implicitly, through the quotient) a
`WellFormed` witness for some representative.

We pick such a representative via `Quotient.hrecOn` + the witness, build
a `ConnectedFeynmanGraph`, feed to `coproductGen`, and use H4.6 for
well-definedness.
-/

/-- Given a `HopfGen` element (a class-level connected-divergent
witness), produce a `ConnectedFeynmanGraph` representative and its
well-formedness witness. Uses `Classical.choice` to pick a graph
representative; the connectedness + well-formedness witnesses flow
from `IsConnectedDivergent`. -/
noncomputable def HopfGen.toConnectedWF (g : HopfGen) :
    Σ' (G : ConnectedFeynmanGraph), G.toFeynmanGraph.WellFormed := by
  -- g.val : FeynmanGraphClass; choose a representative G.
  -- Use Quotient.out: FeynmanGraphClass → FeynmanGraph.
  let G := Quotient.out g.val
  -- g.property : g.val.IsConnectedDivergent
  -- By design (Sprint C1), this is a Quotient.lift of
  -- FeynmanGraph.IsConnectedDivergent; on the specific representative G = Quotient.out g.val,
  -- `g.val = G.toClass` holds (Quotient.out_eq).
  have hClassEq : G.toClass = g.val := Quotient.out_eq _
  have hCD : G.IsConnectedDivergent := by
    -- g.property : g.val.IsConnectedDivergent.
    -- By isConnectedDivergent_toClass (simp) + Quotient.out_eq,
    -- reducing the class-level IsCD to G.IsCD.
    have := g.property
    rw [← hClassEq] at this
    exact (FeynmanGraphClass.isConnectedDivergent_toClass G).mp this
  have hWF : G.WellFormed := hCD.wellFormed
  -- Now build ConnectedFeynmanGraph from G + connectedness witness.
  -- Connectedness witness: IsConnectedDivergent decomposes to
  -- the "self.IsConnected" which is G.IsSupportConnected.
  have hConn : G.IsSupportConnected := by
    have hself := hCD.self_isConnectedDivergent
    exact hself.1
  exact ⟨ConnectedFeynmanGraph.mk' G hConn, hWF⟩

@[simp] theorem HopfGen.toConnectedWF_toFeynmanGraph_toClass (g : HopfGen) :
    (HopfGen.toConnectedWF g).1.toFeynmanGraph.toClass = g.val := by
  unfold HopfGen.toConnectedWF
  exact Quotient.out_eq _

/-! ### Sprint E shared API — `repG` canonical representative

The following definitions extract the canonical `ConnectedFeynmanGraph`
representative of a `HopfGen` element, together with the `WellFormed`
/ `IsConnectedDivergent` / `IsOnePI` witnesses. These are shared between
the `coproduct_strict_forest` machinery and the Sprint E antipode
construction, so they belong in `Coproduct.lean` (the file that owns
the strict-forest carrier definitions).

Originally defined in `Coassoc.lean` during Sprint D; promoted here
in Sprint E to avoid an Antipode → Coassoc → Counit → Coproduct
reverse-import cycle when assembling the Hopf algebra instance. -/

/-- The chosen `ConnectedFeynmanGraph` representative of a `HopfGen`
element (via `Quotient.out`). -/
noncomputable def repG (g : HopfGen) : ConnectedFeynmanGraph :=
  (HopfGen.toConnectedWF g).1

theorem repG_wellFormed (g : HopfGen) : (repG g).toFeynmanGraph.WellFormed :=
  (HopfGen.toConnectedWF g).2

theorem repG_toClass (g : HopfGen) :
    (repG g).toFeynmanGraph.toClass = g.val :=
  HopfGen.toConnectedWF_toFeynmanGraph_toClass g

theorem repG_isConnectedDivergent (g : HopfGen) :
    (repG g).toFeynmanGraph.IsConnectedDivergent :=
  (FeynmanGraphClass.isConnectedDivergent_toClass (repG g).toFeynmanGraph).mp
    ((repG_toClass g) ▸ g.property)

theorem repG_isOnePI (g : HopfGen) :
    (repG g).toFeynmanGraph.IsOnePI :=
  (repG_isConnectedDivergent g).self_isConnectedDivergent.isOnePI

/-- **H4.7** — The coproduct evaluated on a strict CK generator.
Well-definedness (i.e. class-level independence of the chosen
representative) uses H4.6 `coproductGen_isomorphism_invariant`. -/
noncomputable def coproductGenClass (g : HopfGen) : HopfH_temp ⊗[ℚ] HopfH_temp :=
  coproductGen (HopfGen.toConnectedWF g).1

/-! ### H4.8 — extend multiplicatively via `MvPolynomial.aeval` -/

/-- **H4.8** — The full coproduct `Δ : HopfH →ₐ[ℚ] HopfH_temp ⊗ HopfH_temp`,
obtained by extending `coproductGenClass` algebraically via the
universal property of `MvPolynomial`.

Type-level note: the target is `HopfH_temp ⊗ HopfH_temp`, not
`HopfH ⊗ HopfH`. Composing with `bridge` (Sprint C1 H3.9) recovers
the `HopfH ⊗ HopfH`-valued form when needed; for now `HopfH_temp`
is the natural target because the coproduct values are `gen_temp`-based.
-/
noncomputable def coproduct : HopfH →ₐ[ℚ] HopfH_temp ⊗[ℚ] HopfH_temp :=
  MvPolynomial.aeval coproductGenClass

/-! ### H4.9 / H4.10 / H4.11 — basic Hopf-algebra-hom compatibilities -/

/-- **H4.9** — On a generator `X g`, the coproduct equals
`coproductGenClass g`. -/
theorem coproduct_X (g : HopfGen) :
    coproduct (MvPolynomial.X g) = coproductGenClass g := by
  unfold coproduct
  rw [MvPolynomial.aeval_X]

/-- **H4.10** — `coproduct 1 = 1`. From `AlgHom.map_one`. -/
@[simp] theorem coproduct_one : coproduct (1 : HopfH) = 1 := map_one _

/-- **H4.11** — `coproduct` is multiplicative. From `AlgHom.map_mul`. -/
theorem coproduct_mul (a b : HopfH) :
    coproduct (a * b) = coproduct a * coproduct b := map_mul _ _ _

/-! ### Strict CK coproduct — Path-B parallel chain (Sprint D, 2026-04-25)

The Phase A–C chain above lands in `HopfH_temp ⊗ HopfH_temp` (Plan-D
Hybrid scaffold target). Sprint D's `Bialgebra ℚ HopfH` requires a
`comul : HopfH →ₗ[ℚ] HopfH ⊗ HopfH` — source and target both `HopfH`.

We therefore build a **parallel `coproduct_strict : HopfH →ₐ[ℚ] HopfH ⊗ HopfH`**
chain alongside the existing one. Every `gen_temp _` becomes a `gen _`
(strict CK generator), every `toHopfGenTemp` becomes `toHopfGen` (which
internally uses Path-W typeclass #4 `IsAmbientInvariantDivergence` to
lift subgraph-level divergence to graph-level), and every
`contractToHopfGenTemp` becomes `contractToHopfGen` (which additionally
uses `IsDivergencePreservedByContract` for divergence preservation).

The original `coproductGen` / `coproduct` chain is preserved as
internal scaffolding, mirroring Sprint A's `contractWith` / `contract`
and Sprint C1's `HopfH_temp` / `HopfH` patterns. -/

section Strict

variable [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]

/-! ### Minimal admissible generator product

This is the first reusable API for the admissible-subgraph redesign:
an admissible forest contributes the product of its connected-divergent
components as strict generators. The coproduct index itself is intentionally
not changed in this pass.
-/

namespace AdmissibleSubgraph

variable {G : FeynmanGraph}

/-- Product of the Hopf generators carried by an admissible subgraph. -/
noncomputable def componentToHopfH
    (A : AdmissibleSubgraph G) (γ : FeynmanSubgraph G) : HopfH :=
  if hγ : γ ∈ A.elements then
    gen (γ.toHopfGen (A.isConnectedDivergent_of_mem hγ))
  else
    1

/-- Product of the Hopf generators carried by an admissible subgraph. -/
noncomputable def toHopfH (A : AdmissibleSubgraph G) : HopfH :=
  ∏ γ ∈ A.elements, componentToHopfH A γ

@[simp] theorem empty_toHopfH (G : FeynmanGraph) :
    (empty G).toHopfH = (1 : HopfH) := by
  rw [toHopfH, empty_elements]
  simp

@[simp] theorem singleton_toHopfH
    (γ : FeynmanSubgraph G) (hγ : γ.IsConnectedDivergent) :
    (singleton γ hγ).toHopfH = gen (γ.toHopfGen hγ) := by
  rw [toHopfH, singleton_elements, Finset.prod_singleton]
  unfold componentToHopfH
  rw [dif_pos (by simp)]

end AdmissibleSubgraph

namespace FeynmanGraph

variable (G : FeynmanGraph)

/-- The conservative singleton embedding contributes exactly the existing
strict connected generator as its admissible product. -/
@[simp] theorem connectedIndexToAdmissible_toHopfH
    (γ : {γ : FeynmanSubgraph G // γ ∈ G.properConnectedDivergentSubgraphs}) :
    (connectedIndexToAdmissible G γ).toHopfH =
      gen (γ.1.toHopfGen
        (G.properConnectedDivergentSubgraphs_isConnectedDivergent γ.2)) := by
  simp [connectedIndexToAdmissible]

/-- The strict coproduct's existing `if`-guarded generator expression
matches the singleton admissible product on the conservative index. -/
theorem connectedIndexToAdmissible_toHopfH_eq_if
    (γ : {γ : FeynmanSubgraph G // γ ∈ G.properConnectedDivergentSubgraphs}) :
    (if hγ : γ.1.IsConnectedDivergent ∧ 0 < γ.1.internalEdges.card then
      gen (γ.1.toHopfGen hγ.1)
    else 0)
      =
    (connectedIndexToAdmissible G γ).toHopfH := by
  have hγ : γ.1.IsConnectedDivergent ∧ 0 < γ.1.internalEdges.card :=
    ⟨G.properConnectedDivergentSubgraphs_isConnectedDivergent γ.2,
      G.properConnectedDivergentSubgraphs_internalEdges_pos γ.2⟩
  rw [dif_pos hγ]
  simp [connectedIndexToAdmissible]

/-- Connected-divergent generator sums can be reindexed through the
conservative singleton admissible index, with `toHopfH` as the
admissible product. This is the first concrete connected-sum →
singleton-admissible-sum bridge for the strict coproduct. -/
theorem sum_properConnectedDivergentSubgraphs_toHopfH
    (G : FeynmanGraph) :
    (∑ γ ∈ G.properConnectedDivergentSubgraphs,
      if hγ : γ.IsConnectedDivergent ∧ 0 < γ.internalEdges.card then
        gen (γ.toHopfGen hγ.1)
      else 0)
      =
    ∑ A ∈ G.properAdmissibleDivergentSubgraphs, A.toHopfH := by
  rw [← sum_connectedIndexToAdmissible_eq_sum_properAdmissibleDivergentSubgraphs
    G (fun A : AdmissibleSubgraph G => A.toHopfH)]
  rw [← Finset.sum_attach G.properConnectedDivergentSubgraphs
    (fun γ : FeynmanSubgraph G =>
      if hγ : γ.IsConnectedDivergent ∧ 0 < γ.internalEdges.card then
        gen (γ.toHopfGen hγ.1)
      else 0)]
  apply Finset.sum_congr rfl
  intro γ _hγ
  exact connectedIndexToAdmissible_toHopfH_eq_if G γ

/-- Every element of the conservative admissible index is still a
singleton at the level of its product of strict generators. -/
theorem exists_toHopfH_eq_gen_of_mem_properAdmissibleDivergentSubgraphs
    {A : AdmissibleSubgraph G}
    (hA : A ∈ G.properAdmissibleDivergentSubgraphs) :
    ∃ γ : FeynmanSubgraph G,
      ∃ hγ : γ ∈ G.properConnectedDivergentSubgraphs,
        A.toHopfH =
          gen (γ.toHopfGen
            (G.properConnectedDivergentSubgraphs_isConnectedDivergent hγ)) := by
  rcases G.mem_properAdmissibleDivergentSubgraphs_exists_singleton hA with
    ⟨γ, hγ, hAeq⟩
  refine ⟨γ, hγ, ?_⟩
  rw [hAeq]
  simp

/-- The original connected-index strict coproduct summand, isolated so it
can be reindexed before changing `coproductGen_strict` itself. -/
noncomputable def connectedStrictSummand
    (G : FeynmanGraph) (hGwf : G.WellFormed) (hG1PI : G.IsOnePI)
    (γ : FeynmanSubgraph G) : HopfH ⊗[ℚ] HopfH :=
  if hγ : γ.IsConnectedDivergent ∧ 0 < γ.internalEdges.card then
    let hγNe : γ.IsNonempty :=
      FeynmanSubgraph.isNonempty_of_internalEdges_pos hγ.2
    (gen (γ.toHopfGen hγ.1)) ⊗ₜ[ℚ]
      (gen (γ.contractToHopfGen hGwf hG1PI hγ.1 hγNe))
  else 0

/-- Temporary contraction component for the conservative singleton
admissible index. The full forest implementation will replace this body
with genuine admissible contraction. -/
noncomputable def admissibleContractIndex
    (G : FeynmanGraph) (A : AdmissibleSubgraph G)
    (hA : A ∈ G.properAdmissibleDivergentSubgraphs) :
    {γ : FeynmanSubgraph G // γ ∈ G.properConnectedDivergentSubgraphs} :=
  admissibleToConnectedIndex G A hA

/-- The connected component whose contraction supplies the right tensor
factor for the conservative admissible summand. -/
noncomputable def admissibleContractSubgraph
    (G : FeynmanGraph) (A : AdmissibleSubgraph G)
    (hA : A ∈ G.properAdmissibleDivergentSubgraphs) :
    FeynmanSubgraph G :=
  (admissibleContractIndex G A hA).1

theorem admissibleContractSubgraph_mem
    (G : FeynmanGraph) (A : AdmissibleSubgraph G)
    (hA : A ∈ G.properAdmissibleDivergentSubgraphs) :
    admissibleContractSubgraph G A hA ∈
      G.properConnectedDivergentSubgraphs :=
  (admissibleContractIndex G A hA).2

theorem admissibleContractSubgraph_property
    (G : FeynmanGraph) (A : AdmissibleSubgraph G)
    (hA : A ∈ G.properAdmissibleDivergentSubgraphs) :
    (admissibleContractSubgraph G A hA).IsConnectedDivergent ∧
      0 < (admissibleContractSubgraph G A hA).internalEdges.card :=
  ⟨G.properConnectedDivergentSubgraphs_isConnectedDivergent
      (admissibleContractSubgraph_mem G A hA),
    G.properConnectedDivergentSubgraphs_internalEdges_pos
      (admissibleContractSubgraph_mem G A hA)⟩

theorem admissibleContractSubgraph_isConnectedDivergent
    (G : FeynmanGraph) (A : AdmissibleSubgraph G)
    (hA : A ∈ G.properAdmissibleDivergentSubgraphs) :
    (admissibleContractSubgraph G A hA).IsConnectedDivergent :=
  (admissibleContractSubgraph_property G A hA).1

theorem admissibleContractSubgraph_isNonempty
    (G : FeynmanGraph) (A : AdmissibleSubgraph G)
    (hA : A ∈ G.properAdmissibleDivergentSubgraphs) :
    (admissibleContractSubgraph G A hA).IsNonempty :=
  FeynmanSubgraph.isNonempty_of_internalEdges_pos
    (admissibleContractSubgraph_property G A hA).2

/-- Conservative forest-contraction graph for an admissible index element.
For now the index is singleton-only, so the star assignment can use the
selected component's existing contracted vertex. -/
noncomputable def admissibleContractGraphWithStars
    (G : FeynmanGraph) (A : AdmissibleSubgraph G)
    (hA : A ∈ G.properAdmissibleDivergentSubgraphs) : FeynmanGraph :=
  A.contractWithStars
    (fun _ => (admissibleContractSubgraph G A hA).contractedVertex)

/-- The conservative singleton star assignment used by
`admissibleContractGraphWithStars` is a fresh star assignment. This is the
singleton compatibility check for the future forest-star hypotheses. -/
theorem admissibleContractGraphWithStars_isFreshStarAssignment
    (G : FeynmanGraph) (A : AdmissibleSubgraph G)
    (hA : A ∈ G.properAdmissibleDivergentSubgraphs) :
    A.IsFreshStarAssignment
      (fun _ => (admissibleContractSubgraph G A hA).contractedVertex) := by
  unfold admissibleContractSubgraph admissibleContractIndex
  let idx := admissibleToConnectedIndex G A hA
  change A.IsFreshStarAssignment (fun _ : FeynmanSubgraph G => idx.1.contractedVertex)
  rw [← connectedIndexToAdmissible_admissibleToConnectedIndex G A hA]
  dsimp [connectedIndexToAdmissible]
  exact AdmissibleSubgraph.singleton_isFreshStarAssignment idx.1
    (G.properConnectedDivergentSubgraphs_isConnectedDivergent idx.2)

/-- On the conservative singleton-only admissible index, the forest-contraction
skeleton recovers the existing one-component contraction graph. -/
theorem admissibleContractGraphWithStars_eq_contractSubgraph
    (G : FeynmanGraph) (A : AdmissibleSubgraph G)
    (hA : A ∈ G.properAdmissibleDivergentSubgraphs) :
    admissibleContractGraphWithStars G A hA =
      (admissibleContractSubgraph G A hA).contract := by
  unfold admissibleContractGraphWithStars admissibleContractSubgraph
    admissibleContractIndex
  let idx := admissibleToConnectedIndex G A hA
  let starOf : FeynmanSubgraph G → VertexId := fun _ => idx.1.contractedVertex
  change A.contractWithStars starOf = idx.1.contract
  calc
    A.contractWithStars starOf =
        (connectedIndexToAdmissible G idx).contractWithStars starOf := by
          rw [connectedIndexToAdmissible_admissibleToConnectedIndex G A hA]
    _ = idx.1.contract := by
          dsimp [starOf, connectedIndexToAdmissible]
          rw [AdmissibleSubgraph.singleton_contractWithStars_contract]
          rfl

/-- Right tensor generator for the conservative admissible summand.
This is the named replacement point for the future forest contraction API. -/
noncomputable def admissibleContractToHopfGen
    (G : FeynmanGraph) (hGwf : G.WellFormed) (hG1PI : G.IsOnePI)
    (A : AdmissibleSubgraph G)
    (hA : A ∈ G.properAdmissibleDivergentSubgraphs) : HopfGen :=
  (admissibleContractSubgraph G A hA).contractToHopfGen hGwf hG1PI
    (admissibleContractSubgraph_isConnectedDivergent G A hA)
    (admissibleContractSubgraph_isNonempty G A hA)

/-- Right tensor generator packaged from the forest-contraction skeleton. On
the conservative singleton index this is propositionally the same generator as
`admissibleContractToHopfGen`. -/
noncomputable def admissibleContractGraphWithStarsToHopfGen
    (G : FeynmanGraph) (hGwf : G.WellFormed) (hG1PI : G.IsOnePI)
    (A : AdmissibleSubgraph G)
    (hA : A ∈ G.properAdmissibleDivergentSubgraphs) : HopfGen :=
  ⟨(admissibleContractGraphWithStars G A hA).toClass, by
    rw [admissibleContractGraphWithStars_eq_contractSubgraph G A hA]
    exact (admissibleContractToHopfGen G hGwf hG1PI A hA).property⟩

theorem admissibleContractGraphWithStarsToHopfGen_eq
    (G : FeynmanGraph) (hGwf : G.WellFormed) (hG1PI : G.IsOnePI)
    (A : AdmissibleSubgraph G)
    (hA : A ∈ G.properAdmissibleDivergentSubgraphs) :
    admissibleContractGraphWithStarsToHopfGen G hGwf hG1PI A hA =
      admissibleContractToHopfGen G hGwf hG1PI A hA := by
  apply Subtype.ext
  simp [admissibleContractGraphWithStarsToHopfGen,
    admissibleContractToHopfGen,
    admissibleContractGraphWithStars_eq_contractSubgraph]

theorem admissibleContractIndex_connectedIndexToAdmissible
    (G : FeynmanGraph)
    (γ : {γ : FeynmanSubgraph G // γ ∈ G.properConnectedDivergentSubgraphs})
    (hA : connectedIndexToAdmissible G γ ∈
      G.properAdmissibleDivergentSubgraphs) :
    admissibleContractIndex G (connectedIndexToAdmissible G γ) hA = γ := by
  unfold admissibleContractIndex
  exact admissibleToConnectedIndex_connectedIndexToAdmissible G γ hA

theorem admissibleContractSubgraph_connectedIndexToAdmissible
    (G : FeynmanGraph)
    (γ : {γ : FeynmanSubgraph G // γ ∈ G.properConnectedDivergentSubgraphs})
    (hA : connectedIndexToAdmissible G γ ∈
      G.properAdmissibleDivergentSubgraphs) :
    admissibleContractSubgraph G (connectedIndexToAdmissible G γ) hA =
      γ.1 := by
  unfold admissibleContractSubgraph
  rw [admissibleContractIndex_connectedIndexToAdmissible G γ hA]

/-- On singleton admissible elements, the named admissible contraction
generator is the original connected contraction generator. -/
theorem admissibleContractToHopfGen_connectedIndexToAdmissible
    (G : FeynmanGraph) (hGwf : G.WellFormed) (hG1PI : G.IsOnePI)
    (γ : {γ : FeynmanSubgraph G // γ ∈ G.properConnectedDivergentSubgraphs})
    (hA : connectedIndexToAdmissible G γ ∈
      G.properAdmissibleDivergentSubgraphs) :
    admissibleContractToHopfGen G hGwf hG1PI
        (connectedIndexToAdmissible G γ) hA =
      γ.1.contractToHopfGen hGwf hG1PI
        (G.properConnectedDivergentSubgraphs_isConnectedDivergent γ.2)
        (FeynmanSubgraph.isNonempty_of_internalEdges_pos
          (G.properConnectedDivergentSubgraphs_internalEdges_pos γ.2)) := by
  apply Subtype.ext
  simp [admissibleContractToHopfGen,
    admissibleContractSubgraph_connectedIndexToAdmissible]

/-- The same strict coproduct summand, but indexed by the conservative
singleton admissible index. The right tensor factor is obtained by the
temporary conservative inverse `admissibleToConnectedIndex`; in the full
forest version this is where genuine admissible contraction will sit. -/
noncomputable def admissibleStrictSummand
    (G : FeynmanGraph) (hGwf : G.WellFormed) (hG1PI : G.IsOnePI)
    (A : AdmissibleSubgraph G) : HopfH ⊗[ℚ] HopfH :=
  if hA : A ∈ G.properAdmissibleDivergentSubgraphs then
    A.toHopfH ⊗ₜ[ℚ]
      (gen (admissibleContractToHopfGen G hGwf hG1PI A hA))
  else 0

/-- Parametric admissible strict summand over an arbitrary finite admissible
carrier. The right tensor generator is supplied externally, so this definition
does not depend on the conservative singleton inverse. -/
noncomputable def admissibleStrictSummandWithRight
    (G : FeynmanGraph) (I : Finset (AdmissibleSubgraph G))
    (right : ∀ A : AdmissibleSubgraph G, A ∈ I → HopfGen)
    (A : AdmissibleSubgraph G) : HopfH ⊗[ℚ] HopfH :=
  if hA : A ∈ I then
    A.toHopfH ⊗ₜ[ℚ] (gen (right A hA))
  else 0

/-- The future forest strict summand shape over the proper disjoint
admissible carrier. The remaining mathematical work is to construct the
`right` generator from genuine forest contraction. -/
noncomputable def admissibleForestStrictSummand
    (G : FeynmanGraph)
    (right : ∀ A : AdmissibleSubgraph G,
      A ∈ G.properDisjointAdmissibleDivergentSubgraphs → HopfGen)
    (A : AdmissibleSubgraph G) : HopfH ⊗[ℚ] HopfH :=
  admissibleStrictSummandWithRight G
    G.properDisjointAdmissibleDivergentSubgraphs right A

/-- Genuine forest-contraction graph with a caller-supplied component-star
assignment. This is only a named wrapper around `AdmissibleSubgraph.contractWithStars`,
but it gives the future right tensor factor a stable API. -/
noncomputable def admissibleForestContractGraphWithStars
    (G : FeynmanGraph) (A : AdmissibleSubgraph G)
    (starOf : FeynmanSubgraph G → VertexId) : FeynmanGraph :=
  A.contractWithStars starOf

@[simp] theorem admissibleForestContractGraphWithStars_eq
    (G : FeynmanGraph) (A : AdmissibleSubgraph G)
    (starOf : FeynmanSubgraph G → VertexId) :
    admissibleForestContractGraphWithStars G A starOf =
      A.contractWithStars starOf := rfl

/-- Package a forest-contraction graph as a strict Hopf generator, assuming
the connected-divergent preservation proof has already been supplied. -/
noncomputable def admissibleForestContractToHopfGen
    (G : FeynmanGraph) (A : AdmissibleSubgraph G)
    (starOf : FeynmanSubgraph G → VertexId)
    (hCD : (admissibleForestContractGraphWithStars G A starOf).IsConnectedDivergent) :
    HopfGen :=
  ⟨(admissibleForestContractGraphWithStars G A starOf).toClass,
    (FeynmanGraphClass.isConnectedDivergent_toClass
      (admissibleForestContractGraphWithStars G A starOf)).mpr hCD⟩

@[simp] theorem admissibleForestContractToHopfGen_val
    (G : FeynmanGraph) (A : AdmissibleSubgraph G)
    (starOf : FeynmanSubgraph G → VertexId)
    (hCD : (admissibleForestContractGraphWithStars G A starOf).IsConnectedDivergent) :
    (admissibleForestContractToHopfGen G A starOf hCD).val =
      (admissibleForestContractGraphWithStars G A starOf).toClass := rfl

/-- The right tensor generator for a genuine forest summand, assuming both
the component-star assignment and the connected-divergent preservation proof
are supplied for each element of the proper-disjoint admissible carrier. -/
noncomputable def admissibleForestRightWithStars
    (G : FeynmanGraph)
    (starOf : ∀ A : AdmissibleSubgraph G,
      A ∈ G.properDisjointAdmissibleDivergentSubgraphs →
        FeynmanSubgraph G → VertexId)
    (hCD : ∀ A : AdmissibleSubgraph G,
      ∀ hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
        (admissibleForestContractGraphWithStars G A (starOf A hA)).IsConnectedDivergent)
    (A : AdmissibleSubgraph G)
    (hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs) :
    HopfGen :=
  admissibleForestContractToHopfGen G A (starOf A hA) (hCD A hA)

/-- Same right tensor generator as `admissibleForestRightWithStars`, but with
the freshness/injectivity hypothesis made explicit in the API. The current
body only needs `hCD`; preservation lemmas will consume `hFresh`. -/
noncomputable def admissibleForestRightWithFreshStars
    (G : FeynmanGraph)
    (starOf : ∀ A : AdmissibleSubgraph G,
      A ∈ G.properDisjointAdmissibleDivergentSubgraphs →
        FeynmanSubgraph G → VertexId)
    (_hFresh : ∀ A : AdmissibleSubgraph G,
      ∀ hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
        A.IsFreshStarAssignment (starOf A hA))
    (hCD : ∀ A : AdmissibleSubgraph G,
      ∀ hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
        (admissibleForestContractGraphWithStars G A (starOf A hA)).IsConnectedDivergent)
    (A : AdmissibleSubgraph G)
    (hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs) :
    HopfGen :=
  admissibleForestRightWithStars G starOf hCD A hA

theorem admissibleForestRightWithFreshStars_eq
    (G : FeynmanGraph)
    (starOf : ∀ A : AdmissibleSubgraph G,
      A ∈ G.properDisjointAdmissibleDivergentSubgraphs →
        FeynmanSubgraph G → VertexId)
    (hFresh : ∀ A : AdmissibleSubgraph G,
      ∀ hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
        A.IsFreshStarAssignment (starOf A hA))
    (hCD : ∀ A : AdmissibleSubgraph G,
      ∀ hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
        (admissibleForestContractGraphWithStars G A (starOf A hA)).IsConnectedDivergent)
    (A : AdmissibleSubgraph G)
    (hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs) :
    admissibleForestRightWithFreshStars G starOf hFresh hCD A hA =
      admissibleForestRightWithStars G starOf hCD A hA := rfl

@[simp] theorem admissibleForestRightWithFreshStars_val
    (G : FeynmanGraph)
    (starOf : ∀ A : AdmissibleSubgraph G,
      A ∈ G.properDisjointAdmissibleDivergentSubgraphs →
        FeynmanSubgraph G → VertexId)
    (hFresh : ∀ A : AdmissibleSubgraph G,
      ∀ hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
        A.IsFreshStarAssignment (starOf A hA))
    (hCD : ∀ A : AdmissibleSubgraph G,
      ∀ hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
        (admissibleForestContractGraphWithStars G A (starOf A hA)).IsConnectedDivergent)
    (A : AdmissibleSubgraph G)
    (hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs) :
    (admissibleForestRightWithFreshStars G starOf hFresh hCD A hA).val =
      (admissibleForestContractGraphWithStars G A (starOf A hA)).toClass := rfl

@[simp] theorem admissibleForestRightWithStars_val
    (G : FeynmanGraph)
    (starOf : ∀ A : AdmissibleSubgraph G,
      A ∈ G.properDisjointAdmissibleDivergentSubgraphs →
        FeynmanSubgraph G → VertexId)
    (hCD : ∀ A : AdmissibleSubgraph G,
      ∀ hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
        (admissibleForestContractGraphWithStars G A (starOf A hA)).IsConnectedDivergent)
    (A : AdmissibleSubgraph G)
    (hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs) :
    (admissibleForestRightWithStars G starOf hCD A hA).val =
      (admissibleForestContractGraphWithStars G A (starOf A hA)).toClass := rfl

/-- Future forest strict summand specialized to component-star contraction.
The hard theorem still to prove is the preservation hypothesis `hCD`. -/
noncomputable def admissibleForestStrictSummandWithStars
    (G : FeynmanGraph)
    (starOf : ∀ A : AdmissibleSubgraph G,
      A ∈ G.properDisjointAdmissibleDivergentSubgraphs →
        FeynmanSubgraph G → VertexId)
    (hCD : ∀ A : AdmissibleSubgraph G,
      ∀ hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
        (admissibleForestContractGraphWithStars G A (starOf A hA)).IsConnectedDivergent)
    (A : AdmissibleSubgraph G) : HopfH ⊗[ℚ] HopfH :=
  admissibleForestStrictSummand G
    (admissibleForestRightWithStars G starOf hCD) A

theorem admissibleForestStrictSummandWithStars_of_mem
    (G : FeynmanGraph)
    (starOf : ∀ A : AdmissibleSubgraph G,
      A ∈ G.properDisjointAdmissibleDivergentSubgraphs →
        FeynmanSubgraph G → VertexId)
    (hCD : ∀ A : AdmissibleSubgraph G,
      ∀ hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
        (admissibleForestContractGraphWithStars G A (starOf A hA)).IsConnectedDivergent)
    (A : AdmissibleSubgraph G)
    (hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs) :
    admissibleForestStrictSummandWithStars G starOf hCD A =
      A.toHopfH ⊗ₜ[ℚ]
        (gen (admissibleForestRightWithStars G starOf hCD A hA)) := by
  unfold admissibleForestStrictSummandWithStars admissibleForestStrictSummand
    admissibleStrictSummandWithRight
  rw [dif_pos hA]

theorem admissibleForestStrictSummandWithStars_of_not_mem
    (G : FeynmanGraph)
    (starOf : ∀ A : AdmissibleSubgraph G,
      A ∈ G.properDisjointAdmissibleDivergentSubgraphs →
        FeynmanSubgraph G → VertexId)
    (hCD : ∀ A : AdmissibleSubgraph G,
      ∀ hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
        (admissibleForestContractGraphWithStars G A (starOf A hA)).IsConnectedDivergent)
    (A : AdmissibleSubgraph G)
    (hA : A ∉ G.properDisjointAdmissibleDivergentSubgraphs) :
    admissibleForestStrictSummandWithStars G starOf hCD A = 0 := by
  unfold admissibleForestStrictSummandWithStars admissibleForestStrictSummand
    admissibleStrictSummandWithRight
  rw [dif_neg hA]

/-- Future forest strict summand with the fresh-star hypothesis explicitly
present in the API. The body is the same as
`admissibleForestStrictSummandWithStars`; the point is to expose the exact
hypotheses the preservation theorem will use. -/
noncomputable def admissibleForestStrictSummandWithFreshStars
    (G : FeynmanGraph)
    (starOf : ∀ A : AdmissibleSubgraph G,
      A ∈ G.properDisjointAdmissibleDivergentSubgraphs →
        FeynmanSubgraph G → VertexId)
    (hFresh : ∀ A : AdmissibleSubgraph G,
      ∀ hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
        A.IsFreshStarAssignment (starOf A hA))
    (hCD : ∀ A : AdmissibleSubgraph G,
      ∀ hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
        (admissibleForestContractGraphWithStars G A (starOf A hA)).IsConnectedDivergent)
    (A : AdmissibleSubgraph G) : HopfH ⊗[ℚ] HopfH :=
  admissibleForestStrictSummand G
    (admissibleForestRightWithFreshStars G starOf hFresh hCD) A

theorem admissibleForestStrictSummandWithFreshStars_eq
    (G : FeynmanGraph)
    (starOf : ∀ A : AdmissibleSubgraph G,
      A ∈ G.properDisjointAdmissibleDivergentSubgraphs →
        FeynmanSubgraph G → VertexId)
    (hFresh : ∀ A : AdmissibleSubgraph G,
      ∀ hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
        A.IsFreshStarAssignment (starOf A hA))
    (hCD : ∀ A : AdmissibleSubgraph G,
      ∀ hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
        (admissibleForestContractGraphWithStars G A (starOf A hA)).IsConnectedDivergent)
    (A : AdmissibleSubgraph G) :
    admissibleForestStrictSummandWithFreshStars G starOf hFresh hCD A =
      admissibleForestStrictSummandWithStars G starOf hCD A := by
  unfold admissibleForestStrictSummandWithFreshStars
    admissibleForestStrictSummandWithStars admissibleForestStrictSummand
    admissibleStrictSummandWithRight
  by_cases hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs
  · simp [hA, admissibleForestRightWithFreshStars_eq]
  · simp [hA]

theorem admissibleForestStrictSummandWithFreshStars_of_mem
    (G : FeynmanGraph)
    (starOf : ∀ A : AdmissibleSubgraph G,
      A ∈ G.properDisjointAdmissibleDivergentSubgraphs →
        FeynmanSubgraph G → VertexId)
    (hFresh : ∀ A : AdmissibleSubgraph G,
      ∀ hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
        A.IsFreshStarAssignment (starOf A hA))
    (hCD : ∀ A : AdmissibleSubgraph G,
      ∀ hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
        (admissibleForestContractGraphWithStars G A (starOf A hA)).IsConnectedDivergent)
    (A : AdmissibleSubgraph G)
    (hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs) :
    admissibleForestStrictSummandWithFreshStars G starOf hFresh hCD A =
      A.toHopfH ⊗ₜ[ℚ]
        (gen (admissibleForestRightWithFreshStars G starOf hFresh hCD A hA)) := by
  unfold admissibleForestStrictSummandWithFreshStars admissibleForestStrictSummand
    admissibleStrictSummandWithRight
  rw [dif_pos hA]

theorem admissibleForestStrictSummandWithFreshStars_of_not_mem
    (G : FeynmanGraph)
    (starOf : ∀ A : AdmissibleSubgraph G,
      A ∈ G.properDisjointAdmissibleDivergentSubgraphs →
        FeynmanSubgraph G → VertexId)
    (hFresh : ∀ A : AdmissibleSubgraph G,
      ∀ hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
        A.IsFreshStarAssignment (starOf A hA))
    (hCD : ∀ A : AdmissibleSubgraph G,
      ∀ hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
        (admissibleForestContractGraphWithStars G A (starOf A hA)).IsConnectedDivergent)
    (A : AdmissibleSubgraph G)
    (hA : A ∉ G.properDisjointAdmissibleDivergentSubgraphs) :
    admissibleForestStrictSummandWithFreshStars G starOf hFresh hCD A = 0 := by
  unfold admissibleForestStrictSummandWithFreshStars admissibleForestStrictSummand
    admissibleStrictSummandWithRight
  rw [dif_neg hA]

/-- Canonical component-star assignment for a proper-disjoint admissible
forest, obtained from the finite component carrier itself. -/
noncomputable def admissibleForestCanonicalStarOf
    (G : FeynmanGraph) (A : AdmissibleSubgraph G)
    (_hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs) :
    FeynmanSubgraph G → VertexId :=
  A.componentFreshStar

@[simp] theorem admissibleForestCanonicalStarOf_eq
    (G : FeynmanGraph) (A : AdmissibleSubgraph G)
    (hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs) :
    admissibleForestCanonicalStarOf G A hA = A.componentFreshStar := rfl

theorem admissibleForestCanonicalStarOf_isFreshStarAssignment
    (G : FeynmanGraph) :
    ∀ A : AdmissibleSubgraph G,
      ∀ hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
        A.IsFreshStarAssignment (admissibleForestCanonicalStarOf G A hA) := by
  intro A _hA
  exact A.componentFreshStar_isFreshStarAssignment

/-- Canonical forest-contraction graph for a proper-disjoint admissible
carrier. This is just `contractWithStars` with the canonical component-star
assignment, named so the remaining preservation theorem can be split into
small graph-theoretic parts. -/
noncomputable def admissibleForestCanonicalContractGraph
    (G : FeynmanGraph) (A : AdmissibleSubgraph G)
    (hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs) :
    FeynmanGraph :=
  admissibleForestContractGraphWithStars G A
    (admissibleForestCanonicalStarOf G A hA)

@[simp] theorem admissibleForestCanonicalContractGraph_eq
    (G : FeynmanGraph) (A : AdmissibleSubgraph G)
    (hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs) :
    admissibleForestCanonicalContractGraph G A hA =
      admissibleForestContractGraphWithStars G A
        (admissibleForestCanonicalStarOf G A hA) := rfl

theorem admissibleForestCanonicalContractGraph_isConnectedDivergent_of_parts
    (G : FeynmanGraph) (A : AdmissibleSubgraph G)
    (hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs)
    (hWF : (admissibleForestCanonicalContractGraph G A hA).WellFormed)
    (hConn : (admissibleForestCanonicalContractGraph G A hA).IsSupportConnected)
    (hOnePI : (admissibleForestCanonicalContractGraph G A hA).IsOnePI)
    (hDiv : (FeynmanSubgraph.self
      (admissibleForestCanonicalContractGraph G A hA) hWF).IsDivergent) :
    (admissibleForestCanonicalContractGraph G A hA).IsConnectedDivergent := by
  refine ⟨hWF, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · show (admissibleForestCanonicalContractGraph G A hA).IsSupportConnected
    exact hConn
  · show (admissibleForestCanonicalContractGraph G A hA).IsOnePI
    exact hOnePI
  · exact hDiv

theorem admissibleForestCanonicalContractGraph_hCD_of_parts
    (G : FeynmanGraph)
    (hWF : ∀ A : AdmissibleSubgraph G,
      ∀ hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
        (admissibleForestCanonicalContractGraph G A hA).WellFormed)
    (hConn : ∀ A : AdmissibleSubgraph G,
      ∀ hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
        (admissibleForestCanonicalContractGraph G A hA).IsSupportConnected)
    (hOnePI : ∀ A : AdmissibleSubgraph G,
      ∀ hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
        (admissibleForestCanonicalContractGraph G A hA).IsOnePI)
    (hDiv : ∀ A : AdmissibleSubgraph G,
      ∀ hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
        (FeynmanSubgraph.self (admissibleForestCanonicalContractGraph G A hA)
          (hWF A hA)).IsDivergent) :
    ∀ A : AdmissibleSubgraph G,
      ∀ hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
        (admissibleForestContractGraphWithStars G A
          (admissibleForestCanonicalStarOf G A hA)).IsConnectedDivergent := by
  intro A hA
  exact admissibleForestCanonicalContractGraph_isConnectedDivergent_of_parts
    G A hA (hWF A hA) (hConn A hA) (hOnePI A hA) (hDiv A hA)

theorem admissibleForestCanonicalContractGraph_wellFormed
    (G : FeynmanGraph) (hGwf : G.WellFormed) :
    ∀ A : AdmissibleSubgraph G,
      ∀ hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
        (admissibleForestCanonicalContractGraph G A hA).WellFormed := by
  intro A hA
  unfold admissibleForestCanonicalContractGraph
    admissibleForestContractGraphWithStars
  exact A.contractWithStars_wellFormed
    (admissibleForestCanonicalStarOf G A hA) hGwf

theorem admissibleForestCanonicalContractGraph_hCD_of_graph_parts
    (G : FeynmanGraph) (hGwf : G.WellFormed)
    (hConn : ∀ A : AdmissibleSubgraph G,
      ∀ hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
        (admissibleForestCanonicalContractGraph G A hA).IsSupportConnected)
    (hOnePI : ∀ A : AdmissibleSubgraph G,
      ∀ hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
        (admissibleForestCanonicalContractGraph G A hA).IsOnePI)
    (hDiv : ∀ A : AdmissibleSubgraph G,
      ∀ hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
        (FeynmanSubgraph.self (admissibleForestCanonicalContractGraph G A hA)
          (admissibleForestCanonicalContractGraph_wellFormed G hGwf A hA)).IsDivergent) :
    ∀ A : AdmissibleSubgraph G,
      ∀ hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
        (admissibleForestContractGraphWithStars G A
          (admissibleForestCanonicalStarOf G A hA)).IsConnectedDivergent := by
  exact admissibleForestCanonicalContractGraph_hCD_of_parts G
    (admissibleForestCanonicalContractGraph_wellFormed G hGwf)
    hConn hOnePI hDiv

theorem admissibleForestCanonicalContractGraph_isSupportConnected
    (G : FeynmanGraph) (hG : G.IsSupportConnected) :
    ∀ A : AdmissibleSubgraph G,
      ∀ hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
        (admissibleForestCanonicalContractGraph G A hA).IsSupportConnected := by
  intro A hA
  unfold admissibleForestCanonicalContractGraph
    admissibleForestContractGraphWithStars
  exact A.contractWithStars_isSupportConnected hG
    (G.properDisjointAdmissibleDivergentSubgraphs_isPairwiseDisjoint hA)
    (G.properDisjointAdmissibleDivergentSubgraphs_hasNonemptyComponents hA)
    (admissibleForestCanonicalStarOf G A hA)

theorem admissibleForestCanonicalContractGraph_hCD_of_onePI_divergence
    (G : FeynmanGraph) (hGwf : G.WellFormed)
    (hGconn : G.IsSupportConnected)
    (hOnePI : ∀ A : AdmissibleSubgraph G,
      ∀ hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
        (admissibleForestCanonicalContractGraph G A hA).IsOnePI)
    (hDiv : ∀ A : AdmissibleSubgraph G,
      ∀ hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
        (FeynmanSubgraph.self (admissibleForestCanonicalContractGraph G A hA)
          (admissibleForestCanonicalContractGraph_wellFormed G hGwf A hA)).IsDivergent) :
    ∀ A : AdmissibleSubgraph G,
      ∀ hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
        (admissibleForestContractGraphWithStars G A
          (admissibleForestCanonicalStarOf G A hA)).IsConnectedDivergent := by
  exact admissibleForestCanonicalContractGraph_hCD_of_graph_parts G hGwf
    (admissibleForestCanonicalContractGraph_isSupportConnected G hGconn)
    hOnePI hDiv

theorem admissibleForestCanonicalContractGraph_noBridge_of_erase_connected
    (G : FeynmanGraph)
    (hEraseConn : ∀ A : AdmissibleSubgraph G,
      ∀ hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
        ∀ e : FeynmanEdge,
          e ∈ (admissibleForestCanonicalContractGraph G A hA).internalEdges →
            ((admissibleForestCanonicalContractGraph G A hA).eraseInternalEdge e
              ).IsSupportConnected) :
    ∀ A : AdmissibleSubgraph G,
      ∀ hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
        ∀ e : FeynmanEdge,
          e ∈ (admissibleForestCanonicalContractGraph G A hA).internalEdges →
            ¬ (admissibleForestCanonicalContractGraph G A hA).IsBridge e := by
  intro A hA e he hBridge
  exact hBridge.not_supportConnected_of_erase (hEraseConn A hA e he)

theorem admissibleForestCanonicalContractGraph_internalEdge_preimage
    (G : FeynmanGraph) {A : AdmissibleSubgraph G}
    {hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs}
    {e' : FeynmanEdge}
    (he' : e' ∈ (admissibleForestCanonicalContractGraph G A hA).internalEdges) :
    ∃ e : FeynmanEdge,
      e ∈ A.complementEdges ∧
        A.retargetEdge (admissibleForestCanonicalStarOf G A hA) e = e' := by
  unfold admissibleForestCanonicalContractGraph
    admissibleForestContractGraphWithStars at he'
  exact AdmissibleSubgraph.mem_contractWithStars_internalEdges.mp he'

theorem admissibleForestCanonicalContractGraph_retarget_erase_connected_of_onePI
    (G : FeynmanGraph) (hG : G.IsOnePI) :
    ∀ A : AdmissibleSubgraph G,
      ∀ hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
        ∀ e : FeynmanEdge,
          e ∈ A.complementEdges →
            ((admissibleForestCanonicalContractGraph G A hA).eraseInternalEdge
              (A.retargetEdge (admissibleForestCanonicalStarOf G A hA) e)
              ).IsSupportConnected := by
  intro A hA e he
  have heG : e ∈ G.internalEdges :=
    A.mem_ambientInternalEdges_of_mem_complementEdges he
  have hNoBridge : ¬ G.IsBridge e := hG.no_bridge e heG
  have hGErase : (G.eraseInternalEdge e).IsSupportConnected := by
    by_contra hnot
    exact hNoBridge ⟨heG, hnot⟩
  unfold admissibleForestCanonicalContractGraph
    admissibleForestContractGraphWithStars
  exact A.contractWithStars_eraseInternalEdge_isSupportConnected he hGErase
    (G.properDisjointAdmissibleDivergentSubgraphs_isPairwiseDisjoint hA)
    (G.properDisjointAdmissibleDivergentSubgraphs_hasNonemptyComponents hA)
    (admissibleForestCanonicalStarOf G A hA)

theorem admissibleForestCanonicalContractGraph_erase_connected_of_retarget_complement
    (G : FeynmanGraph)
    (hRetargetEraseConn : ∀ A : AdmissibleSubgraph G,
      ∀ hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
        ∀ e : FeynmanEdge,
          e ∈ A.complementEdges →
            ((admissibleForestCanonicalContractGraph G A hA).eraseInternalEdge
              (A.retargetEdge (admissibleForestCanonicalStarOf G A hA) e)
              ).IsSupportConnected) :
    ∀ A : AdmissibleSubgraph G,
      ∀ hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
        ∀ e' : FeynmanEdge,
          e' ∈ (admissibleForestCanonicalContractGraph G A hA).internalEdges →
            ((admissibleForestCanonicalContractGraph G A hA).eraseInternalEdge e'
              ).IsSupportConnected := by
  intro A hA e' he'
  rcases admissibleForestCanonicalContractGraph_internalEdge_preimage
      G (A := A) (hA := hA) he' with ⟨e, he, heq⟩
  rw [← heq]
  exact hRetargetEraseConn A hA e he

theorem admissibleForestCanonicalContractGraph_erase_connected_of_onePI
    (G : FeynmanGraph) (hG : G.IsOnePI) :
    ∀ A : AdmissibleSubgraph G,
      ∀ hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
        ∀ e' : FeynmanEdge,
          e' ∈ (admissibleForestCanonicalContractGraph G A hA).internalEdges →
            ((admissibleForestCanonicalContractGraph G A hA).eraseInternalEdge e'
              ).IsSupportConnected :=
  admissibleForestCanonicalContractGraph_erase_connected_of_retarget_complement
    G (admissibleForestCanonicalContractGraph_retarget_erase_connected_of_onePI
      G hG)

theorem admissibleForestCanonicalContractGraph_isOnePI_of_erase_connected
    (G : FeynmanGraph) (hGconn : G.IsSupportConnected)
    (hEraseConn : ∀ A : AdmissibleSubgraph G,
      ∀ hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
        ∀ e : FeynmanEdge,
          e ∈ (admissibleForestCanonicalContractGraph G A hA).internalEdges →
            ((admissibleForestCanonicalContractGraph G A hA).eraseInternalEdge e
              ).IsSupportConnected) :
    ∀ A : AdmissibleSubgraph G,
      ∀ hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
        (admissibleForestCanonicalContractGraph G A hA).IsOnePI := by
  intro A hA
  refine ⟨?_, ?_⟩
  · exact admissibleForestCanonicalContractGraph_isSupportConnected G hGconn A hA
  · exact admissibleForestCanonicalContractGraph_noBridge_of_erase_connected
      G hEraseConn A hA

theorem admissibleForestCanonicalContractGraph_isOnePI_of_ambient_onePI
    (G : FeynmanGraph) (hG : G.IsOnePI) :
    ∀ A : AdmissibleSubgraph G,
      ∀ hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
        (admissibleForestCanonicalContractGraph G A hA).IsOnePI :=
  admissibleForestCanonicalContractGraph_isOnePI_of_erase_connected
    G hG.isSupportConnected
    (admissibleForestCanonicalContractGraph_erase_connected_of_onePI G hG)

theorem admissibleForestCanonicalContractGraph_hCD_of_erase_connected_divergence
    (G : FeynmanGraph) (hGwf : G.WellFormed)
    (hGconn : G.IsSupportConnected)
    (hEraseConn : ∀ A : AdmissibleSubgraph G,
      ∀ hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
        ∀ e : FeynmanEdge,
          e ∈ (admissibleForestCanonicalContractGraph G A hA).internalEdges →
            ((admissibleForestCanonicalContractGraph G A hA).eraseInternalEdge e
              ).IsSupportConnected)
    (hDiv : ∀ A : AdmissibleSubgraph G,
      ∀ hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
        (FeynmanSubgraph.self (admissibleForestCanonicalContractGraph G A hA)
          (admissibleForestCanonicalContractGraph_wellFormed G hGwf A hA)).IsDivergent) :
    ∀ A : AdmissibleSubgraph G,
      ∀ hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
        (admissibleForestContractGraphWithStars G A
          (admissibleForestCanonicalStarOf G A hA)).IsConnectedDivergent := by
  exact admissibleForestCanonicalContractGraph_hCD_of_onePI_divergence G
    hGwf hGconn
    (admissibleForestCanonicalContractGraph_isOnePI_of_erase_connected
      G hGconn hEraseConn)
    hDiv

theorem admissibleForestCanonicalContractGraph_hCD_of_ambient_onePI_divergence
    (G : FeynmanGraph) (hGwf : G.WellFormed)
    (hG : G.IsOnePI)
    (hDiv : ∀ A : AdmissibleSubgraph G,
      ∀ hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
        (FeynmanSubgraph.self (admissibleForestCanonicalContractGraph G A hA)
          (admissibleForestCanonicalContractGraph_wellFormed G hGwf A hA)).IsDivergent) :
    ∀ A : AdmissibleSubgraph G,
      ∀ hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
        (admissibleForestContractGraphWithStars G A
          (admissibleForestCanonicalStarOf G A hA)).IsConnectedDivergent := by
  exact admissibleForestCanonicalContractGraph_hCD_of_onePI_divergence G
    hGwf hG.isSupportConnected
    (admissibleForestCanonicalContractGraph_isOnePI_of_ambient_onePI G hG)
    hDiv

theorem admissibleForestCanonicalContractGraph_isDivergent_of_ambient_connectedDivergent
    [IsDivergencePreservedByAdmissibleForestContract]
    (G : FeynmanGraph) (hGwf : G.WellFormed)
    (hGCD : G.IsConnectedDivergent) :
    ∀ A : AdmissibleSubgraph G,
      ∀ hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
        (FeynmanSubgraph.self (admissibleForestCanonicalContractGraph G A hA)
          (admissibleForestCanonicalContractGraph_wellFormed G hGwf A hA)).IsDivergent := by
  intro A hA
  have hGDiv : (FeynmanSubgraph.self G hGwf).IsDivergent := by
    convert hGCD.self_isConnectedDivergent.isDivergent
  unfold admissibleForestCanonicalContractGraph
    admissibleForestContractGraphWithStars
  exact A.contractWithStars_isDivergent hGwf hGDiv
    (G.properDisjointAdmissibleDivergentSubgraphs_isPairwiseDisjoint hA)
    (G.properDisjointAdmissibleDivergentSubgraphs_hasNonemptyComponents hA)
    (admissibleForestCanonicalStarOf G A hA)
    (admissibleForestCanonicalStarOf_isFreshStarAssignment G A hA)
    (admissibleForestCanonicalContractGraph_wellFormed G hGwf A hA)

theorem admissibleForestCanonicalContractGraph_hCD_of_ambient_preservation
    [IsDivergencePreservedByAdmissibleForestContract]
    (G : FeynmanGraph) (hGwf : G.WellFormed)
    (hG1PI : G.IsOnePI) (hGCD : G.IsConnectedDivergent) :
    ∀ A : AdmissibleSubgraph G,
      ∀ hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
        (admissibleForestContractGraphWithStars G A
          (admissibleForestCanonicalStarOf G A hA)).IsConnectedDivergent := by
  exact admissibleForestCanonicalContractGraph_hCD_of_ambient_onePI_divergence
    G hGwf hG1PI
    (admissibleForestCanonicalContractGraph_isDivergent_of_ambient_connectedDivergent
      G hGwf hGCD)

theorem admissibleForestCanonicalContractGraph_hCD_of_retarget_erase_connected_divergence
    (G : FeynmanGraph) (hGwf : G.WellFormed)
    (hGconn : G.IsSupportConnected)
    (hRetargetEraseConn : ∀ A : AdmissibleSubgraph G,
      ∀ hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
        ∀ e : FeynmanEdge,
          e ∈ A.complementEdges →
            ((admissibleForestCanonicalContractGraph G A hA).eraseInternalEdge
              (A.retargetEdge (admissibleForestCanonicalStarOf G A hA) e)
              ).IsSupportConnected)
    (hDiv : ∀ A : AdmissibleSubgraph G,
      ∀ hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
        (FeynmanSubgraph.self (admissibleForestCanonicalContractGraph G A hA)
          (admissibleForestCanonicalContractGraph_wellFormed G hGwf A hA)).IsDivergent) :
    ∀ A : AdmissibleSubgraph G,
      ∀ hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
        (admissibleForestContractGraphWithStars G A
          (admissibleForestCanonicalStarOf G A hA)).IsConnectedDivergent := by
  exact admissibleForestCanonicalContractGraph_hCD_of_erase_connected_divergence
    G hGwf hGconn
    (admissibleForestCanonicalContractGraph_erase_connected_of_retarget_complement
      G hRetargetEraseConn)
    hDiv

/-- Right tensor generator using the canonical component-star assignment.
This removes the explicit fresh-star hypothesis from the public API; only the
graph-theoretic connected-divergent preservation hypothesis remains. -/
noncomputable def admissibleForestRightWithCanonicalStars
    (G : FeynmanGraph)
    (hCD : ∀ A : AdmissibleSubgraph G,
      ∀ hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
        (admissibleForestContractGraphWithStars G A
          (admissibleForestCanonicalStarOf G A hA)).IsConnectedDivergent)
    (A : AdmissibleSubgraph G)
    (hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs) :
    HopfGen :=
  admissibleForestRightWithFreshStars G
    (admissibleForestCanonicalStarOf G)
    (admissibleForestCanonicalStarOf_isFreshStarAssignment G)
    hCD A hA

@[simp] theorem admissibleForestRightWithCanonicalStars_val
    (G : FeynmanGraph)
    (hCD : ∀ A : AdmissibleSubgraph G,
      ∀ hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
        (admissibleForestContractGraphWithStars G A
          (admissibleForestCanonicalStarOf G A hA)).IsConnectedDivergent)
    (A : AdmissibleSubgraph G)
    (hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs) :
    (admissibleForestRightWithCanonicalStars G hCD A hA).val =
      (admissibleForestContractGraphWithStars G A
        (admissibleForestCanonicalStarOf G A hA)).toClass := rfl

/-- Future proper-disjoint forest summand with canonical component stars.
The freshness condition is now internal; the remaining open hypothesis is
only connected-divergent preservation for the contracted forest graph. -/
noncomputable def admissibleForestStrictSummandWithCanonicalStars
    (G : FeynmanGraph)
    (hCD : ∀ A : AdmissibleSubgraph G,
      ∀ hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
        (admissibleForestContractGraphWithStars G A
          (admissibleForestCanonicalStarOf G A hA)).IsConnectedDivergent)
    (A : AdmissibleSubgraph G) : HopfH ⊗[ℚ] HopfH :=
  admissibleForestStrictSummand G
    (admissibleForestRightWithCanonicalStars G hCD) A

theorem admissibleForestStrictSummandWithCanonicalStars_eq_freshStars
    (G : FeynmanGraph)
    (hCD : ∀ A : AdmissibleSubgraph G,
      ∀ hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
        (admissibleForestContractGraphWithStars G A
          (admissibleForestCanonicalStarOf G A hA)).IsConnectedDivergent)
    (A : AdmissibleSubgraph G) :
    admissibleForestStrictSummandWithCanonicalStars G hCD A =
      admissibleForestStrictSummandWithFreshStars G
        (admissibleForestCanonicalStarOf G)
        (admissibleForestCanonicalStarOf_isFreshStarAssignment G)
        hCD A := rfl

theorem admissibleForestStrictSummandWithCanonicalStars_of_mem
    (G : FeynmanGraph)
    (hCD : ∀ A : AdmissibleSubgraph G,
      ∀ hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
        (admissibleForestContractGraphWithStars G A
          (admissibleForestCanonicalStarOf G A hA)).IsConnectedDivergent)
    (A : AdmissibleSubgraph G)
    (hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs) :
    admissibleForestStrictSummandWithCanonicalStars G hCD A =
      A.toHopfH ⊗ₜ[ℚ]
        (gen (admissibleForestRightWithCanonicalStars G hCD A hA)) := by
  unfold admissibleForestStrictSummandWithCanonicalStars admissibleForestStrictSummand
    admissibleStrictSummandWithRight
  rw [dif_pos hA]

theorem admissibleForestStrictSummandWithCanonicalStars_of_not_mem
    (G : FeynmanGraph)
    (hCD : ∀ A : AdmissibleSubgraph G,
      ∀ hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
        (admissibleForestContractGraphWithStars G A
          (admissibleForestCanonicalStarOf G A hA)).IsConnectedDivergent)
    (A : AdmissibleSubgraph G)
    (hA : A ∉ G.properDisjointAdmissibleDivergentSubgraphs) :
    admissibleForestStrictSummandWithCanonicalStars G hCD A = 0 := by
  unfold admissibleForestStrictSummandWithCanonicalStars admissibleForestStrictSummand
    admissibleStrictSummandWithRight
  rw [dif_neg hA]

/-- The same conservative admissible strict summand, but with the right tensor
factor routed through the forest-contraction skeleton. This is the replacement
point for upgrading from singleton-only admissible indices to genuine forests. -/
noncomputable def admissibleStrictSummandWithStars
    (G : FeynmanGraph) (hGwf : G.WellFormed) (hG1PI : G.IsOnePI)
    (A : AdmissibleSubgraph G) : HopfH ⊗[ℚ] HopfH :=
  if hA : A ∈ G.properAdmissibleDivergentSubgraphs then
    A.toHopfH ⊗ₜ[ℚ]
      (gen (admissibleContractGraphWithStarsToHopfGen G hGwf hG1PI A hA))
  else 0

theorem admissibleStrictSummandWithStars_eq_admissibleStrictSummand
    (G : FeynmanGraph) (hGwf : G.WellFormed) (hG1PI : G.IsOnePI)
    (A : AdmissibleSubgraph G) :
    admissibleStrictSummandWithStars G hGwf hG1PI A =
      admissibleStrictSummand G hGwf hG1PI A := by
  unfold admissibleStrictSummandWithStars admissibleStrictSummand
  by_cases hA : A ∈ G.properAdmissibleDivergentSubgraphs
  · simp [hA, admissibleContractGraphWithStarsToHopfGen_eq]
  · simp [hA]

/-- The current `WithStars` summand is just the parametric summand specialized
to the conservative singleton carrier and the existing conservative right
generator. -/
theorem admissibleStrictSummandWithRight_properAdmissible_eq_withStars
    (G : FeynmanGraph) (hGwf : G.WellFormed) (hG1PI : G.IsOnePI)
    (A : AdmissibleSubgraph G) :
    admissibleStrictSummandWithRight G
        G.properAdmissibleDivergentSubgraphs
        (fun A hA =>
          admissibleContractGraphWithStarsToHopfGen G hGwf hG1PI A hA)
        A =
      admissibleStrictSummandWithStars G hGwf hG1PI A := by
  unfold admissibleStrictSummandWithRight admissibleStrictSummandWithStars
  by_cases hA : A ∈ G.properAdmissibleDivergentSubgraphs
  · simp [hA]
  · simp [hA]

/-- On a singleton admissible element, the admissible strict summand is
definitionally the original connected strict summand after reindexing. -/
theorem admissibleStrictSummand_connectedIndexToAdmissible
    (G : FeynmanGraph) (hGwf : G.WellFormed) (hG1PI : G.IsOnePI)
    (γ : {γ : FeynmanSubgraph G // γ ∈ G.properConnectedDivergentSubgraphs}) :
    admissibleStrictSummand G hGwf hG1PI (connectedIndexToAdmissible G γ) =
      connectedStrictSummand G hGwf hG1PI γ.1 := by
  unfold admissibleStrictSummand connectedStrictSummand
  have hA :
      connectedIndexToAdmissible G γ ∈ G.properAdmissibleDivergentSubgraphs := by
    unfold properAdmissibleDivergentSubgraphs
    exact Finset.mem_image.mpr ⟨γ, by simp, rfl⟩
  rw [dif_pos hA]
  have hγ : γ.1.IsConnectedDivergent ∧ 0 < γ.1.internalEdges.card :=
    ⟨G.properConnectedDivergentSubgraphs_isConnectedDivergent γ.2,
      G.properConnectedDivergentSubgraphs_internalEdges_pos γ.2⟩
  rw [dif_pos hγ]
  rw [admissibleContractToHopfGen_connectedIndexToAdmissible G hGwf hG1PI γ hA]
  simp [connectedIndexToAdmissible]

/-- The whole strict connected coproduct summand reindexed through the
conservative singleton admissible index. This is the summand-level bridge
needed before re-stating `coproductGen_strict` with admissible indexing. -/
theorem sum_properConnectedDivergentSubgraphs_admissibleStrictSummand
    (G : FeynmanGraph) (hGwf : G.WellFormed) (hG1PI : G.IsOnePI) :
    (∑ γ ∈ G.properConnectedDivergentSubgraphs,
      connectedStrictSummand G hGwf hG1PI γ)
      =
    ∑ A ∈ G.properAdmissibleDivergentSubgraphs,
      admissibleStrictSummand G hGwf hG1PI A := by
  rw [← sum_connectedIndexToAdmissible_eq_sum_properAdmissibleDivergentSubgraphs
    G (fun A : AdmissibleSubgraph G =>
      admissibleStrictSummand G hGwf hG1PI A)]
  rw [← Finset.sum_attach G.properConnectedDivergentSubgraphs
    (fun γ : FeynmanSubgraph G =>
      connectedStrictSummand G hGwf hG1PI γ)]
  apply Finset.sum_congr rfl
  intro γ _hγ
  exact (admissibleStrictSummand_connectedIndexToAdmissible
    G hGwf hG1PI γ).symm

/-- Inline form of
`sum_properConnectedDivergentSubgraphs_admissibleStrictSummand`, matching
the summand that currently appears in `coproductGen_strict`. -/
theorem sum_properConnectedDivergentSubgraphs_inline_admissibleStrictSummand
    (G : FeynmanGraph) (hGwf : G.WellFormed) (hG1PI : G.IsOnePI) :
    (∑ γ ∈ G.properConnectedDivergentSubgraphs,
      if hγ : γ.IsConnectedDivergent ∧ 0 < γ.internalEdges.card then
        let hγNe : γ.IsNonempty :=
          FeynmanSubgraph.isNonempty_of_internalEdges_pos hγ.2
        (gen (γ.toHopfGen hγ.1)) ⊗ₜ[ℚ]
          (gen (γ.contractToHopfGen hGwf hG1PI hγ.1 hγNe))
      else 0)
      =
    ∑ A ∈ G.properAdmissibleDivergentSubgraphs,
      admissibleStrictSummand G hGwf hG1PI A := by
  change (∑ γ ∈ G.properConnectedDivergentSubgraphs,
      connectedStrictSummand G hGwf hG1PI γ)
      =
    ∑ A ∈ G.properAdmissibleDivergentSubgraphs,
      admissibleStrictSummand G hGwf hG1PI A
  exact sum_properConnectedDivergentSubgraphs_admissibleStrictSummand
    G hGwf hG1PI

/-- The conservative admissible summand can already be displayed over the
larger nonempty disjoint admissible carrier: every extra term vanishes until
the genuine forest contraction summand replaces the conservative body. -/
theorem sum_properAdmissibleDivergentSubgraphs_admissibleStrictSummand_nonemptyDisjoint
    (G : FeynmanGraph) (hGwf : G.WellFormed) (hG1PI : G.IsOnePI) :
    (∑ A ∈ G.properAdmissibleDivergentSubgraphs,
      admissibleStrictSummand G hGwf hG1PI A)
      =
    ∑ A ∈ G.nonemptyDisjointAdmissibleDivergentSubgraphs,
      admissibleStrictSummand G hGwf hG1PI A := by
  exact G.sum_properAdmissibleDivergentSubgraphs_eq_sum_nonemptyDisjointAdmissibleDivergentSubgraphs
    (fun A : AdmissibleSubgraph G => admissibleStrictSummand G hGwf hG1PI A)
    (by
      intro A _hA hA_not
      simp [admissibleStrictSummand, hA_not])

/-- Replacing the right tensor factor by the forest-contraction skeleton does
not change the conservative proper-admissible strict sum. -/
theorem sum_properAdmissibleDivergentSubgraphs_admissibleStrictSummandWithStars
    (G : FeynmanGraph) (hGwf : G.WellFormed) (hG1PI : G.IsOnePI) :
    (∑ A ∈ G.properAdmissibleDivergentSubgraphs,
      admissibleStrictSummand G hGwf hG1PI A)
      =
    ∑ A ∈ G.properAdmissibleDivergentSubgraphs,
      admissibleStrictSummandWithStars G hGwf hG1PI A := by
  apply Finset.sum_congr rfl
  intro A _hA
  exact (admissibleStrictSummandWithStars_eq_admissibleStrictSummand
    G hGwf hG1PI A).symm

/-- Direct bridge from the old connected strict sum to the forest-skeleton
proper-admissible display. -/
theorem sum_properConnectedDivergentSubgraphs_admissibleStrictSummandWithStars
    (G : FeynmanGraph) (hGwf : G.WellFormed) (hG1PI : G.IsOnePI) :
    (∑ γ ∈ G.properConnectedDivergentSubgraphs,
      connectedStrictSummand G hGwf hG1PI γ)
      =
    ∑ A ∈ G.properAdmissibleDivergentSubgraphs,
      admissibleStrictSummandWithStars G hGwf hG1PI A := by
  rw [sum_properConnectedDivergentSubgraphs_admissibleStrictSummand]
  rw [sum_properAdmissibleDivergentSubgraphs_admissibleStrictSummandWithStars]

/-- Inline direct bridge from the strict coproduct body to the forest-skeleton
proper-admissible display. -/
theorem sum_properConnectedDivergentSubgraphs_inline_admissibleStrictSummandWithStars
    (G : FeynmanGraph) (hGwf : G.WellFormed) (hG1PI : G.IsOnePI) :
    (∑ γ ∈ G.properConnectedDivergentSubgraphs,
      if hγ : γ.IsConnectedDivergent ∧ 0 < γ.internalEdges.card then
        let hγNe : γ.IsNonempty :=
          FeynmanSubgraph.isNonempty_of_internalEdges_pos hγ.2
        (gen (γ.toHopfGen hγ.1)) ⊗ₜ[ℚ]
          (gen (γ.contractToHopfGen hGwf hG1PI hγ.1 hγNe))
      else 0)
      =
    ∑ A ∈ G.properAdmissibleDivergentSubgraphs,
      admissibleStrictSummandWithStars G hGwf hG1PI A := by
  change (∑ γ ∈ G.properConnectedDivergentSubgraphs,
      connectedStrictSummand G hGwf hG1PI γ)
      =
    ∑ A ∈ G.properAdmissibleDivergentSubgraphs,
      admissibleStrictSummandWithStars G hGwf hG1PI A
  exact sum_properConnectedDivergentSubgraphs_admissibleStrictSummandWithStars
    G hGwf hG1PI

/-- The forest-skeleton strict summand can also be displayed over the
nonempty disjoint admissible carrier; extra terms remain zero while the
proper-admissible index is conservative. -/
theorem sum_properAdmissibleDivergentSubgraphs_admissibleStrictSummandWithStars_nonemptyDisjoint
    (G : FeynmanGraph) (hGwf : G.WellFormed) (hG1PI : G.IsOnePI) :
    (∑ A ∈ G.properAdmissibleDivergentSubgraphs,
      admissibleStrictSummandWithStars G hGwf hG1PI A)
      =
    ∑ A ∈ G.nonemptyDisjointAdmissibleDivergentSubgraphs,
      admissibleStrictSummandWithStars G hGwf hG1PI A := by
  exact G.sum_properAdmissibleDivergentSubgraphs_eq_sum_nonemptyDisjointAdmissibleDivergentSubgraphs
    (fun A : AdmissibleSubgraph G =>
      admissibleStrictSummandWithStars G hGwf hG1PI A)
    (by
      intro A _hA hA_not
      simp [admissibleStrictSummandWithStars, hA_not])

/-- The forest-skeleton strict summand can be displayed over the proper
disjoint admissible carrier; extra terms remain zero while the summand body
is still conservative. -/
theorem sum_properAdmissibleDivergentSubgraphs_admissibleStrictSummandWithStars_properDisjoint
    (G : FeynmanGraph) (hGwf : G.WellFormed) (hG1PI : G.IsOnePI) :
    (∑ A ∈ G.properAdmissibleDivergentSubgraphs,
      admissibleStrictSummandWithStars G hGwf hG1PI A)
      =
    ∑ A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
      admissibleStrictSummandWithStars G hGwf hG1PI A := by
  exact G.sum_properAdmissibleDivergentSubgraphs_eq_sum_properDisjointAdmissibleDivergentSubgraphs
    (fun A : AdmissibleSubgraph G =>
      admissibleStrictSummandWithStars G hGwf hG1PI A)
    (by
      intro A _hA hA_not
      simp [admissibleStrictSummandWithStars, hA_not])

/-- Direct bridge from the old connected strict sum to the forest-skeleton
nonempty-disjoint admissible carrier. -/
theorem sum_properConnectedDivergentSubgraphs_admissibleStrictSummandWithStars_nonemptyDisjoint
    (G : FeynmanGraph) (hGwf : G.WellFormed) (hG1PI : G.IsOnePI) :
    (∑ γ ∈ G.properConnectedDivergentSubgraphs,
      connectedStrictSummand G hGwf hG1PI γ)
      =
    ∑ A ∈ G.nonemptyDisjointAdmissibleDivergentSubgraphs,
      admissibleStrictSummandWithStars G hGwf hG1PI A := by
  rw [sum_properConnectedDivergentSubgraphs_admissibleStrictSummandWithStars]
  rw [sum_properAdmissibleDivergentSubgraphs_admissibleStrictSummandWithStars_nonemptyDisjoint]

/-- Direct bridge from the old connected strict sum to the forest-skeleton
proper-disjoint admissible carrier. -/
theorem sum_properConnectedDivergentSubgraphs_admissibleStrictSummandWithStars_properDisjoint
    (G : FeynmanGraph) (hGwf : G.WellFormed) (hG1PI : G.IsOnePI) :
    (∑ γ ∈ G.properConnectedDivergentSubgraphs,
      connectedStrictSummand G hGwf hG1PI γ)
      =
    ∑ A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
      admissibleStrictSummandWithStars G hGwf hG1PI A := by
  rw [sum_properConnectedDivergentSubgraphs_admissibleStrictSummandWithStars]
  rw [sum_properAdmissibleDivergentSubgraphs_admissibleStrictSummandWithStars_properDisjoint]

end FeynmanGraph

/-- **H4.3-strict** — The Connes–Kreimer coproduct with strict generators
on both tensor factors. Same body shape as `coproductGen`, but each
generator is a `HopfGen` (connected + 1PI + divergent) rather than a
`HopfGenTemp` (only support-connected). -/
noncomputable def coproductGen_strict (G : ConnectedFeynmanGraph)
    (hGwf : G.toFeynmanGraph.WellFormed) (hG1PI : G.toFeynmanGraph.IsOnePI)
    (hGCD : G.toFeynmanGraph.IsConnectedDivergent) :
    HopfH ⊗[ℚ] HopfH :=
  let genG : HopfH := gen ⟨G.toFeynmanGraph.toClass,
    (FeynmanGraphClass.isConnectedDivergent_toClass G.toFeynmanGraph).mpr hGCD⟩
  (genG ⊗ₜ[ℚ] (1 : HopfH))
  + ((1 : HopfH) ⊗ₜ[ℚ] genG)
  + ∑ γ ∈ G.toFeynmanGraph.properConnectedDivergentSubgraphs,
      if hγ : γ.IsConnectedDivergent ∧ 0 < γ.internalEdges.card then
        let hγNe : γ.IsNonempty :=
          FeynmanSubgraph.isNonempty_of_internalEdges_pos hγ.2
        (gen (γ.toHopfGen hγ.1)) ⊗ₜ[ℚ]
          (gen (γ.contractToHopfGen hGwf hG1PI hγ.1 hγNe))
      else 0

theorem coproductGen_strict_eq (G : ConnectedFeynmanGraph)
    (hGwf : G.toFeynmanGraph.WellFormed) (hG1PI : G.toFeynmanGraph.IsOnePI)
    (hGCD : G.toFeynmanGraph.IsConnectedDivergent) :
    coproductGen_strict G hGwf hG1PI hGCD =
      (let genG : HopfH := gen ⟨G.toFeynmanGraph.toClass,
        (FeynmanGraphClass.isConnectedDivergent_toClass G.toFeynmanGraph).mpr hGCD⟩
      (genG ⊗ₜ[ℚ] (1 : HopfH))
      + ((1 : HopfH) ⊗ₜ[ℚ] genG)
      + ∑ γ ∈ G.toFeynmanGraph.properConnectedDivergentSubgraphs,
          if hγ : γ.IsConnectedDivergent ∧ 0 < γ.internalEdges.card then
            let hγNe : γ.IsNonempty :=
              FeynmanSubgraph.isNonempty_of_internalEdges_pos hγ.2
            (gen (γ.toHopfGen hγ.1)) ⊗ₜ[ℚ]
              (gen (γ.contractToHopfGen hGwf hG1PI hγ.1 hγNe))
          else 0) := rfl

/-- `coproductGen_strict` with the strict summand reindexed through the
conservative singleton admissible index. This is still definitionally the
old coproduct; it only changes the displayed summation index. -/
theorem coproductGen_strict_eq_admissibleSummand (G : ConnectedFeynmanGraph)
    (hGwf : G.toFeynmanGraph.WellFormed) (hG1PI : G.toFeynmanGraph.IsOnePI)
    (hGCD : G.toFeynmanGraph.IsConnectedDivergent) :
    coproductGen_strict G hGwf hG1PI hGCD =
      (let genG : HopfH := gen ⟨G.toFeynmanGraph.toClass,
        (FeynmanGraphClass.isConnectedDivergent_toClass G.toFeynmanGraph).mpr hGCD⟩
      (genG ⊗ₜ[ℚ] (1 : HopfH))
      + ((1 : HopfH) ⊗ₜ[ℚ] genG)
      + ∑ A ∈ G.toFeynmanGraph.properAdmissibleDivergentSubgraphs,
          FeynmanGraph.admissibleStrictSummand
            G.toFeynmanGraph hGwf hG1PI A) := by
  rw [coproductGen_strict_eq]
  rw [FeynmanGraph.sum_properConnectedDivergentSubgraphs_inline_admissibleStrictSummand]

/-- `coproductGen_strict` displayed over the nonempty disjoint admissible
carrier. This is still the conservative coproduct: extra disjoint terms are
zero until the summand is upgraded to genuine forest contraction. -/
theorem coproductGen_strict_eq_nonemptyDisjointAdmissibleSummand
    (G : ConnectedFeynmanGraph)
    (hGwf : G.toFeynmanGraph.WellFormed) (hG1PI : G.toFeynmanGraph.IsOnePI)
    (hGCD : G.toFeynmanGraph.IsConnectedDivergent) :
    coproductGen_strict G hGwf hG1PI hGCD =
      (let genG : HopfH := gen ⟨G.toFeynmanGraph.toClass,
        (FeynmanGraphClass.isConnectedDivergent_toClass G.toFeynmanGraph).mpr hGCD⟩
      (genG ⊗ₜ[ℚ] (1 : HopfH))
      + ((1 : HopfH) ⊗ₜ[ℚ] genG)
      + ∑ A ∈ G.toFeynmanGraph.nonemptyDisjointAdmissibleDivergentSubgraphs,
          FeynmanGraph.admissibleStrictSummand
            G.toFeynmanGraph hGwf hG1PI A) := by
  rw [coproductGen_strict_eq_admissibleSummand]
  rw [FeynmanGraph.sum_properAdmissibleDivergentSubgraphs_admissibleStrictSummand_nonemptyDisjoint]

/-- `coproductGen_strict` with the conservative admissible summand routed
through the forest-contraction skeleton on the right tensor factor. -/
theorem coproductGen_strict_eq_admissibleSummandWithStars
    (G : ConnectedFeynmanGraph)
    (hGwf : G.toFeynmanGraph.WellFormed) (hG1PI : G.toFeynmanGraph.IsOnePI)
    (hGCD : G.toFeynmanGraph.IsConnectedDivergent) :
    coproductGen_strict G hGwf hG1PI hGCD =
      (let genG : HopfH := gen ⟨G.toFeynmanGraph.toClass,
        (FeynmanGraphClass.isConnectedDivergent_toClass G.toFeynmanGraph).mpr hGCD⟩
      (genG ⊗ₜ[ℚ] (1 : HopfH))
      + ((1 : HopfH) ⊗ₜ[ℚ] genG)
      + ∑ A ∈ G.toFeynmanGraph.properAdmissibleDivergentSubgraphs,
          FeynmanGraph.admissibleStrictSummandWithStars
            G.toFeynmanGraph hGwf hG1PI A) := by
  rw [coproductGen_strict_eq_admissibleSummand]
  rw [FeynmanGraph.sum_properAdmissibleDivergentSubgraphs_admissibleStrictSummandWithStars]

/-- `coproductGen_strict` displayed over the nonempty disjoint admissible
carrier, with the right tensor factor routed through the forest-contraction
skeleton. This is the current small-step target for the admissible-index
redesign. -/
theorem coproductGen_strict_eq_nonemptyDisjointAdmissibleSummandWithStars
    (G : ConnectedFeynmanGraph)
    (hGwf : G.toFeynmanGraph.WellFormed) (hG1PI : G.toFeynmanGraph.IsOnePI)
    (hGCD : G.toFeynmanGraph.IsConnectedDivergent) :
    coproductGen_strict G hGwf hG1PI hGCD =
      (let genG : HopfH := gen ⟨G.toFeynmanGraph.toClass,
        (FeynmanGraphClass.isConnectedDivergent_toClass G.toFeynmanGraph).mpr hGCD⟩
      (genG ⊗ₜ[ℚ] (1 : HopfH))
      + ((1 : HopfH) ⊗ₜ[ℚ] genG)
      + ∑ A ∈ G.toFeynmanGraph.nonemptyDisjointAdmissibleDivergentSubgraphs,
          FeynmanGraph.admissibleStrictSummandWithStars
            G.toFeynmanGraph hGwf hG1PI A) := by
  rw [coproductGen_strict_eq_admissibleSummandWithStars]
  rw [FeynmanGraph.sum_properAdmissibleDivergentSubgraphs_admissibleStrictSummandWithStars_nonemptyDisjoint]

/-- `coproductGen_strict` displayed over the proper disjoint admissible
carrier, with the right tensor factor routed through the forest-contraction
skeleton. This is the narrow final carrier shape before the summand body is
upgraded from conservative singleton contraction to genuine forest
contraction. -/
theorem coproductGen_strict_eq_properDisjointAdmissibleSummandWithStars
    (G : ConnectedFeynmanGraph)
    (hGwf : G.toFeynmanGraph.WellFormed) (hG1PI : G.toFeynmanGraph.IsOnePI)
    (hGCD : G.toFeynmanGraph.IsConnectedDivergent) :
    coproductGen_strict G hGwf hG1PI hGCD =
      (let genG : HopfH := gen ⟨G.toFeynmanGraph.toClass,
        (FeynmanGraphClass.isConnectedDivergent_toClass G.toFeynmanGraph).mpr hGCD⟩
      (genG ⊗ₜ[ℚ] (1 : HopfH))
      + ((1 : HopfH) ⊗ₜ[ℚ] genG)
      + ∑ A ∈ G.toFeynmanGraph.properDisjointAdmissibleDivergentSubgraphs,
          FeynmanGraph.admissibleStrictSummandWithStars
            G.toFeynmanGraph hGwf hG1PI A) := by
  rw [coproductGen_strict_eq_admissibleSummandWithStars]
  rw [FeynmanGraph.sum_properAdmissibleDivergentSubgraphs_admissibleStrictSummandWithStars_properDisjoint]

/-- Future strict coproduct formula over the proper-disjoint admissible
carrier, with the right tensor factor supplied by genuine forest contraction
through `contractWithStars`. This does not replace `coproductGen_strict` yet:
the remaining work is to provide the preservation proof `hCD` from graph
combinatorics and then use this formula in H5. -/
noncomputable def coproductGen_strict_forestWithStars
    (G : ConnectedFeynmanGraph)
    (hGCD : G.toFeynmanGraph.IsConnectedDivergent)
    (starOf : ∀ A : AdmissibleSubgraph G.toFeynmanGraph,
      A ∈ G.toFeynmanGraph.properDisjointAdmissibleDivergentSubgraphs →
        FeynmanSubgraph G.toFeynmanGraph → VertexId)
    (hCD : ∀ A : AdmissibleSubgraph G.toFeynmanGraph,
      ∀ hA : A ∈ G.toFeynmanGraph.properDisjointAdmissibleDivergentSubgraphs,
        (FeynmanGraph.admissibleForestContractGraphWithStars
          G.toFeynmanGraph A (starOf A hA)).IsConnectedDivergent) :
    HopfH ⊗[ℚ] HopfH :=
  let genG : HopfH := gen ⟨G.toFeynmanGraph.toClass,
    (FeynmanGraphClass.isConnectedDivergent_toClass G.toFeynmanGraph).mpr hGCD⟩
  (genG ⊗ₜ[ℚ] (1 : HopfH))
  + ((1 : HopfH) ⊗ₜ[ℚ] genG)
  + ∑ A ∈ G.toFeynmanGraph.properDisjointAdmissibleDivergentSubgraphs.filter
      (fun A => 0 < A.complementEdges.card),
      FeynmanGraph.admissibleForestStrictSummandWithStars
        G.toFeynmanGraph starOf hCD A

/-- Future strict coproduct formula with fresh-star hypotheses exposed.
Once the preservation theorem constructs `hCD` from `hFresh`, this is the
formula that will be compared with the conservative display. -/
noncomputable def coproductGen_strict_forestWithFreshStars
    (G : ConnectedFeynmanGraph)
    (hGCD : G.toFeynmanGraph.IsConnectedDivergent)
    (starOf : ∀ A : AdmissibleSubgraph G.toFeynmanGraph,
      A ∈ G.toFeynmanGraph.properDisjointAdmissibleDivergentSubgraphs →
        FeynmanSubgraph G.toFeynmanGraph → VertexId)
    (hFresh : ∀ A : AdmissibleSubgraph G.toFeynmanGraph,
      ∀ hA : A ∈ G.toFeynmanGraph.properDisjointAdmissibleDivergentSubgraphs,
        A.IsFreshStarAssignment (starOf A hA))
    (hCD : ∀ A : AdmissibleSubgraph G.toFeynmanGraph,
      ∀ hA : A ∈ G.toFeynmanGraph.properDisjointAdmissibleDivergentSubgraphs,
        (FeynmanGraph.admissibleForestContractGraphWithStars
          G.toFeynmanGraph A (starOf A hA)).IsConnectedDivergent) :
    HopfH ⊗[ℚ] HopfH :=
  let genG : HopfH := gen ⟨G.toFeynmanGraph.toClass,
    (FeynmanGraphClass.isConnectedDivergent_toClass G.toFeynmanGraph).mpr hGCD⟩
  (genG ⊗ₜ[ℚ] (1 : HopfH))
  + ((1 : HopfH) ⊗ₜ[ℚ] genG)
  + ∑ A ∈ G.toFeynmanGraph.properDisjointAdmissibleDivergentSubgraphs.filter
      (fun A => 0 < A.complementEdges.card),
      FeynmanGraph.admissibleForestStrictSummandWithFreshStars
        G.toFeynmanGraph starOf hFresh hCD A

theorem coproductGen_strict_forestWithFreshStars_eq_forestWithStars
    (G : ConnectedFeynmanGraph)
    (hGCD : G.toFeynmanGraph.IsConnectedDivergent)
    (starOf : ∀ A : AdmissibleSubgraph G.toFeynmanGraph,
      A ∈ G.toFeynmanGraph.properDisjointAdmissibleDivergentSubgraphs →
        FeynmanSubgraph G.toFeynmanGraph → VertexId)
    (hFresh : ∀ A : AdmissibleSubgraph G.toFeynmanGraph,
      ∀ hA : A ∈ G.toFeynmanGraph.properDisjointAdmissibleDivergentSubgraphs,
        A.IsFreshStarAssignment (starOf A hA))
    (hCD : ∀ A : AdmissibleSubgraph G.toFeynmanGraph,
      ∀ hA : A ∈ G.toFeynmanGraph.properDisjointAdmissibleDivergentSubgraphs,
        (FeynmanGraph.admissibleForestContractGraphWithStars
          G.toFeynmanGraph A (starOf A hA)).IsConnectedDivergent) :
    coproductGen_strict_forestWithFreshStars G hGCD starOf hFresh hCD =
      coproductGen_strict_forestWithStars G hGCD starOf hCD := by
  unfold coproductGen_strict_forestWithFreshStars
    coproductGen_strict_forestWithStars
  congr 1

/-- Future strict coproduct formula with canonical component stars. This is
the first staged forest formula whose public API no longer asks for a
fresh-star proof; the remaining hypothesis is exactly the graph-theoretic
connected-divergent preservation of the canonical forest contraction. -/
noncomputable def coproductGen_strict_forestWithCanonicalStars
    (G : ConnectedFeynmanGraph)
    (hGCD : G.toFeynmanGraph.IsConnectedDivergent)
    (hCD : ∀ A : AdmissibleSubgraph G.toFeynmanGraph,
      ∀ hA : A ∈ G.toFeynmanGraph.properDisjointAdmissibleDivergentSubgraphs,
        (FeynmanGraph.admissibleForestContractGraphWithStars
          G.toFeynmanGraph A
          (FeynmanGraph.admissibleForestCanonicalStarOf
            G.toFeynmanGraph A hA)).IsConnectedDivergent) :
    HopfH ⊗[ℚ] HopfH :=
  let genG : HopfH := gen ⟨G.toFeynmanGraph.toClass,
    (FeynmanGraphClass.isConnectedDivergent_toClass G.toFeynmanGraph).mpr hGCD⟩
  (genG ⊗ₜ[ℚ] (1 : HopfH))
  + ((1 : HopfH) ⊗ₜ[ℚ] genG)
  + ∑ A ∈ G.toFeynmanGraph.properDisjointAdmissibleDivergentSubgraphs.filter
      (fun A => 0 < A.complementEdges.card),
      FeynmanGraph.admissibleForestStrictSummandWithCanonicalStars
        G.toFeynmanGraph hCD A

theorem coproductGen_strict_forestWithCanonicalStars_eq_freshStars
    (G : ConnectedFeynmanGraph)
    (hGCD : G.toFeynmanGraph.IsConnectedDivergent)
    (hCD : ∀ A : AdmissibleSubgraph G.toFeynmanGraph,
      ∀ hA : A ∈ G.toFeynmanGraph.properDisjointAdmissibleDivergentSubgraphs,
        (FeynmanGraph.admissibleForestContractGraphWithStars
          G.toFeynmanGraph A
          (FeynmanGraph.admissibleForestCanonicalStarOf
            G.toFeynmanGraph A hA)).IsConnectedDivergent) :
    coproductGen_strict_forestWithCanonicalStars G hGCD hCD =
      coproductGen_strict_forestWithFreshStars G hGCD
        (FeynmanGraph.admissibleForestCanonicalStarOf G.toFeynmanGraph)
        (FeynmanGraph.admissibleForestCanonicalStarOf_isFreshStarAssignment
          G.toFeynmanGraph)
        hCD := by
  unfold coproductGen_strict_forestWithCanonicalStars
    coproductGen_strict_forestWithFreshStars
  congr 1

/-- Future strict coproduct formula with canonical stars, but with the
remaining preservation hypothesis split into the four graph-theoretic slices
needed to build `IsConnectedDivergent`: well-formedness, connectedness, 1PI,
and divergence of the self-subgraph. -/
noncomputable def coproductGen_strict_forestWithCanonicalStarsFromParts
    (G : ConnectedFeynmanGraph)
    (hGCD : G.toFeynmanGraph.IsConnectedDivergent)
    (hWF : ∀ A : AdmissibleSubgraph G.toFeynmanGraph,
      ∀ hA : A ∈ G.toFeynmanGraph.properDisjointAdmissibleDivergentSubgraphs,
        (FeynmanGraph.admissibleForestCanonicalContractGraph
          G.toFeynmanGraph A hA).WellFormed)
    (hConn : ∀ A : AdmissibleSubgraph G.toFeynmanGraph,
      ∀ hA : A ∈ G.toFeynmanGraph.properDisjointAdmissibleDivergentSubgraphs,
        (FeynmanGraph.admissibleForestCanonicalContractGraph
          G.toFeynmanGraph A hA).IsSupportConnected)
    (hOnePI : ∀ A : AdmissibleSubgraph G.toFeynmanGraph,
      ∀ hA : A ∈ G.toFeynmanGraph.properDisjointAdmissibleDivergentSubgraphs,
        (FeynmanGraph.admissibleForestCanonicalContractGraph
          G.toFeynmanGraph A hA).IsOnePI)
    (hDiv : ∀ A : AdmissibleSubgraph G.toFeynmanGraph,
      ∀ hA : A ∈ G.toFeynmanGraph.properDisjointAdmissibleDivergentSubgraphs,
        (FeynmanSubgraph.self
          (FeynmanGraph.admissibleForestCanonicalContractGraph
            G.toFeynmanGraph A hA)
          (hWF A hA)).IsDivergent) :
    HopfH ⊗[ℚ] HopfH :=
  coproductGen_strict_forestWithCanonicalStars G hGCD
    (FeynmanGraph.admissibleForestCanonicalContractGraph_hCD_of_parts
      G.toFeynmanGraph hWF hConn hOnePI hDiv)

theorem coproductGen_strict_forestWithCanonicalStarsFromParts_eq
    (G : ConnectedFeynmanGraph)
    (hGCD : G.toFeynmanGraph.IsConnectedDivergent)
    (hWF : ∀ A : AdmissibleSubgraph G.toFeynmanGraph,
      ∀ hA : A ∈ G.toFeynmanGraph.properDisjointAdmissibleDivergentSubgraphs,
        (FeynmanGraph.admissibleForestCanonicalContractGraph
          G.toFeynmanGraph A hA).WellFormed)
    (hConn : ∀ A : AdmissibleSubgraph G.toFeynmanGraph,
      ∀ hA : A ∈ G.toFeynmanGraph.properDisjointAdmissibleDivergentSubgraphs,
        (FeynmanGraph.admissibleForestCanonicalContractGraph
          G.toFeynmanGraph A hA).IsSupportConnected)
    (hOnePI : ∀ A : AdmissibleSubgraph G.toFeynmanGraph,
      ∀ hA : A ∈ G.toFeynmanGraph.properDisjointAdmissibleDivergentSubgraphs,
        (FeynmanGraph.admissibleForestCanonicalContractGraph
          G.toFeynmanGraph A hA).IsOnePI)
    (hDiv : ∀ A : AdmissibleSubgraph G.toFeynmanGraph,
      ∀ hA : A ∈ G.toFeynmanGraph.properDisjointAdmissibleDivergentSubgraphs,
        (FeynmanSubgraph.self
          (FeynmanGraph.admissibleForestCanonicalContractGraph
            G.toFeynmanGraph A hA)
          (hWF A hA)).IsDivergent) :
    coproductGen_strict_forestWithCanonicalStarsFromParts
      G hGCD hWF hConn hOnePI hDiv =
    coproductGen_strict_forestWithCanonicalStars G hGCD
      (FeynmanGraph.admissibleForestCanonicalContractGraph_hCD_of_parts
        G.toFeynmanGraph hWF hConn hOnePI hDiv) := rfl

/-- Same split formula, after discharging well-formedness from the ambient
graph. The remaining obligations are exactly the three mathematical slices:
connectedness, 1PI, and divergence preservation for canonical forest
contraction. -/
noncomputable def coproductGen_strict_forestWithCanonicalStarsFromGraphParts
    (G : ConnectedFeynmanGraph)
    (hGwf : G.toFeynmanGraph.WellFormed)
    (hGCD : G.toFeynmanGraph.IsConnectedDivergent)
    (hConn : ∀ A : AdmissibleSubgraph G.toFeynmanGraph,
      ∀ hA : A ∈ G.toFeynmanGraph.properDisjointAdmissibleDivergentSubgraphs,
        (FeynmanGraph.admissibleForestCanonicalContractGraph
          G.toFeynmanGraph A hA).IsSupportConnected)
    (hOnePI : ∀ A : AdmissibleSubgraph G.toFeynmanGraph,
      ∀ hA : A ∈ G.toFeynmanGraph.properDisjointAdmissibleDivergentSubgraphs,
        (FeynmanGraph.admissibleForestCanonicalContractGraph
          G.toFeynmanGraph A hA).IsOnePI)
    (hDiv : ∀ A : AdmissibleSubgraph G.toFeynmanGraph,
      ∀ hA : A ∈ G.toFeynmanGraph.properDisjointAdmissibleDivergentSubgraphs,
        (FeynmanSubgraph.self
          (FeynmanGraph.admissibleForestCanonicalContractGraph
            G.toFeynmanGraph A hA)
          (FeynmanGraph.admissibleForestCanonicalContractGraph_wellFormed
            G.toFeynmanGraph hGwf A hA)).IsDivergent) :
    HopfH ⊗[ℚ] HopfH :=
  coproductGen_strict_forestWithCanonicalStars G hGCD
    (FeynmanGraph.admissibleForestCanonicalContractGraph_hCD_of_graph_parts
      G.toFeynmanGraph hGwf hConn hOnePI hDiv)

theorem coproductGen_strict_forestWithCanonicalStarsFromGraphParts_eq
    (G : ConnectedFeynmanGraph)
    (hGwf : G.toFeynmanGraph.WellFormed)
    (hGCD : G.toFeynmanGraph.IsConnectedDivergent)
    (hConn : ∀ A : AdmissibleSubgraph G.toFeynmanGraph,
      ∀ hA : A ∈ G.toFeynmanGraph.properDisjointAdmissibleDivergentSubgraphs,
        (FeynmanGraph.admissibleForestCanonicalContractGraph
          G.toFeynmanGraph A hA).IsSupportConnected)
    (hOnePI : ∀ A : AdmissibleSubgraph G.toFeynmanGraph,
      ∀ hA : A ∈ G.toFeynmanGraph.properDisjointAdmissibleDivergentSubgraphs,
        (FeynmanGraph.admissibleForestCanonicalContractGraph
          G.toFeynmanGraph A hA).IsOnePI)
    (hDiv : ∀ A : AdmissibleSubgraph G.toFeynmanGraph,
      ∀ hA : A ∈ G.toFeynmanGraph.properDisjointAdmissibleDivergentSubgraphs,
        (FeynmanSubgraph.self
          (FeynmanGraph.admissibleForestCanonicalContractGraph
            G.toFeynmanGraph A hA)
          (FeynmanGraph.admissibleForestCanonicalContractGraph_wellFormed
            G.toFeynmanGraph hGwf A hA)).IsDivergent) :
    coproductGen_strict_forestWithCanonicalStarsFromGraphParts
      G hGwf hGCD hConn hOnePI hDiv =
    coproductGen_strict_forestWithCanonicalStars G hGCD
      (FeynmanGraph.admissibleForestCanonicalContractGraph_hCD_of_graph_parts
        G.toFeynmanGraph hGwf hConn hOnePI hDiv) := rfl

/-- Same split formula after discharging both well-formedness and
connectedness from the ambient graph plus the strengthened admissible carrier.
The only remaining preservation obligations are 1PI and divergence. -/
noncomputable def coproductGen_strict_forestWithCanonicalStarsFromOnePIDivergence
    (G : ConnectedFeynmanGraph)
    (hGwf : G.toFeynmanGraph.WellFormed)
    (hGCD : G.toFeynmanGraph.IsConnectedDivergent)
    (hOnePI : ∀ A : AdmissibleSubgraph G.toFeynmanGraph,
      ∀ hA : A ∈ G.toFeynmanGraph.properDisjointAdmissibleDivergentSubgraphs,
        (FeynmanGraph.admissibleForestCanonicalContractGraph
          G.toFeynmanGraph A hA).IsOnePI)
    (hDiv : ∀ A : AdmissibleSubgraph G.toFeynmanGraph,
      ∀ hA : A ∈ G.toFeynmanGraph.properDisjointAdmissibleDivergentSubgraphs,
        (FeynmanSubgraph.self
          (FeynmanGraph.admissibleForestCanonicalContractGraph
            G.toFeynmanGraph A hA)
          (FeynmanGraph.admissibleForestCanonicalContractGraph_wellFormed
            G.toFeynmanGraph hGwf A hA)).IsDivergent) :
    HopfH ⊗[ℚ] HopfH :=
  coproductGen_strict_forestWithCanonicalStars G hGCD
    (FeynmanGraph.admissibleForestCanonicalContractGraph_hCD_of_onePI_divergence
      G.toFeynmanGraph hGwf
      (ConnectedFeynmanGraph.isSupportConnected G) hOnePI hDiv)

theorem coproductGen_strict_forestWithCanonicalStarsFromOnePIDivergence_eq
    (G : ConnectedFeynmanGraph)
    (hGwf : G.toFeynmanGraph.WellFormed)
    (hGCD : G.toFeynmanGraph.IsConnectedDivergent)
    (hOnePI : ∀ A : AdmissibleSubgraph G.toFeynmanGraph,
      ∀ hA : A ∈ G.toFeynmanGraph.properDisjointAdmissibleDivergentSubgraphs,
        (FeynmanGraph.admissibleForestCanonicalContractGraph
          G.toFeynmanGraph A hA).IsOnePI)
    (hDiv : ∀ A : AdmissibleSubgraph G.toFeynmanGraph,
      ∀ hA : A ∈ G.toFeynmanGraph.properDisjointAdmissibleDivergentSubgraphs,
        (FeynmanSubgraph.self
          (FeynmanGraph.admissibleForestCanonicalContractGraph
            G.toFeynmanGraph A hA)
          (FeynmanGraph.admissibleForestCanonicalContractGraph_wellFormed
            G.toFeynmanGraph hGwf A hA)).IsDivergent) :
    coproductGen_strict_forestWithCanonicalStarsFromOnePIDivergence
      G hGwf hGCD hOnePI hDiv =
    coproductGen_strict_forestWithCanonicalStars G hGCD
      (FeynmanGraph.admissibleForestCanonicalContractGraph_hCD_of_onePI_divergence
        G.toFeynmanGraph hGwf
        (ConnectedFeynmanGraph.isSupportConnected G) hOnePI hDiv) := rfl

/-- Same formula after discharging the canonical quotient 1PI obligation from
the ambient graph's 1PI property. The only remaining preservation obligation
is divergence of the canonical forest quotient. -/
noncomputable def coproductGen_strict_forestWithCanonicalStarsFromAmbientOnePIDivergence
    (G : ConnectedFeynmanGraph)
    (hGwf : G.toFeynmanGraph.WellFormed)
    (hG1PI : G.toFeynmanGraph.IsOnePI)
    (hGCD : G.toFeynmanGraph.IsConnectedDivergent)
    (hDiv : ∀ A : AdmissibleSubgraph G.toFeynmanGraph,
      ∀ hA : A ∈ G.toFeynmanGraph.properDisjointAdmissibleDivergentSubgraphs,
        (FeynmanSubgraph.self
          (FeynmanGraph.admissibleForestCanonicalContractGraph
            G.toFeynmanGraph A hA)
          (FeynmanGraph.admissibleForestCanonicalContractGraph_wellFormed
            G.toFeynmanGraph hGwf A hA)).IsDivergent) :
    HopfH ⊗[ℚ] HopfH :=
  coproductGen_strict_forestWithCanonicalStars G hGCD
    (FeynmanGraph.admissibleForestCanonicalContractGraph_hCD_of_ambient_onePI_divergence
      G.toFeynmanGraph hGwf hG1PI hDiv)

theorem coproductGen_strict_forestWithCanonicalStarsFromAmbientOnePIDivergence_eq
    (G : ConnectedFeynmanGraph)
    (hGwf : G.toFeynmanGraph.WellFormed)
    (hG1PI : G.toFeynmanGraph.IsOnePI)
    (hGCD : G.toFeynmanGraph.IsConnectedDivergent)
    (hDiv : ∀ A : AdmissibleSubgraph G.toFeynmanGraph,
      ∀ hA : A ∈ G.toFeynmanGraph.properDisjointAdmissibleDivergentSubgraphs,
        (FeynmanSubgraph.self
          (FeynmanGraph.admissibleForestCanonicalContractGraph
            G.toFeynmanGraph A hA)
          (FeynmanGraph.admissibleForestCanonicalContractGraph_wellFormed
            G.toFeynmanGraph hGwf A hA)).IsDivergent) :
    coproductGen_strict_forestWithCanonicalStarsFromAmbientOnePIDivergence
      G hGwf hG1PI hGCD hDiv =
    coproductGen_strict_forestWithCanonicalStars G hGCD
      (FeynmanGraph.admissibleForestCanonicalContractGraph_hCD_of_ambient_onePI_divergence
        G.toFeynmanGraph hGwf hG1PI hDiv) := rfl

/-- Canonical forest-summand formula with all graph-theoretic preservation
obligations discharged from the ambient generator hypotheses and the
forest-contraction divergence preservation class. -/
noncomputable def coproductGen_strict_forestWithCanonicalStarsFromAmbientPreservation
    [IsDivergencePreservedByAdmissibleForestContract]
    (G : ConnectedFeynmanGraph)
    (hGwf : G.toFeynmanGraph.WellFormed)
    (hG1PI : G.toFeynmanGraph.IsOnePI)
    (hGCD : G.toFeynmanGraph.IsConnectedDivergent) :
    HopfH ⊗[ℚ] HopfH :=
  coproductGen_strict_forestWithCanonicalStars G hGCD
    (FeynmanGraph.admissibleForestCanonicalContractGraph_hCD_of_ambient_preservation
      G.toFeynmanGraph hGwf hG1PI hGCD)

theorem coproductGen_strict_forestWithCanonicalStarsFromAmbientPreservation_eq
    [IsDivergencePreservedByAdmissibleForestContract]
    (G : ConnectedFeynmanGraph)
    (hGwf : G.toFeynmanGraph.WellFormed)
    (hG1PI : G.toFeynmanGraph.IsOnePI)
    (hGCD : G.toFeynmanGraph.IsConnectedDivergent) :
    coproductGen_strict_forestWithCanonicalStarsFromAmbientPreservation
      G hGwf hG1PI hGCD =
    coproductGen_strict_forestWithCanonicalStars G hGCD
      (FeynmanGraph.admissibleForestCanonicalContractGraph_hCD_of_ambient_preservation
        G.toFeynmanGraph hGwf hG1PI hGCD) := rfl

/-- Same formula after reducing the 1PI obligation to the exact bridge-free
target: erasing any internal edge of the canonical forest contraction remains
support-connected. -/
noncomputable def coproductGen_strict_forestWithCanonicalStarsFromEraseConnectedDivergence
    (G : ConnectedFeynmanGraph)
    (hGwf : G.toFeynmanGraph.WellFormed)
    (hGCD : G.toFeynmanGraph.IsConnectedDivergent)
    (hEraseConn : ∀ A : AdmissibleSubgraph G.toFeynmanGraph,
      ∀ hA : A ∈ G.toFeynmanGraph.properDisjointAdmissibleDivergentSubgraphs,
        ∀ e : FeynmanEdge,
          e ∈ (FeynmanGraph.admissibleForestCanonicalContractGraph
            G.toFeynmanGraph A hA).internalEdges →
            ((FeynmanGraph.admissibleForestCanonicalContractGraph
              G.toFeynmanGraph A hA).eraseInternalEdge e).IsSupportConnected)
    (hDiv : ∀ A : AdmissibleSubgraph G.toFeynmanGraph,
      ∀ hA : A ∈ G.toFeynmanGraph.properDisjointAdmissibleDivergentSubgraphs,
        (FeynmanSubgraph.self
          (FeynmanGraph.admissibleForestCanonicalContractGraph
            G.toFeynmanGraph A hA)
          (FeynmanGraph.admissibleForestCanonicalContractGraph_wellFormed
            G.toFeynmanGraph hGwf A hA)).IsDivergent) :
    HopfH ⊗[ℚ] HopfH :=
  coproductGen_strict_forestWithCanonicalStars G hGCD
    (FeynmanGraph.admissibleForestCanonicalContractGraph_hCD_of_erase_connected_divergence
      G.toFeynmanGraph hGwf
      (ConnectedFeynmanGraph.isSupportConnected G) hEraseConn hDiv)

theorem coproductGen_strict_forestWithCanonicalStarsFromEraseConnectedDivergence_eq
    (G : ConnectedFeynmanGraph)
    (hGwf : G.toFeynmanGraph.WellFormed)
    (hGCD : G.toFeynmanGraph.IsConnectedDivergent)
    (hEraseConn : ∀ A : AdmissibleSubgraph G.toFeynmanGraph,
      ∀ hA : A ∈ G.toFeynmanGraph.properDisjointAdmissibleDivergentSubgraphs,
        ∀ e : FeynmanEdge,
          e ∈ (FeynmanGraph.admissibleForestCanonicalContractGraph
            G.toFeynmanGraph A hA).internalEdges →
            ((FeynmanGraph.admissibleForestCanonicalContractGraph
              G.toFeynmanGraph A hA).eraseInternalEdge e).IsSupportConnected)
    (hDiv : ∀ A : AdmissibleSubgraph G.toFeynmanGraph,
      ∀ hA : A ∈ G.toFeynmanGraph.properDisjointAdmissibleDivergentSubgraphs,
        (FeynmanSubgraph.self
          (FeynmanGraph.admissibleForestCanonicalContractGraph
            G.toFeynmanGraph A hA)
          (FeynmanGraph.admissibleForestCanonicalContractGraph_wellFormed
            G.toFeynmanGraph hGwf A hA)).IsDivergent) :
    coproductGen_strict_forestWithCanonicalStarsFromEraseConnectedDivergence
      G hGwf hGCD hEraseConn hDiv =
    coproductGen_strict_forestWithCanonicalStars G hGCD
      (FeynmanGraph.admissibleForestCanonicalContractGraph_hCD_of_erase_connected_divergence
        G.toFeynmanGraph hGwf
        (ConnectedFeynmanGraph.isSupportConnected G) hEraseConn hDiv) := rfl

/-- Same formula after reducing the erased-quotient connectedness obligation to
edges coming from the original complement, retargeted by the canonical
component-star assignment. -/
noncomputable def coproductGen_strict_forestWithCanonicalStarsFromRetargetEraseConnectedDivergence
    (G : ConnectedFeynmanGraph)
    (hGwf : G.toFeynmanGraph.WellFormed)
    (hGCD : G.toFeynmanGraph.IsConnectedDivergent)
    (hRetargetEraseConn : ∀ A : AdmissibleSubgraph G.toFeynmanGraph,
      ∀ hA : A ∈ G.toFeynmanGraph.properDisjointAdmissibleDivergentSubgraphs,
        ∀ e : FeynmanEdge,
          e ∈ A.complementEdges →
            ((FeynmanGraph.admissibleForestCanonicalContractGraph
              G.toFeynmanGraph A hA).eraseInternalEdge
                (A.retargetEdge
                  (FeynmanGraph.admissibleForestCanonicalStarOf
                    G.toFeynmanGraph A hA) e)).IsSupportConnected)
    (hDiv : ∀ A : AdmissibleSubgraph G.toFeynmanGraph,
      ∀ hA : A ∈ G.toFeynmanGraph.properDisjointAdmissibleDivergentSubgraphs,
        (FeynmanSubgraph.self
          (FeynmanGraph.admissibleForestCanonicalContractGraph
            G.toFeynmanGraph A hA)
          (FeynmanGraph.admissibleForestCanonicalContractGraph_wellFormed
            G.toFeynmanGraph hGwf A hA)).IsDivergent) :
    HopfH ⊗[ℚ] HopfH :=
  coproductGen_strict_forestWithCanonicalStars G hGCD
    (FeynmanGraph.admissibleForestCanonicalContractGraph_hCD_of_retarget_erase_connected_divergence
      G.toFeynmanGraph hGwf
      (ConnectedFeynmanGraph.isSupportConnected G) hRetargetEraseConn hDiv)

theorem coproductGen_strict_forestWithCanonicalStarsFromRetargetEraseConnectedDivergence_eq
    (G : ConnectedFeynmanGraph)
    (hGwf : G.toFeynmanGraph.WellFormed)
    (hGCD : G.toFeynmanGraph.IsConnectedDivergent)
    (hRetargetEraseConn : ∀ A : AdmissibleSubgraph G.toFeynmanGraph,
      ∀ hA : A ∈ G.toFeynmanGraph.properDisjointAdmissibleDivergentSubgraphs,
        ∀ e : FeynmanEdge,
          e ∈ A.complementEdges →
            ((FeynmanGraph.admissibleForestCanonicalContractGraph
              G.toFeynmanGraph A hA).eraseInternalEdge
                (A.retargetEdge
                  (FeynmanGraph.admissibleForestCanonicalStarOf
                    G.toFeynmanGraph A hA) e)).IsSupportConnected)
    (hDiv : ∀ A : AdmissibleSubgraph G.toFeynmanGraph,
      ∀ hA : A ∈ G.toFeynmanGraph.properDisjointAdmissibleDivergentSubgraphs,
        (FeynmanSubgraph.self
          (FeynmanGraph.admissibleForestCanonicalContractGraph
            G.toFeynmanGraph A hA)
          (FeynmanGraph.admissibleForestCanonicalContractGraph_wellFormed
            G.toFeynmanGraph hGwf A hA)).IsDivergent) :
    coproductGen_strict_forestWithCanonicalStarsFromRetargetEraseConnectedDivergence
      G hGwf hGCD hRetargetEraseConn hDiv =
    coproductGen_strict_forestWithCanonicalStars G hGCD
      (FeynmanGraph.admissibleForestCanonicalContractGraph_hCD_of_retarget_erase_connected_divergence
        G.toFeynmanGraph hGwf
        (ConnectedFeynmanGraph.isSupportConnected G) hRetargetEraseConn hDiv) := rfl

/-- **H4.6-strict** — Isomorphism invariance of `coproductGen_strict`.
Direct mirror of `coproductGen_isomorphism_invariant`: the
subgraph-level helpers (`mapPermSubgraph_*`, `contract_mapPerm_isIso`)
are independent of the choice of `HopfGenTemp` vs `HopfGen` packaging,
so the proof structure is identical with `gen`/`toHopfGen`/`contractToHopfGen`
replacing `gen_temp`/`toHopfGenTemp`/`contractToHopfGenTemp`.

Note: `IsOnePI` and `IsConnectedDivergent` are mapPerm-invariant
(`mapPerm_isOnePI_iff`, `mapPerm_isConnectedDivergent_iff` from
StrictGenerators.lean), so the witnesses transport across the
isomorphism. -/
theorem coproductGen_strict_isomorphism_invariant
    {G₁ G₂ : ConnectedFeynmanGraph}
    (hG₁wf : G₁.toFeynmanGraph.WellFormed) (hG₁1PI : G₁.toFeynmanGraph.IsOnePI)
    (hG₁CD : G₁.toFeynmanGraph.IsConnectedDivergent)
    (hG₂wf : G₂.toFeynmanGraph.WellFormed) (hG₂1PI : G₂.toFeynmanGraph.IsOnePI)
    (hG₂CD : G₂.toFeynmanGraph.IsConnectedDivergent)
    (h : G₁.toFeynmanGraph.IsIso G₂.toFeynmanGraph) :
    coproductGen_strict G₁ hG₁wf hG₁1PI hG₁CD =
      coproductGen_strict G₂ hG₂wf hG₂1PI hG₂CD := by
  obtain ⟨π, hπ⟩ := h
  rw [coproductGen_strict_eq, coproductGen_strict_eq]
  have hClass : G₁.toFeynmanGraph.toClass = G₂.toFeynmanGraph.toClass :=
    (FeynmanGraph.toClass_eq_iff _ _).mpr ⟨π, hπ⟩
  -- Boundary terms: unify the two genG witnesses via hClass + Subtype.ext.
  have hGen : (⟨G₁.toFeynmanGraph.toClass,
      (FeynmanGraphClass.isConnectedDivergent_toClass G₁.toFeynmanGraph).mpr
        hG₁CD⟩ : HopfGen) =
      ⟨G₂.toFeynmanGraph.toClass,
       (FeynmanGraphClass.isConnectedDivergent_toClass G₂.toFeynmanGraph).mpr
         hG₂CD⟩ := Subtype.ext hClass
  simp only [gen]
  rw [hGen]
  congr 1
  · -- Sum terms: reindex via mapPermSubgraph (same machinery as H4.6).
    apply Finset.sum_bij (fun γ _ => mapPermSubgraph hπ γ)
    · -- maps-into
      intro γ hγ
      exact (mapPermSubgraph_mem_index_iff hπ γ).mpr hγ
    · -- injective: same proof as H4.6
      intro γ₁ _ γ₂ _ heq
      apply FeynmanSubgraph.ext_iff.mpr
      have hELInj : Function.Injective (ExternalLeg.map π) := by
        intro ℓ₁ ℓ₂ h
        cases ℓ₁ with
        | mk a₁ s₁ =>
          cases ℓ₂ with
          | mk a₂ s₂ =>
            have hπa : π a₁ = π a₂ := congrArg ExternalLeg.attachedTo h
            have hs : s₁ = s₂ := congrArg ExternalLeg.sector h
            have : a₁ = a₂ := π.injective hπa
            subst this; subst hs; rfl
      refine ⟨?_, ?_, ?_⟩
      · have h := congrArg FeynmanSubgraph.vertices heq
        rw [mapPermSubgraph_vertices, mapPermSubgraph_vertices] at h
        exact Finset.image_injective π.injective h
      · have h := congrArg FeynmanSubgraph.internalEdges heq
        rw [mapPermSubgraph_internalEdges, mapPermSubgraph_internalEdges] at h
        exact Multiset.map_injective
          (FeynmanGraph.FeynmanEdge_map_injective π) h
      · have h := congrArg FeynmanSubgraph.externalLegs heq
        rw [mapPermSubgraph_externalLegs, mapPermSubgraph_externalLegs] at h
        exact Multiset.map_injective hELInj h
    · -- surjective via mapPermSubgraph_preimage
      intro γ' hγ'
      refine ⟨mapPermSubgraph_preimage hπ γ', ?_,
        mapPermSubgraph_preimage_eq hπ γ'⟩
      have := (mapPermSubgraph_mem_index_iff hπ
        (mapPermSubgraph_preimage hπ γ')).mp
      rw [mapPermSubgraph_preimage_eq] at this
      exact this hγ'
    · -- per-term equality
      intro γ hγ
      have hγ'full := (G₁.toFeynmanGraph.mem_properConnectedDivergentSubgraphs γ).mp hγ
      have hγ''full := (G₂.toFeynmanGraph.mem_properConnectedDivergentSubgraphs
          (mapPermSubgraph hπ γ)).mp
        ((mapPermSubgraph_mem_index_iff hπ γ).mpr hγ)
      have hγ' : γ.IsConnectedDivergent ∧ 0 < γ.internalEdges.card :=
        ⟨hγ'full.1, hγ'full.2.1⟩
      have hγ'' : (mapPermSubgraph hπ γ).IsConnectedDivergent ∧
          0 < (mapPermSubgraph hπ γ).internalEdges.card :=
        ⟨hγ''full.1, hγ''full.2.1⟩
      rw [dif_pos hγ', dif_pos hγ'']
      -- Build subtype equalities for both tensor factors.
      have hLeft : (γ.toHopfGen hγ'.1) =
          (mapPermSubgraph hπ γ).toHopfGen hγ''.1 :=
        Subtype.ext (mapPermSubgraph_toClass_eq hπ γ).symm
      have hRight :
          (γ.contractToHopfGen hG₁wf hG₁1PI hγ'.1
            (FeynmanSubgraph.isNonempty_of_internalEdges_pos hγ'.2)) =
          ((mapPermSubgraph hπ γ).contractToHopfGen hG₂wf hG₂1PI hγ''.1
            (FeynmanSubgraph.isNonempty_of_internalEdges_pos hγ''.2)) :=
        Subtype.ext (mapPermSubgraph_contract_toClass_eq hG₁wf hπ γ).symm
      rw [hLeft, hRight]

/-! ### H4.7-strict / H4.8-strict — class-lift + aeval extension -/

/-- **H4.7-strict** — The strict coproduct evaluated on a `HopfGen`
generator. Picks a `ConnectedFeynmanGraph` representative via
`HopfGen.toConnectedWF`, plus its `WellFormed` / `IsOnePI` / `IsCD`
witnesses, and feeds them to `coproductGen_strict`.

`HopfGen.toConnectedWF` returns `(G : ConnectedFeynmanGraph) ×' G.toFeynmanGraph.WellFormed`
where `G.toFeynmanGraph` is the chosen `Quotient.out` representative. The
1PI and CD witnesses come from `g.property : g.val.IsConnectedDivergent`
unfolded along `Quotient.out_eq`. -/
noncomputable def coproductGenClass_strict (g : HopfGen) :
    HopfH ⊗[ℚ] HopfH :=
  let GhWF := HopfGen.toConnectedWF g
  let G := GhWF.1
  let hWF : G.toFeynmanGraph.WellFormed := GhWF.2
  -- Recover IsConnectedDivergent at the graph level for G.toFeynmanGraph.
  -- HopfGen.toConnectedWF_toFeynmanGraph_toClass: G.toFeynmanGraph.toClass = g.val.
  let hClassEq : G.toFeynmanGraph.toClass = g.val :=
    HopfGen.toConnectedWF_toFeynmanGraph_toClass g
  -- g.property : g.val.IsConnectedDivergent. Transport to G.toFeynmanGraph via class equality.
  let hCD : G.toFeynmanGraph.IsConnectedDivergent :=
    (FeynmanGraphClass.isConnectedDivergent_toClass G.toFeynmanGraph).mp
      (hClassEq ▸ g.property)
  -- `(FeynmanSubgraph.self G.toFeynmanGraph hWF).IsOnePI` is definitionally
  -- `G.toFeynmanGraph.IsOnePI` (subgraph IsOnePI = toFeynmanGraph.IsOnePI = G itself).
  let hG1PI : G.toFeynmanGraph.IsOnePI := hCD.self_isConnectedDivergent.isOnePI
  coproductGen_strict G hWF hG1PI hCD

/-- **H4.8-strict** — The full strict coproduct
`Δ : HopfH →ₐ[ℚ] HopfH ⊗ HopfH`, obtained by extending
`coproductGenClass_strict` algebraically via the universal property of
`MvPolynomial`. -/
noncomputable def coproduct_strict : HopfH →ₐ[ℚ] HopfH ⊗[ℚ] HopfH :=
  MvPolynomial.aeval coproductGenClass_strict

/-- **H4.9-strict** — On a generator `X g`, the strict coproduct equals
`coproductGenClass_strict g`. -/
theorem coproduct_strict_X (g : HopfGen) :
    coproduct_strict (MvPolynomial.X g) = coproductGenClass_strict g := by
  unfold coproduct_strict
  rw [MvPolynomial.aeval_X]

/-- **H4.9-strict-expanded** — Explicit body unfold of `coproductGenClass_strict`.
The internal `HopfGen.toConnectedWF` representative is exposed so that
downstream proofs can match the body terms without needing to unfold
the private machinery in Counit/Bialgebra files. -/
theorem coproductGenClass_strict_eq (g : HopfGen) :
    coproductGenClass_strict g =
      (let GhWF := HopfGen.toConnectedWF g
       let G := GhWF.1
       let hWF : G.toFeynmanGraph.WellFormed := GhWF.2
       let hCD : G.toFeynmanGraph.IsConnectedDivergent :=
         (FeynmanGraphClass.isConnectedDivergent_toClass G.toFeynmanGraph).mp
           ((HopfGen.toConnectedWF_toFeynmanGraph_toClass g) ▸ g.property)
       let hG1PI : G.toFeynmanGraph.IsOnePI := hCD.self_isConnectedDivergent.isOnePI
       coproductGen_strict G hWF hG1PI hCD) := rfl

/-- **H4.10-strict** — `coproduct_strict 1 = 1`. -/
@[simp] theorem coproduct_strict_one : coproduct_strict (1 : HopfH) = 1 := map_one _

/-- **H4.11-strict** — `coproduct_strict` is multiplicative. -/
theorem coproduct_strict_mul (a b : HopfH) :
    coproduct_strict (a * b) = coproduct_strict a * coproduct_strict b := map_mul _ _ _

/-! ### Forest strict CK coproduct — admissible-forest target for H5.8

The connected-only `coproduct_strict` above is kept intact for the earlier
strict/counit scaffolding.  The genuine CK forest summand is now available
as a parallel algebra map, so the coassociativity decomposition can move to
the proper-disjoint admissible carrier without pretending that the
connected-only summand already contains those forest terms. -/

/-- Forest strict coproduct evaluated on a strict CK generator, using the
canonical component-star assignment and the ambient preservation entrypoint
for the contracted forest graph. -/
noncomputable def coproductGenClass_strict_forest
    [IsDivergencePreservedByAdmissibleForestContract] (g : HopfGen) :
    HopfH ⊗[ℚ] HopfH :=
  let GhWF := HopfGen.toConnectedWF g
  let G := GhWF.1
  let hWF : G.toFeynmanGraph.WellFormed := GhWF.2
  let hClassEq : G.toFeynmanGraph.toClass = g.val :=
    HopfGen.toConnectedWF_toFeynmanGraph_toClass g
  let hCD : G.toFeynmanGraph.IsConnectedDivergent :=
    (FeynmanGraphClass.isConnectedDivergent_toClass G.toFeynmanGraph).mp
      (hClassEq ▸ g.property)
  let hG1PI : G.toFeynmanGraph.IsOnePI := hCD.self_isConnectedDivergent.isOnePI
  coproductGen_strict_forestWithCanonicalStarsFromAmbientPreservation
    G hWF hG1PI hCD

/-- The full forest strict coproduct, extended multiplicatively from the
genuine proper-disjoint admissible forest summand. -/
noncomputable def coproduct_strict_forest
    [IsDivergencePreservedByAdmissibleForestContract] :
    HopfH →ₐ[ℚ] HopfH ⊗[ℚ] HopfH :=
  MvPolynomial.aeval coproductGenClass_strict_forest

/-- On a generator `X g`, the forest strict coproduct is the forest generator
formula. -/
theorem coproduct_strict_forest_X
    [IsDivergencePreservedByAdmissibleForestContract] (g : HopfGen) :
    coproduct_strict_forest (MvPolynomial.X g) =
      coproductGenClass_strict_forest g := by
  unfold coproduct_strict_forest
  rw [MvPolynomial.aeval_X]

/-- Explicit body unfold for the forest strict generator formula. -/
theorem coproductGenClass_strict_forest_eq
    [IsDivergencePreservedByAdmissibleForestContract] (g : HopfGen) :
    coproductGenClass_strict_forest g =
      (let GhWF := HopfGen.toConnectedWF g
       let G := GhWF.1
       let hWF : G.toFeynmanGraph.WellFormed := GhWF.2
       let hCD : G.toFeynmanGraph.IsConnectedDivergent :=
         (FeynmanGraphClass.isConnectedDivergent_toClass G.toFeynmanGraph).mp
           ((HopfGen.toConnectedWF_toFeynmanGraph_toClass g) ▸ g.property)
       let hG1PI : G.toFeynmanGraph.IsOnePI := hCD.self_isConnectedDivergent.isOnePI
       coproductGen_strict_forestWithCanonicalStarsFromAmbientPreservation
         G hWF hG1PI hCD) := rfl

/-- The forest strict coproduct preserves `1`. -/
@[simp] theorem coproduct_strict_forest_one
    [IsDivergencePreservedByAdmissibleForestContract] :
    coproduct_strict_forest (1 : HopfH) = 1 := map_one _

/-- The forest strict coproduct is multiplicative. -/
theorem coproduct_strict_forest_mul
    [IsDivergencePreservedByAdmissibleForestContract] (a b : HopfH) :
    coproduct_strict_forest (a * b) =
      coproduct_strict_forest a * coproduct_strict_forest b := map_mul _ _ _

/-! ### Admissible forest internal-edge API (Sprint E shared)

The four lemmas below are the minimal admissible-forest internal-edge
API that Sprint E (Antipode termination), the existing strict forest
coproduct, and any future forest-based reasoning all depend on.
Originally proved as `private` Sprint D helpers in `Coassoc.lean`;
promoted here in Sprint E because they are not coassoc-specific —
they are basic facts about the admissible carrier. -/

/-- Helper: counting commutes with `Finset.sum` over multiset-valued
functions. -/
theorem multiset_count_finset_sum {ι α : Type*} [DecidableEq α]
    (s : Finset ι) (f : ι → Multiset α) (a : α) :
    (∑ i ∈ s, f i).count a = ∑ i ∈ s, (f i).count a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
      simp [Finset.sum_insert, hi, Multiset.count_add, ih]

/-- Pairwise-disjoint admissible forest: aggregate internal edges are
bounded above by the ambient graph's. -/
theorem admissibleSubgraph_internalEdges_le_of_pairwise
    {G : FeynmanGraph} [DivergenceMeasure G] (A : AdmissibleSubgraph G)
    (hA : A.IsPairwiseDisjoint) :
    A.internalEdges ≤ G.internalEdges := by
  classical
  rw [Multiset.le_iff_count]
  intro e
  by_cases heA : e ∈ A.internalEdges
  · rcases AdmissibleSubgraph.mem_internalEdges.mp heA with ⟨γ, hγ, heγ⟩
    have hzero :
        ∀ δ ∈ A.elements, δ ≠ γ → δ.internalEdges.count e = 0 := by
      intro δ hδ hne
      by_cases heδ : e ∈ δ.internalEdges
      · have hdisj := hA hδ hγ hne
        have hsuppδ := δ.edges_supported e heδ
        have hsuppγ := γ.edges_supported e heγ
        simp [FeynmanEdge.SupportedOn] at hsuppδ hsuppγ
        exact False.elim ((Finset.disjoint_left.mp hdisj hsuppδ.1) hsuppγ.1)
      · exact Multiset.count_eq_zero.mpr heδ
    unfold AdmissibleSubgraph.internalEdges
    rw [multiset_count_finset_sum]
    calc
      (∑ x ∈ A.elements, Multiset.count e x.internalEdges)
          = γ.internalEdges.count e := by
            rw [Finset.sum_eq_single γ]
            · intro δ hδ hne
              exact hzero δ hδ hne
            · intro hγnot
              exact False.elim (hγnot hγ)
      _ ≤ G.internalEdges.count e :=
          Multiset.count_le_of_le e γ.internalEdges_le
  · rw [Multiset.count_eq_zero.mpr heA]
    exact Nat.zero_le _

/-- A component of a pairwise-disjoint admissible forest has its
internal edges contained in the aggregate forest internal-edge multiset. -/
theorem feynmanSubgraph_internalEdges_le_admissible_internalEdges_of_mem
    {G : FeynmanGraph} [DivergenceMeasure G] (A : AdmissibleSubgraph G)
    (hA : A.IsPairwiseDisjoint)
    {γ : FeynmanSubgraph G} (hγ : γ ∈ A.elements) :
    γ.internalEdges ≤ A.internalEdges := by
  classical
  rw [Multiset.le_iff_count]
  intro e
  by_cases heγ : e ∈ γ.internalEdges
  · have hzero :
        ∀ δ ∈ A.elements, δ ≠ γ → δ.internalEdges.count e = 0 := by
      intro δ hδ hne
      by_cases heδ : e ∈ δ.internalEdges
      · have hdisj := hA hδ hγ hne
        have hsuppδ := δ.edges_supported e heδ
        have hsuppγ := γ.edges_supported e heγ
        simp [FeynmanEdge.SupportedOn] at hsuppδ hsuppγ
        exact False.elim ((Finset.disjoint_left.mp hdisj hsuppδ.1) hsuppγ.1)
      · exact Multiset.count_eq_zero.mpr heδ
    unfold AdmissibleSubgraph.internalEdges
    rw [multiset_count_finset_sum]
    have hsum :
        (∑ x ∈ A.elements, Multiset.count e x.internalEdges) =
          γ.internalEdges.count e := by
      rw [Finset.sum_eq_single γ]
      · intro δ hδ hne
        exact hzero δ hδ hne
      · intro hγnot
        exact False.elim (hγnot hγ)
    rw [hsum]
  · rw [Multiset.count_eq_zero.mpr heγ]
    exact Nat.zero_le _

/-- Pairwise-disjoint admissible forest: aggregate internal edges are
bounded above by any multiset that bounds every component's internal
edges. Generalizes `_of_pairwise` from `≤ G.internalEdges` to `≤ M`. -/
theorem admissibleSubgraph_internalEdges_le_of_components_le
    {G : FeynmanGraph} [DivergenceMeasure G] (A : AdmissibleSubgraph G)
    (hA : A.IsPairwiseDisjoint) {M : Multiset FeynmanEdge}
    (hComp : ∀ γ ∈ A.elements, γ.internalEdges ≤ M) :
    A.internalEdges ≤ M := by
  classical
  rw [Multiset.le_iff_count]
  intro e
  by_cases heA : e ∈ A.internalEdges
  · rcases AdmissibleSubgraph.mem_internalEdges.mp heA with ⟨γ, hγ, heγ⟩
    have hzero :
        ∀ δ ∈ A.elements, δ ≠ γ → δ.internalEdges.count e = 0 := by
      intro δ hδ hne
      by_cases heδ : e ∈ δ.internalEdges
      · have hdisj := hA hδ hγ hne
        have hsuppδ := δ.edges_supported e heδ
        have hsuppγ := γ.edges_supported e heγ
        simp [FeynmanEdge.SupportedOn] at hsuppδ hsuppγ
        exact False.elim ((Finset.disjoint_left.mp hdisj hsuppδ.1) hsuppγ.1)
      · exact Multiset.count_eq_zero.mpr heδ
    unfold AdmissibleSubgraph.internalEdges
    rw [multiset_count_finset_sum]
    calc
      (∑ x ∈ A.elements, Multiset.count e x.internalEdges)
          = γ.internalEdges.count e := by
            rw [Finset.sum_eq_single γ]
            · intro δ hδ hne
              exact hzero δ hδ hne
            · intro hγnot
              exact False.elim (hγnot hγ)
      _ ≤ M.count e := Multiset.count_le_of_le e (hComp γ hγ)
  · rw [Multiset.count_eq_zero.mpr heA]
    exact Nat.zero_le _

/-! ### Sprint E shared carrier — proper forest index

`forestCoproductProperForestIndex g` is the index Finset shared between
`coproduct_strict_forest` (forest summand carrier with strictness
filter `0 < A.complementEdges.card`) and the Sprint E antipode (recursion
carrier on the same forest).

Originally defined privately in `Coassoc.lean` during Sprint D; promoted
to public API here in Sprint E so that `Antipode.lean` can recurse on
the same carrier without a reverse-import dependency on `Coassoc`. -/

/-- Genuine forest choices in the strict coproduct: proper disjoint
admissible forests that still leave a nonempty right complement. The
broader `properDisjointAdmissibleDivergentSubgraphs` carrier is kept
available for quotient-retarget transports that do not preserve this
extra strictness. -/
noncomputable def forestCoproductProperForestIndex
    [IsDivergencePreservedByAdmissibleForestContract] (g : HopfGen) :
    Finset (AdmissibleSubgraph (repG g).toFeynmanGraph) :=
  ((repG g).toFeynmanGraph.properDisjointAdmissibleDivergentSubgraphs).filter
    (fun A => 0 < A.complementEdges.card)

@[simp] theorem mem_forestCoproductProperForestIndex
    [IsDivergencePreservedByAdmissibleForestContract] (g : HopfGen)
    (A : AdmissibleSubgraph (repG g).toFeynmanGraph) :
    A ∈ forestCoproductProperForestIndex g ↔
      A ∈ (repG g).toFeynmanGraph.properDisjointAdmissibleDivergentSubgraphs ∧
        0 < A.complementEdges.card := by
  classical
  unfold forestCoproductProperForestIndex
  simp

/-- **Sprint E termination lemma** — for any component `γ` of any forest
`A` in the proper forest index, the strict edge-count decrease holds:

  `γ.internalEdges.card < (repG g).toFeynmanGraph.internalEdges.card`.

This is the well-foundedness witness for the antipode recursion on
`HopfGen`. -/
theorem component_internalEdges_card_lt_of_mem_forestCoproductProperForestIndex
    [IsDivergencePreservedByAdmissibleForestContract] {g : HopfGen}
    {A : AdmissibleSubgraph (repG g).toFeynmanGraph}
    (hA : A ∈ forestCoproductProperForestIndex g)
    {γ : FeynmanSubgraph (repG g).toFeynmanGraph} (hγ : γ ∈ A.elements) :
    γ.internalEdges.card < (repG g).toFeynmanGraph.internalEdges.card := by
  rw [mem_forestCoproductProperForestIndex] at hA
  obtain ⟨hAprop, hCompl⟩ := hA
  -- A is in the proper-disjoint admissible divergent carrier; extract
  -- its pairwise-disjoint witness and apply the aggregate ≤ ambient lemma.
  have hDisj : A.IsPairwiseDisjoint :=
    (repG g).toFeynmanGraph.properDisjointAdmissibleDivergentSubgraphs_isPairwiseDisjoint
      hAprop
  have hAle : A.internalEdges ≤ (repG g).toFeynmanGraph.internalEdges :=
    admissibleSubgraph_internalEdges_le_of_pairwise A hDisj
  have hγle : γ.internalEdges ≤ A.internalEdges :=
    feynmanSubgraph_internalEdges_le_admissible_internalEdges_of_mem A hDisj hγ
  -- |G.I - A.I| = |G.I| - |A.I| and 0 < |G.I - A.I| yields strict |A.I| < |G.I|.
  have hAlt : A.internalEdges.card < (repG g).toFeynmanGraph.internalEdges.card := by
    have hcard_compl : A.complementEdges.card =
        (repG g).toFeynmanGraph.internalEdges.card - A.internalEdges.card := by
      unfold AdmissibleSubgraph.complementEdges
      rw [Multiset.card_sub hAle]
    rw [hcard_compl] at hCompl
    have hcardle : A.internalEdges.card ≤ (repG g).toFeynmanGraph.internalEdges.card :=
      Multiset.card_le_card hAle
    omega
  exact lt_of_le_of_lt (Multiset.card_le_card hγle) hAlt

/-! #### Iso-invariance of `internalEdges.card` along `repG`

`repG` chooses a `Quotient.out` representative, so for any other graph
`G'` with `G'.toClass = h.val` we get `(repG h).toFeynmanGraph.IsIso G'`,
and graph isomorphism preserves `internalEdgeCount = internalEdges.card`.

This bridge is needed by the antipode well-founded recursion: the
recursive call lands on `γ.toHopfGen hγ`, whose `repG` is a Quot.out
representative possibly distinct from `γ.toFeynmanGraph`, yet has the
same internal-edge count. -/

/-- **Sprint E iso-invariance bridge** — for any `HopfGen` element `h`
and any graph `G'` whose class is `h.val`, the canonical representative
`repG h` and `G'` have equal `internalEdges.card`. -/
theorem repG_internalEdges_card_eq_of_toClass
    (h : HopfGen) {G' : FeynmanGraph} (hclass : G'.toClass = h.val) :
    (repG h).toFeynmanGraph.internalEdges.card = G'.internalEdges.card := by
  -- Both have the same toClass (= h.val), pass through the lifted
  -- internalEdgeCount to the class and compare.
  have hrepClass : (repG h).toFeynmanGraph.toClass = h.val := repG_toClass h
  have hclasses : (repG h).toFeynmanGraph.toClass = G'.toClass := by
    rw [hrepClass, ← hclass]
  -- internalEdgeCount G = G.internalEdges.card definitionally;
  -- internalEdgeCount lifts through toClass.
  have hcount :
      FeynmanGraphClass.internalEdgeCount (repG h).toFeynmanGraph.toClass =
      FeynmanGraphClass.internalEdgeCount G'.toClass := by
    rw [hclasses]
  simpa [FeynmanGraphClass.internalEdgeCount_toClass,
    FeynmanGraph.internalEdgeCount] using hcount

/-- **Sprint E antipode termination lemma** — strict edge-count decrease
on the *recursive target* `γ.toHopfGen hγ`. Combines the basic component
edge-count bound with the iso-invariance bridge above. -/
theorem repG_toHopfGen_internalEdges_card_lt_of_mem_forestCoproductProperForestIndex
    [IsDivergencePreservedByAdmissibleForestContract] {g : HopfGen}
    {A : AdmissibleSubgraph (repG g).toFeynmanGraph}
    (hA : A ∈ forestCoproductProperForestIndex g)
    {γ : FeynmanSubgraph (repG g).toFeynmanGraph} (hγ : γ ∈ A.elements)
    (hγCD : γ.IsConnectedDivergent) :
    (repG (γ.toHopfGen hγCD)).toFeynmanGraph.internalEdges.card <
      (repG g).toFeynmanGraph.internalEdges.card := by
  -- Bridge: |I (repG (γ.toHopfGen hγCD))| = |I γ.toFeynmanGraph| via class equality.
  have hcard :
      (repG (γ.toHopfGen hγCD)).toFeynmanGraph.internalEdges.card =
        γ.toFeynmanGraph.internalEdges.card := by
    apply repG_internalEdges_card_eq_of_toClass
    -- (γ.toHopfGen hγCD).val = γ.toFeynmanGraph.toClass by toHopfGen_val.
    exact FeynmanSubgraph.toHopfGen_val hγCD
  -- toFeynmanGraph_internalEdges is rfl: γ.toFeynmanGraph.internalEdges = γ.internalEdges.
  rw [hcard, FeynmanSubgraph.toFeynmanGraph_internalEdges]
  exact component_internalEdges_card_lt_of_mem_forestCoproductProperForestIndex hA hγ

end Strict

end PathW

end GaugeGeometry.QFT.Combinatorial
