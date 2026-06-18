import GaugeGeometry.QFT.Combinatorial.ResolvedFeynmanGraphs
import GaugeGeometry.QFT.Combinatorial.GraphIsomorphism
import GaugeGeometry.QFT.HopfAlgebra.StrictGenerators

/-!
# R-6a — the resolved-generator Hopf carrier scaffold

The flat Hopf algebra carrier `HopfH = MvPolynomial HopfGen ℚ` is built on
`HopfGen = { c : FeynmanGraphClass // c.IsConnectedDivergent }`, where
`FeynmanGraphClass = Quotient FeynmanGraph.isoSetoid` **already collapses the edge/leg
identities** at the generator level (ordinary graph isomorphism relabels vertices and
quotients away the persistent `edgeId`/`legId`).  That is the deepest root of the two
boundary facades: the algebra's own generators are id-forgotten classes.

This file builds the **parallel resolved-native carrier** that does *not* discard identity
at the algebra level:

* `ResolvedFeynmanGraph.mapPerm` — vertex relabeling that **preserves** `edgeId`/`legId`;
* `ResolvedFeynmanGraph.IsIso` / `idIsoSetoid` — id-preserving isomorphism (the orbit of
  the vertex-permutation action on resolved graphs); **not** flat graph iso;
* `ResolvedFeynmanGraphClass = Quotient idIsoSetoid` with the forgetful
  `toFlatClass : ResolvedFeynmanGraphClass → FeynmanGraphClass`;
* `ResolvedHopfGen = { c : ResolvedFeynmanGraphClass // (toFlatClass c).IsConnectedDivergent }`,
  `ResolvedHopfH = MvPolynomial ResolvedHopfGen ℚ`;
* `forgetHopf : ResolvedHopfH →ₐ[ℚ] HopfH`, the algebra morphism forgetting the ids.

**No coproduct is defined here** (that is R-6b).  This is the first stone: the algebra
carrier that keeps the half-edge/leg identities Lean has shown the facades depend on.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

/-! ## Identity-preserving vertex relabeling on resolved graphs -/

namespace ResolvedFeynmanEdge

/-- Relabel an edge's endpoints by `π`, **preserving** `edgeId`/`sector`. -/
def map (π : Equiv.Perm VertexId) (e : ResolvedFeynmanEdge) : ResolvedFeynmanEdge :=
  { edgeId := e.edgeId, source := π e.source, target := π e.target, sector := e.sector }

@[simp] theorem map_one (e : ResolvedFeynmanEdge) : e.map 1 = e := by cases e; rfl

@[simp] theorem map_mul (π σ : Equiv.Perm VertexId) (e : ResolvedFeynmanEdge) :
    e.map (π * σ) = (e.map σ).map π := by cases e; rfl

@[simp] theorem forget_map (π : Equiv.Perm VertexId) (e : ResolvedFeynmanEdge) :
    (e.map π).forget = (e.forget).map π := by cases e; rfl

end ResolvedFeynmanEdge

namespace ResolvedExternalLeg

/-- Relabel a leg's attachment by `π`, **preserving** `legId`/`sector`. -/
def map (π : Equiv.Perm VertexId) (ℓ : ResolvedExternalLeg) : ResolvedExternalLeg :=
  { legId := ℓ.legId, attachedTo := π ℓ.attachedTo, sector := ℓ.sector }

@[simp] theorem map_one (ℓ : ResolvedExternalLeg) : ℓ.map 1 = ℓ := by cases ℓ; rfl

@[simp] theorem map_mul (π σ : Equiv.Perm VertexId) (ℓ : ResolvedExternalLeg) :
    ℓ.map (π * σ) = (ℓ.map σ).map π := by cases ℓ; rfl

@[simp] theorem forget_map (π : Equiv.Perm VertexId) (ℓ : ResolvedExternalLeg) :
    (ℓ.map π).forget = (ℓ.forget).map π := by cases ℓ; rfl

end ResolvedExternalLeg

namespace ResolvedFeynmanGraph

/-- Transport a resolved graph along a vertex permutation, **preserving all ids**. -/
def mapPerm (π : Equiv.Perm VertexId) (G : ResolvedFeynmanGraph) : ResolvedFeynmanGraph where
  vertices := G.vertices.image π
  internalEdges := G.internalEdges.map (ResolvedFeynmanEdge.map π)
  externalLegs := G.externalLegs.map (ResolvedExternalLeg.map π)

@[simp] theorem mapPerm_one (G : ResolvedFeynmanGraph) : G.mapPerm 1 = G := by
  unfold mapPerm
  have hV : G.vertices.image (1 : Equiv.Perm VertexId) = G.vertices := by ext v; simp
  have hI : G.internalEdges.map (ResolvedFeynmanEdge.map 1) = G.internalEdges := by
    simp
  have hE : G.externalLegs.map (ResolvedExternalLeg.map 1) = G.externalLegs := by
    simp
  rw [hV, hI, hE]

theorem mapPerm_mul (π σ : Equiv.Perm VertexId) (G : ResolvedFeynmanGraph) :
    G.mapPerm (π * σ) = (G.mapPerm σ).mapPerm π := by
  unfold mapPerm
  have hV : G.vertices.image (π * σ) = (G.vertices.image σ).image π := by
    rw [show ((π * σ : Equiv.Perm VertexId) : VertexId → VertexId)
        = (π : VertexId → VertexId) ∘ (σ : VertexId → VertexId) from rfl]
    exact Finset.image_image.symm
  have hI : G.internalEdges.map (ResolvedFeynmanEdge.map (π * σ))
      = (G.internalEdges.map (ResolvedFeynmanEdge.map σ)).map (ResolvedFeynmanEdge.map π) := by
    rw [Multiset.map_map]; exact Multiset.map_congr rfl (fun e _ => by simp)
  have hE : G.externalLegs.map (ResolvedExternalLeg.map (π * σ))
      = (G.externalLegs.map (ResolvedExternalLeg.map σ)).map (ResolvedExternalLeg.map π) := by
    rw [Multiset.map_map]; exact Multiset.map_congr rfl (fun ℓ _ => by simp)
  rw [hV, hI, hE]

/-- **The forgetful square**: relabeling-then-forgetting equals forgetting-then-relabeling.
This makes `toFlatClass` well defined (an id-preserving iso forgets to a flat iso). -/
@[simp] theorem forget_mapPerm (π : Equiv.Perm VertexId) (G : ResolvedFeynmanGraph) :
    (G.mapPerm π).forget = (G.forget).mapPerm π := by
  obtain ⟨v, ie, el⟩ := G
  simp only [mapPerm, ResolvedFeynmanGraph.forget, FeynmanGraph.mapPerm, Multiset.map_map,
    FeynmanGraph.mk.injEq, true_and]
  refine ⟨?_, ?_⟩
  · exact Multiset.map_congr rfl (fun e _ => by simp)
  · exact Multiset.map_congr rfl (fun ℓ _ => by simp)

/-! ## Identity-preserving isomorphism and its quotient -/

/-- Id-preserving isomorphism: the orbit of the vertex-permutation action on resolved
graphs.  Because `mapPerm` preserves `edgeId`/`legId`, two resolved graphs are equivalent
iff they differ by a vertex relabeling with the **identities intact**. -/
def IsIso (G₁ G₂ : ResolvedFeynmanGraph) : Prop :=
  ∃ π : Equiv.Perm VertexId, G₂ = G₁.mapPerm π

theorem IsIso.refl (G : ResolvedFeynmanGraph) : G.IsIso G := ⟨1, by rw [mapPerm_one]⟩

theorem IsIso.symm {G₁ G₂ : ResolvedFeynmanGraph} (h : G₁.IsIso G₂) : G₂.IsIso G₁ := by
  obtain ⟨π, hπ⟩ := h
  exact ⟨π⁻¹, by rw [hπ, ← mapPerm_mul]; simp⟩

theorem IsIso.trans {G₁ G₂ G₃ : ResolvedFeynmanGraph}
    (h₁₂ : G₁.IsIso G₂) (h₂₃ : G₂.IsIso G₃) : G₁.IsIso G₃ := by
  obtain ⟨π, hπ⟩ := h₁₂
  obtain ⟨σ, hσ⟩ := h₂₃
  exact ⟨σ * π, by rw [hσ, hπ, mapPerm_mul]⟩

theorem isIso_equivalence : Equivalence (IsIso : ResolvedFeynmanGraph → ResolvedFeynmanGraph → Prop) :=
  { refl := IsIso.refl, symm := IsIso.symm, trans := IsIso.trans }

/-- The id-preserving isomorphism `Setoid` (NOT the flat graph iso). -/
def idIsoSetoid : Setoid ResolvedFeynmanGraph where
  r := IsIso
  iseqv := isIso_equivalence

end ResolvedFeynmanGraph

/-- Identity-preserving isomorphism classes of resolved Feynman graphs — the resolved
analogue of `FeynmanGraphClass`, but retaining the persistent edge/leg ids. -/
def ResolvedFeynmanGraphClass : Type := Quotient ResolvedFeynmanGraph.idIsoSetoid

namespace ResolvedFeynmanGraph

/-- The id-preserving isomorphism class of a resolved graph. -/
def toResolvedClass (G : ResolvedFeynmanGraph) : ResolvedFeynmanGraphClass :=
  Quotient.mk ResolvedFeynmanGraph.idIsoSetoid G

end ResolvedFeynmanGraph

namespace ResolvedFeynmanGraphClass

/-- Forget the ids on a class: the flat isomorphism class of the forgotten graph.  Well
defined because an id-preserving iso forgets to a flat iso (`forget_mapPerm`). -/
def toFlatClass : ResolvedFeynmanGraphClass → FeynmanGraphClass :=
  Quotient.lift (fun G => G.forget.toClass) <| by
    intro a b h
    obtain ⟨π, hπ⟩ := h
    show a.forget.toClass = b.forget.toClass
    rw [hπ, ResolvedFeynmanGraph.forget_mapPerm]
    exact (FeynmanGraph.toClass_eq_iff _ _).mpr ⟨π, rfl⟩

@[simp] theorem toFlatClass_mk (G : ResolvedFeynmanGraph) :
    toFlatClass G.toResolvedClass = G.forget.toClass := rfl

end ResolvedFeynmanGraphClass

/-! ## The resolved-generator algebra carrier

The connected-divergence predicate (hence `HopfGen`/`ResolvedHopfGen`) lives in the ambient
`DivergenceMeasure` environment, so we open the same section variable the flat
`StrictGenerators` uses. -/

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]

/-- **R-6a — resolved-native Hopf generators**: id-preserving classes of connected
divergent resolved Feynman graphs.  The connected-divergence predicate is read on the
forgotten flat class (it is an iso-invariant of the flat class), so a generator is a
resolved graph class whose flat shadow is a flat generator. -/
abbrev ResolvedHopfGen : Type :=
  { c : ResolvedFeynmanGraphClass // (ResolvedFeynmanGraphClass.toFlatClass c).IsConnectedDivergent }

/-- Forget a resolved generator to its flat generator (forget the ids on the class). -/
def ResolvedHopfGen.forget (x : ResolvedHopfGen) : HopfGen :=
  Subtype.mk (ResolvedFeynmanGraphClass.toFlatClass x.val) x.property

/-- **R-6a — the resolved-native Hopf algebra carrier**: the free commutative ℚ-algebra on
the resolved generators.  `CommRing`/`Algebra ℚ` come from Mathlib automatically. -/
noncomputable abbrev ResolvedHopfH : Type := MvPolynomial ResolvedHopfGen ℚ

noncomputable example : CommRing ResolvedHopfH := inferInstance
noncomputable example : Algebra ℚ ResolvedHopfH := inferInstance

/-- **R-6a — the forgetful algebra morphism** `ResolvedHopfH →ₐ HopfH`, sending each
resolved generator to its flat shadow.  An algebra map (not injective — `forget` collapses
the ids). -/
noncomputable def forgetHopf : ResolvedHopfH →ₐ[ℚ] HopfH :=
  MvPolynomial.aeval (fun x : ResolvedHopfGen => MvPolynomial.X x.forget)

@[simp] theorem forgetHopf_X (x : ResolvedHopfGen) :
    forgetHopf (MvPolynomial.X x) = MvPolynomial.X x.forget := by
  simp [forgetHopf]

end GaugeGeometry.QFT.Combinatorial