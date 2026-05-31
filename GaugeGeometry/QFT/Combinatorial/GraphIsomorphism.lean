import GaugeGeometry.QFT.Combinatorial.Permutation
import Mathlib.GroupTheory.GroupAction.Defs

/-!
# Graph isomorphism and the orbit relation

Two Feynman graphs are *isomorphic* if they are in the same orbit under
the `Equiv.Perm VertexId`-action defined in `Permutation.lean`.

This file provides:

* `FeynmanGraph.IsIso` — the orbit relation, stated in the direct `∃ π`
  form,
* `Setoid` and `Equivalence` instances showing it is an equivalence
  relation,
* basic lemmas connecting it to the `MulAction` structure.

The passage to actual isomorphism *classes* (a quotient type) and the
lift of combinatorial invariants is handled in a downstream file.
-/

namespace GaugeGeometry.QFT.Combinatorial

namespace FeynmanGraph

/--
Two Feynman graphs are isomorphic if one is obtained from the other by
relabeling vertices through a permutation of `VertexId`.

This is exactly the orbit relation of the `Equiv.Perm VertexId`-action
on `FeynmanGraph`.
-/
def IsIso (G₁ G₂ : FeynmanGraph) : Prop :=
  ∃ π : Equiv.Perm VertexId, G₂ = G₁.mapPerm π

/-!
### Equivalence relation properties
-/

theorem IsIso.refl (G : FeynmanGraph) : G.IsIso G :=
  ⟨1, by rw [mapPerm_one]⟩

theorem IsIso.symm {G₁ G₂ : FeynmanGraph} (h : G₁.IsIso G₂) : G₂.IsIso G₁ := by
  obtain ⟨π, hπ⟩ := h
  refine ⟨π⁻¹, ?_⟩
  rw [hπ, ← mapPerm_mul]
  simp

theorem IsIso.trans {G₁ G₂ G₃ : FeynmanGraph}
    (h₁₂ : G₁.IsIso G₂) (h₂₃ : G₂.IsIso G₃) : G₁.IsIso G₃ := by
  obtain ⟨π, hπ⟩ := h₁₂
  obtain ⟨σ, hσ⟩ := h₂₃
  refine ⟨σ * π, ?_⟩
  rw [hσ, hπ, mapPerm_mul]

theorem isIso_equivalence : Equivalence (IsIso : FeynmanGraph → FeynmanGraph → Prop) :=
  { refl := IsIso.refl
    symm := IsIso.symm
    trans := IsIso.trans }

/-- The `Setoid` induced by `IsIso`. -/
def isoSetoid : Setoid FeynmanGraph where
  r := IsIso
  iseqv := isIso_equivalence

/-!
### Connection to the `MulAction` orbit relation
-/

theorem isIso_iff_orbitRel (G₁ G₂ : FeynmanGraph) :
    G₁.IsIso G₂ ↔ MulAction.orbitRel (Equiv.Perm VertexId) FeynmanGraph G₁ G₂ := by
  -- `MulAction.orbitRel _ _ x y` unfolds to `∃ m, m • y = x`, i.e. `y` is
  -- moved to `x`. Our `IsIso G₁ G₂ := ∃ π, G₂ = G₁.mapPerm π` moves `G₁` to
  -- `G₂`, so we need to pass through the inverse permutation.
  constructor
  · rintro ⟨π, hπ⟩
    refine ⟨π⁻¹, ?_⟩
    show π⁻¹ • G₂ = G₁
    rw [hπ]
    show (G₁.mapPerm π).mapPerm π⁻¹ = G₁
    rw [← mapPerm_mul]
    simp
  · rintro ⟨π, hπ⟩
    refine ⟨π⁻¹, ?_⟩
    show G₂ = G₁.mapPerm π⁻¹
    have : π • G₂ = G₁ := hπ
    have : G₁ = G₂.mapPerm π := this.symm
    rw [this, ← mapPerm_mul]
    simp

/-!
### Transport of numeric invariants along an isomorphism

These are direct consequences of `mapPerm_*Count` and `mapPerm_loopNumber`
from `Permutation.lean`, lifted to the `IsIso` setting.
-/

theorem IsIso.vertexCount_eq {G₁ G₂ : FeynmanGraph} (h : G₁.IsIso G₂) :
    G₁.vertexCount = G₂.vertexCount := by
  obtain ⟨π, rfl⟩ := h
  simp

theorem IsIso.internalEdgeCount_eq {G₁ G₂ : FeynmanGraph} (h : G₁.IsIso G₂) :
    G₁.internalEdgeCount = G₂.internalEdgeCount := by
  obtain ⟨π, rfl⟩ := h
  simp

theorem IsIso.externalLegCount_eq {G₁ G₂ : FeynmanGraph} (h : G₁.IsIso G₂) :
    G₁.externalLegCount = G₂.externalLegCount := by
  obtain ⟨π, rfl⟩ := h
  simp

theorem IsIso.loopNumber_eq {G₁ G₂ : FeynmanGraph} (h : G₁.IsIso G₂) :
    G₁.loopNumber = G₂.loopNumber := by
  obtain ⟨π, rfl⟩ := h
  simp

end FeynmanGraph

/-!
## Quotient by graph isomorphism

`FeynmanGraphClass` is the quotient of `FeynmanGraph` by `IsIso`.
Its elements are isomorphism classes of labeled Feynman graphs, which
is the correct setting for Hopf-algebra generators in Connes–Kreimer
style renormalization.
-/

/-- Isomorphism classes of Feynman graphs. -/
def FeynmanGraphClass : Type := Quotient FeynmanGraph.isoSetoid

namespace FeynmanGraph

/-- The isomorphism class of a Feynman graph. -/
def toClass (G : FeynmanGraph) : FeynmanGraphClass :=
  Quotient.mk FeynmanGraph.isoSetoid G

@[simp] theorem toClass_eq_iff (G₁ G₂ : FeynmanGraph) :
    G₁.toClass = G₂.toClass ↔ G₁.IsIso G₂ := by
  exact Quotient.eq

end FeynmanGraph

namespace FeynmanGraphClass

/-- Vertex count lifted to isomorphism classes. -/
def vertexCount : FeynmanGraphClass → Nat :=
  Quotient.lift FeynmanGraph.vertexCount (fun _ _ h => h.vertexCount_eq)

/-- Internal-edge count lifted to isomorphism classes. -/
def internalEdgeCount : FeynmanGraphClass → Nat :=
  Quotient.lift FeynmanGraph.internalEdgeCount
    (fun _ _ h => h.internalEdgeCount_eq)

/-- External-leg count lifted to isomorphism classes. -/
def externalLegCount : FeynmanGraphClass → Nat :=
  Quotient.lift FeynmanGraph.externalLegCount
    (fun _ _ h => h.externalLegCount_eq)

/-- Euler loop number lifted to isomorphism classes. -/
def loopNumber : FeynmanGraphClass → Int :=
  Quotient.lift FeynmanGraph.loopNumber (fun _ _ h => h.loopNumber_eq)

@[simp] theorem vertexCount_toClass (G : FeynmanGraph) :
    vertexCount G.toClass = G.vertexCount := rfl

@[simp] theorem internalEdgeCount_toClass (G : FeynmanGraph) :
    internalEdgeCount G.toClass = G.internalEdgeCount := rfl

@[simp] theorem externalLegCount_toClass (G : FeynmanGraph) :
    externalLegCount G.toClass = G.externalLegCount := rfl

@[simp] theorem loopNumber_toClass (G : FeynmanGraph) :
    loopNumber G.toClass = G.loopNumber := rfl

end FeynmanGraphClass

end GaugeGeometry.QFT.Combinatorial
