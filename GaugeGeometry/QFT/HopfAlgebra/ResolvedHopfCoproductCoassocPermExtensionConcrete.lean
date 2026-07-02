import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocPermLeaves

/-!
# R-6c-leaf-35 — global vertex permutation extension (the one nonlocal leaf, isolated generically)

Thirtieth leaf-body discharge — isolating the sole *nonlocal* obligation: extending a finite vertex
correspondence to a global `Equiv.Perm VertexId`.  The three-route correspondence is a bijection between two
vertex `Finset`s (`corr.toEquiv : {v // v ∈ G₁.vertices} ≃ {v // v ∈ G₂.vertices}`); `VertexPermExtension corr`
asks for a global permutation restricting to it (and its inverse) on the two vertex sets.

This is a GENERIC finite-extension problem, stated here for an arbitrary type + two Finsets + a subtype
bijection (`FinsetSubtypePermExtensionSupply`), and adapted to `VertexPermExtension` via `corr.toEquiv`
(`corr.toEquiv.symm = corr.invFun`, `corr.toEquiv = corr.toFun` definitionally).  Building the `Equiv.Perm`
from the finite bijection (extending over the complements) is the genuine nonlocal content and stays the
supply's `perm` field + the two agreement laws.

Per the HALT, the `Equiv.Perm` is NOT constructed (fielded generically); Retarget / Transport / Sector untouched.

Landed:

* `FinsetSubtypePermExtensionSupply s t e` — a global `perm` restricting to `e` / `e.symm` on `t` / `s`;
* `.toVertexPermExtension corr` — the `VertexPermExtension` from the generic extension at `corr.toEquiv`;
* `.toRightPermLeafSupply` — the `ResolvedRightPermLeafSupply` (the `Perm` leaf) from a per-split-choice family.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

/-- **R-6c-leaf-35 — the generic finite-subtype permutation extension.**  A global `Equiv.Perm α` restricting
to a Finset-subtype bijection `e` on `t` and to `e.symm` on `s`. -/
structure FinsetSubtypePermExtensionSupply {α : Type*} [DecidableEq α] (s t : Finset α)
    (e : {x // x ∈ s} ≃ {x // x ∈ t}) where
  /-- The extending global permutation. -/
  perm : Equiv.Perm α
  /-- On `t`, `perm` is the inverse bijection. -/
  on_t : ∀ {v}, (hv : v ∈ t) → perm v = (e.symm ⟨v, hv⟩).1
  /-- On `s`, `perm.symm` is the forward bijection. -/
  symm_on_s : ∀ {v}, (hv : v ∈ s) → perm.symm v = (e ⟨v, hv⟩).1

/-- **R-6c-leaf-35 — the `VertexPermExtension` from the generic extension at `corr.toEquiv`. -/
def FinsetSubtypePermExtensionSupply.toVertexPermExtension {G₁ G₂ : ResolvedFeynmanGraph}
    (corr : ResolvedContractTwiceVertexCorrespondence G₁ G₂)
    (E : FinsetSubtypePermExtensionSupply G₁.vertices G₂.vertices corr.toEquiv) :
    VertexPermExtension corr where
  starPerm := E.perm
  on_vertices := fun _ hw => E.on_t hw
  inv_on_vertices := fun _ hv => E.symm_on_s hv

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}
  {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}

/-- **R-6c-leaf-35 — the `Perm` leaf (leaf-22) from a per-split-choice family of generic extensions. -/
noncomputable def ResolvedRightPermLeafSupply.ofFinsetExtension
    (Three : ResolvedThreeRouteProvedSupply D G imageOf)
    (E : ∀ s : ResolvedCoassocSplitChoice D G,
      FinsetSubtypePermExtensionSupply (oneStageContractGraph s).vertices
        (twoStageContractGraph imageOf s).vertices (Three.toVertexCorrespondence s).toEquiv) :
    ResolvedRightPermLeafSupply D G imageOf Three where
  permExt := fun s => (E s).toVertexPermExtension (Three.toVertexCorrespondence s)

end GaugeGeometry.QFT.Combinatorial
