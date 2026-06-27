import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocStarGeometry

/-!
# R-6c-heart-6a-5c-1 — the contract-twice vertex correspondence (the permutation scaffold)

Constructing the star permutation of `ResolvedContractTwiceClassData` directly lands in `Finset` /
subtype bookkeeping.  This file fixes the correspondence at the **function** level first: a bijection
`G₁.vertices ≃ G₂.vertices` between the one-stage and two-stage contracted graphs' vertices (surviving
original vertices fixed, the one-stage star of each component mapping to its two-stage star).

This is the scaffold for the star permutation: once `toFun` / `invFun` are constructed (next step), the
class-data star permutation is the extension of `toEquiv` to all of `VertexId`, and the three field
equalities split cleanly into

1. the vertex bijection (this file's type),
2. `retargetVertex_eq` (the retarget composition, 5c-2b-2a),
3. `internalEdges_domain` (the complement-edge correspondence, 5c-2b-2b),
4. `vertices_eq` (the star-vertex sets).

Per the HALT, `toFun` / `invFun` are **not** constructed and no field equality is proved — this only
fixes the correspondence type.

Landed:

* `ResolvedContractTwiceVertexCorrespondence G₁ G₂` — a vertex bijection (with inverse laws);
* `.toEquiv` — the bundled `G₁.vertices ≃ G₂.vertices`.

No facade, no flat term, no `forgetHopf`.  Constructing the bijection (and extending it to the star
permutation) is the remaining work.
-/

namespace GaugeGeometry.QFT.Combinatorial

/-- **R-6c-heart-6a-5c-1 — the contract-twice vertex correspondence.**  A bijection between the one-stage
(`G₁`) and two-stage (`G₂`) contracted graphs' vertices — the function-level scaffold for the star
permutation. -/
structure ResolvedContractTwiceVertexCorrespondence (G₁ G₂ : ResolvedFeynmanGraph) where
  /-- One-stage vertex ↦ two-stage vertex (surviving fixed, star ↦ star). -/
  toFun : {v : VertexId // v ∈ G₁.vertices} → {v : VertexId // v ∈ G₂.vertices}
  /-- The inverse correspondence. -/
  invFun : {v : VertexId // v ∈ G₂.vertices} → {v : VertexId // v ∈ G₁.vertices}
  /-- `invFun` is a left inverse of `toFun`. -/
  left_inv : Function.LeftInverse invFun toFun
  /-- `invFun` is a right inverse of `toFun`. -/
  right_inv : Function.RightInverse invFun toFun

/-- **R-6c-heart-6a-5c-1 — the correspondence as an `Equiv`.**  `G₁.vertices ≃ G₂.vertices`. -/
def ResolvedContractTwiceVertexCorrespondence.toEquiv {G₁ G₂ : ResolvedFeynmanGraph}
    (C : ResolvedContractTwiceVertexCorrespondence G₁ G₂) :
    {v : VertexId // v ∈ G₁.vertices} ≃ {v : VertexId // v ∈ G₂.vertices} where
  toFun := C.toFun
  invFun := C.invFun
  left_inv := C.left_inv
  right_inv := C.right_inv

end GaugeGeometry.QFT.Combinatorial
