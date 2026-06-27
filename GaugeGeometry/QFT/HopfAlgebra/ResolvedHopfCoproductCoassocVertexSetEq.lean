import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocClassDataFromVertexCorr

/-!
# R-6c-heart-6a-5c-3b — `vertices_eq` from the perm extension (generic)

The `vertices_eq` field equality `G₁.vertices = (G₂.mapPerm E.starPerm).vertices` is **generic** — it
needs only that `E.starPerm` agrees with the vertex correspondence on the vertices (`E.on_vertices`) and
that the correspondence is a bijection (`corr.left_inv`).  It does **not** touch the concrete
`starToStar` / `surviving_to`, so it closes outright.

So once the perm extension is in hand, the `vertices_eq` obligation of `ResolvedContractTwiceFieldEqSupply`
is **discharged**, leaving `internalEdges_eq` (the complement-edge domain) and `externalLegs_eq` (free via
the retarget route).

Landed:

* `vertices_eq_of_perm_extension` — `G₁.vertices = (G₂.mapPerm E.starPerm).vertices` from `on_vertices` +
  `corr.left_inv`;
* `ResolvedContractTwiceFieldEqSupply.ofVerticesAuto` — fill `vertices_eq` automatically, taking only the
  edge/leg equalities.

No facade, no flat term, no `forgetHopf`.  `internalEdges_eq`, the star bijection, and the perm extension
are the remaining work.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {G₁ G₂ : ResolvedFeynmanGraph}

/-- **R-6c-heart-6a-5c-3b — `vertices_eq` from the perm extension.**  `G₁.vertices = (G₂.mapPerm
E.starPerm).vertices` — the permutation maps `G₂`'s vertices onto `G₁`'s via the (bijective) inverse
correspondence.  Generic: independent of the concrete star map. -/
theorem vertices_eq_of_perm_extension
    {corr : ResolvedContractTwiceVertexCorrespondence G₁ G₂} (E : VertexPermExtension corr) :
    G₁.vertices = (G₂.mapPerm E.starPerm).vertices := by
  show G₁.vertices = G₂.vertices.image E.starPerm
  ext v
  rw [Finset.mem_image]
  constructor
  · intro hv
    refine ⟨(corr.toFun ⟨v, hv⟩).1, (corr.toFun ⟨v, hv⟩).2, ?_⟩
    have hstar : E.starPerm (corr.toFun ⟨v, hv⟩).1
        = (corr.invFun (corr.toFun ⟨v, hv⟩)).1 := E.on_vertices _ (corr.toFun ⟨v, hv⟩).2
    rw [hstar, corr.left_inv ⟨v, hv⟩]
  · rintro ⟨w, hw, rfl⟩
    rw [E.on_vertices w hw]
    exact (corr.invFun ⟨w, hw⟩).2

/-- **R-6c-heart-6a-5c-3b — field-equality supply with `vertices_eq` auto-filled.**  Only the edge/leg
equalities remain as inputs. -/
def ResolvedContractTwiceFieldEqSupply.ofVerticesAuto
    {corr : ResolvedContractTwiceVertexCorrespondence G₁ G₂} (E : VertexPermExtension corr)
    (internalEdges_eq : G₁.internalEdges = (G₂.mapPerm E.starPerm).internalEdges)
    (externalLegs_eq : G₁.externalLegs = (G₂.mapPerm E.starPerm).externalLegs) :
    ResolvedContractTwiceFieldEqSupply E where
  vertices_eq := vertices_eq_of_perm_extension E
  internalEdges_eq := internalEdges_eq
  externalLegs_eq := externalLegs_eq

end GaugeGeometry.QFT.Combinatorial
