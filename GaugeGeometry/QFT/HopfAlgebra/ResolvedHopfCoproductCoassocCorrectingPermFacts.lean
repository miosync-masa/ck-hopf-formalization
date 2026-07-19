import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocFinsetPermBody
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocStarIndexRecover
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCanonicalStarFacts
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfSubgraphMapPerm

/-!
# R-6c-body-407 — correcting-permutation machinery + star-set freshness (PROVED foundations)

Four-hundred-and-seventh genuine-body step — the load-bearing foundations for the same-forest relabeling correcting
permutation `τ` (body-406's `classData`), built from `Fstar` alone.  Per the safe split, this body lands the generic
extension machinery + the star-index recovery from `Fstar` + the two star-set freshness facts (the content that makes
`τ = σ` on ambient vertices); the star-equivalence chain, `τ := ρ * σ`, and the two action laws follow in body-408 with
the dependent ambient transport isolated there.

* `finsetSubtypeExtensionPerm_apply_of_not_mem` — the generic OUTSIDE law: the extension is the identity off `s ∪ t`
  (banked reusable, `Perm.subtypeCongr.right_apply`);
* `starIndexRecoverOfFacts` — the star-index recovery supply from `Fstar.starOf_injective` (feeds `starVertexEquivIndex`
  on both the old and the relabeled forest);
* `oldMappedStars` / `newStars` — the two star sets (`σ`-image of `A`'s stars vs the relabeled forest's stars);
* `ambient_notMem_oldMappedStars` / `ambient_notMem_newStars` — for `v ∈ G.vertices`, `σ v` lands in NEITHER star set
  (both from `starOf_fresh`): the load-bearing freshness that will give `τ v = σ v`.

Per the HALT: NO graph-data equality; `ResolvedRightTermCorrectingPermSupply` is NOT inhabited; carrier membership / hCD /
ambient edge-leg support are NOT consumed; this is not "strict equivariance"; only the generic finite-extension machinery
is reused (NOT the coassoc `starPerm` instance).  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO
`promote_collapse` / singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

/-- **R-6c-body-407 — the generic outside law.**  `finsetSubtypeExtensionPerm` is the identity off `s ∪ t`. -/
theorem finsetSubtypeExtensionPerm_apply_of_not_mem {α : Type*} [DecidableEq α] (s t : Finset α)
    (e : {x // x ∈ s} ≃ {x // x ∈ t}) {v : α} (hvs : v ∉ s) (hvt : v ∉ t) :
    finsetSubtypeExtensionPerm s t e v = v := by
  have hvU : ¬ (v ∈ s ∪ t) := fun h => (Finset.mem_union.mp h).elim hvs hvt
  rw [finsetSubtypeExtensionPerm, Equiv.Perm.subtypeCongr.right_apply _ _ hvU]
  rfl

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

variable {R : ResolvedCoproductProperForestRawData}

set_option linter.unusedSectionVars false

/-- **R-6c-body-407 — the star-index recovery supply from the canonical star facts.**  `starOf_injective` is exactly
the no-collision inverse that `starVertexEquivIndex` needs.  (Body-412: over the raw core `R`.) -/
def starIndexRecoverOfFacts (Fstar : ResolvedCanonicalStarRawFacts R) {G : ResolvedFeynmanGraph}
    (A : ResolvedAdmissibleSubgraph G) : ResolvedStarIndexRecoverSupply A (R.starOf G A) where
  star_injective_on_elements := Fstar.starOf_injective G A

/-- **R-6c-body-407 — the `σ`-image of `A`'s star vertices.** -/
noncomputable def oldMappedStars (R : ResolvedCoproductProperForestRawData) {G : ResolvedFeynmanGraph} (σ : Equiv.Perm VertexId)
    (A : ResolvedAdmissibleSubgraph G) : Finset VertexId :=
  (A.starVertices (R.starOf G A)).image σ

/-- **R-6c-body-407 — the relabeled forest's star vertices.** -/
noncomputable def newStars (R : ResolvedCoproductProperForestRawData) {G : ResolvedFeynmanGraph} (σ : Equiv.Perm VertexId)
    (A : ResolvedAdmissibleSubgraph G) : Finset VertexId :=
  (A.mapPerm σ).starVertices (R.starOf (G.mapPerm σ) (A.mapPerm σ))

/-- **R-6c-body-407 — an ambient vertex's `σ`-image avoids the old mapped stars** (from `starOf_fresh`). -/
theorem ambient_notMem_oldMappedStars (Fstar : ResolvedCanonicalStarRawFacts R)
    {G : ResolvedFeynmanGraph} (σ : Equiv.Perm VertexId) (A : ResolvedAdmissibleSubgraph G)
    {v : VertexId} (hv : v ∈ G.vertices) : σ v ∉ oldMappedStars R σ A := by
  intro hmem
  obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp hmem
  rw [σ.injective hwv] at hw
  obtain ⟨γ, hγ, hγv⟩ := ResolvedAdmissibleSubgraph.mem_starVertices.mp hw
  exact Fstar.starOf_fresh G A γ hγ (hγv ▸ hv)

/-- **R-6c-body-407 — an ambient vertex's `σ`-image avoids the new stars** (from `starOf_fresh` on `G.mapPerm σ`). -/
theorem ambient_notMem_newStars (Fstar : ResolvedCanonicalStarRawFacts R)
    {G : ResolvedFeynmanGraph} (σ : Equiv.Perm VertexId) (A : ResolvedAdmissibleSubgraph G)
    {v : VertexId} (hv : v ∈ G.vertices) : σ v ∉ newStars R σ A := by
  intro hmem
  obtain ⟨γσ, hγσ, hγσv⟩ := ResolvedAdmissibleSubgraph.mem_starVertices.mp hmem
  refine Fstar.starOf_fresh (G.mapPerm σ) (A.mapPerm σ) γσ hγσ ?_
  rw [hγσv]
  exact Finset.mem_image_of_mem σ hv

end GaugeGeometry.QFT.Combinatorial
