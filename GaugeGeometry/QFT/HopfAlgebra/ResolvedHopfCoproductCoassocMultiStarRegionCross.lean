import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocConcreteRightRegion
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocParametricCarrierClosure
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocComponentNonempty

/-!
# R-6c-body-338 — the multi-star region core: three cross vertex-disjointnesses + raw union + tag exclusivities

Three-hundred-and-thirty-eighth genuine-body step — bundles the concrete right region (body-337) and the
multi-star forest region (body-332) with the untouched left residual (body-323) into a raw three-region
union, and PROVES the three cross vertex-disjointnesses that the union needs.  The cross-disjointnesses are
NOT "star-avoiding vs star-touching" hand-waving — they are load-bearing on the body-329/330 retarget
geometry:

* **left ↔ right** — a left component sits in `z.1.1.vertices`; a `rightReembed` survivor sits in
  `G \ z.1.1` (`starAvoiding_notMem_outer`).  Directly disjoint.
* **left ↔ forest** — a shared `v` would put `v ∈ z.1.1.vertices` (left) AND `v ∈ parent(δ).vertices`; the
  star-membership engine `localizedParent_star_mem` (330) then forces `starOf(componentAt v) ∈ δ.vertices`,
  i.e. the left component IS `representedByTouched` — contradicting its left-residual membership (323).
* **right ↔ forest** — from the right side `v ∉ z.1.1.vertices`, so the forest parent's retarget is the
  IDENTITY at `v` (`localizedParentVertex_retargets` 329 + `retargetVertex_of_not_mem`); hence `v` lies in
  BOTH quotient components `δ_r` (right, star-avoiding) and `δ_f` (forest, star-touching).  But
  `rightDomain ∩ forestDomain = ∅`, so `δ_r ≠ δ_f` and `z.2.1.pairwiseDisjoint` is contradicted.

The three element-level tag exclusivities follow: a graph in two regions would be self-disjoint, but
`cd_nonempty` (the measure-level nonemptiness, NOT `IsConnectedDivergent` alone) makes every region
component vertex-nonempty.

Landed (all axiom-clean):

* `starAvoiding_notMem_outer` — a star-avoiding `δ`-vertex avoids `z.1.1`;
* `left_right_cross` / `left_forest_cross` / `right_forest_cross` — the three cross vertex-disjointnesses;
* `leftRegion` / `rightRegion` / `forestRegion` (+ `_elements` rfl) — the three concrete regions;
* `regionRawUnion` — the raw three-region union (via `recoveredRawUnion`, PROVED, choice/carrier-free);
* `right_notMem_left` / `forest_notMem_left` / `forest_notMem_right` — the three tag exclusivities
  (cross + `cd_nonempty`).

Per the HALT: raw union + exclusivities are PROVED; `recovered_raw_mem` is the model gate (NOT entered);
the `ResolvedRegionTagValueSupply` converter is a closure-conditional construction (body-339+); carrier
membership is NOT used in any cross-disjointness proof.  No facade, no flat term, no `forgetHopf`, no
rep/perm.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

set_option linter.unusedSectionVars false

/-- **R-6c-body-338 — a star-avoiding survivor vertex avoids the outer forest.**  For `v ∈ δ.vertices`
(star-avoiding `δ`), `v ∉ z.1.1.vertices` (it sits in `G \ z.1.1`, not on a star). -/
theorem starAvoiding_notMem_outer (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
    (hstar : Disjoint δ.vertices (z.1.1.starVertices (D.starOf G z.1.1)))
    {v : VertexId} (hv : v ∈ δ.vertices) : v ∉ z.1.1.vertices := by
  intro hvz
  have hmem := δ.vertices_subset hv
  rw [ResolvedAdmissibleSubgraph.contractWithStars_vertices, Finset.mem_union] at hmem
  cases hmem with
  | inl h => exact (Finset.mem_sdiff.mp h).2 hvz
  | inr h => exact absurd h (Finset.disjoint_left.mp hstar hv)

/-- **R-6c-body-338 — left ↔ right cross-disjointness.**  A left-residual outer component and a `rightReembed`
survivor are vertex-disjoint (`z.1.1` vs `G \ z.1.1`). -/
theorem left_right_cross (z : ForestBlockCodType D G)
    {A : ResolvedFeynmanSubgraph G} (hA : A ∈ leftResidualTouched z)
    {R : ResolvedFeynmanSubgraph G} (hR : R ∈ (rightDomain z).attach.image (rightReembed z)) :
    A.Disjoint R := by
  obtain ⟨δr, -, rfl⟩ := Finset.mem_image.mp hR
  show _root_.Disjoint A.vertices (rightReembed z δr).vertices
  rw [Finset.disjoint_left]
  intro v hvA hvR
  rw [rightReembed_vertices] at hvR
  have hAz : A ∈ z.1.1.elements := (Finset.mem_filter.mp hA).1
  have hvz : v ∈ z.1.1.vertices := ResolvedAdmissibleSubgraph.mem_vertices.mpr ⟨A, hAz, hvA⟩
  exact starAvoiding_notMem_outer z δr.1 (Finset.mem_filter.mp δr.2).2 hvR hvz

/-- **R-6c-body-338 — left ↔ forest cross-disjointness.**  A left-residual outer component and a
de-contracted forest parent are vertex-disjoint: a shared vertex would make the left component
`representedByTouched` via `localizedParent_star_mem` (330). -/
theorem left_forest_cross (M : ResolvedMultiStarDecontractionSupply D)
    (F : ResolvedCanonicalStarFacts D) (z : ForestBlockCodType D G)
    {A : ResolvedFeynmanSubgraph G} (hA : A ∈ leftResidualTouched z)
    {P : ResolvedFeynmanSubgraph G}
    (hP : P ∈ (forestDomain z).attach.image (fun δ => M.parent z δ)) : A.Disjoint P := by
  obtain ⟨δf, -, rfl⟩ := Finset.mem_image.mp hP
  show _root_.Disjoint A.vertices (M.parent z δf).vertices
  rw [Finset.disjoint_left]
  intro v hvA hvP
  have hAz : A ∈ z.1.1.elements := (Finset.mem_filter.mp hA).1
  have hnr : ¬ representedByTouched z A := (Finset.mem_filter.mp hA).2
  have hvz : v ∈ z.1.1.vertices := ResolvedAdmissibleSubgraph.mem_vertices.mpr ⟨A, hAz, hvA⟩
  have hstar := localizedParent_star_mem F z δf.1 (M.legLift z δf) (M.hE z) (M.hL z) hvz hvP
  have hcomp : z.1.1.componentAt hvz = A := by
    by_contra hAne
    exact Finset.disjoint_left.mp
      (z.1.1.pairwiseDisjoint (z.1.1.componentAt_mem hvz) hAz hAne)
      (z.1.1.componentAt_vertex_mem hvz) hvA
  rw [hcomp] at hstar
  exact hnr ⟨δf.1, δf.2, mem_touchedOuterComponents.mpr ⟨hAz, hstar⟩⟩

/-- **R-6c-body-338 — right ↔ forest cross-disjointness.**  A `rightReembed` survivor and a de-contracted
forest parent are vertex-disjoint: a shared vertex avoids `z.1.1`, so the forest retarget is the identity
there, landing `v` in both quotient components `δ_r ≠ δ_f` — against `z.2.1.pairwiseDisjoint`. -/
theorem right_forest_cross (M : ResolvedMultiStarDecontractionSupply D)
    (z : ForestBlockCodType D G)
    {R : ResolvedFeynmanSubgraph G} (hR : R ∈ (rightDomain z).attach.image (rightReembed z))
    {P : ResolvedFeynmanSubgraph G}
    (hP : P ∈ (forestDomain z).attach.image (fun δ => M.parent z δ)) : R.Disjoint P := by
  obtain ⟨δr, -, rfl⟩ := Finset.mem_image.mp hR
  obtain ⟨δf, -, rfl⟩ := Finset.mem_image.mp hP
  show _root_.Disjoint (rightReembed z δr).vertices (M.parent z δf).vertices
  rw [Finset.disjoint_left]
  intro v hvR hvP
  rw [rightReembed_vertices] at hvR
  have hvnotz : v ∉ z.1.1.vertices :=
    starAvoiding_notMem_outer z δr.1 (Finset.mem_filter.mp δr.2).2 hvR
  have hret := localizedParentVertex_retargets z δf.1 (M.legLift z δf) (M.hE z) (M.hL z) hvP
  have hvnottouched : v ∉ (touchedOuterForest z δf.1).vertices :=
    fun hc => hvnotz (touchedOuterForest_vertices_subset z hc)
  rw [ResolvedAdmissibleSubgraph.retargetVertex_of_not_mem _ _ hvnottouched] at hret
  have hne : δr.1 ≠ δf.1 := by
    intro h
    have hrd : Disjoint δr.1.vertices (starOfZ z) := (Finset.mem_filter.mp δr.2).2
    have hfd : ¬ Disjoint δf.1.vertices (starOfZ z) := (Finset.mem_filter.mp δf.2).2
    rw [h] at hrd; exact hfd hrd
  exact Finset.disjoint_left.mp
    (z.2.1.pairwiseDisjoint (Finset.mem_filter.mp δr.2).1 (Finset.mem_filter.mp δf.2).1 hne) hvR hret

/-! ### The three concrete regions. -/

/-- **R-6c-body-338 — the left (untouched residual) region.**  `.elements = leftResidualTouched z`. -/
noncomputable def leftRegion (z : ForestBlockCodType D G) : ResolvedAdmissibleSubgraph G :=
  z.1.1.filterElements (fun A => ¬ representedByTouched z A)

@[simp] theorem leftRegion_elements (z : ForestBlockCodType D G) :
    (leftRegion z).elements = leftResidualTouched z := rfl

/-- **R-6c-body-338 — the right (survivor) region.**  `.elements = image rightReembed` (body-337). -/
noncomputable def rightRegion (z : ForestBlockCodType D G) : ResolvedAdmissibleSubgraph G :=
  ResolvedAdmissibleSubgraph.ofElements ((rightDomain z).attach.image (rightReembed z))
    (fun γ hγ => by
      obtain ⟨δ, -, rfl⟩ := Finset.mem_image.mp hγ
      exact (resolvedConcreteRightRegion D).rightComponentCD z δ)
    (fun _ hγ _ hδ hne => (resolvedConcreteRightRegion D).rightComponentDisjoint z hγ hδ hne)

@[simp] theorem rightRegion_elements (z : ForestBlockCodType D G) :
    (rightRegion z).elements = (rightDomain z).attach.image (rightReembed z) := rfl

/-- **R-6c-body-338 — the forest (de-contracted parent) region** (body-332). -/
noncomputable def forestRegion (M : ResolvedMultiStarDecontractionSupply D)
    (F : ResolvedCanonicalStarFacts D) (z : ForestBlockCodType D G) : ResolvedAdmissibleSubgraph G :=
  M.forestRecoveredMulti F z

@[simp] theorem forestRegion_elements (M : ResolvedMultiStarDecontractionSupply D)
    (F : ResolvedCanonicalStarFacts D) (z : ForestBlockCodType D G) :
    (forestRegion M F z).elements = (forestDomain z).attach.image (fun δ => M.parent z δ) :=
  M.forestRecoveredMulti_elements F z

/-! ### The raw three-region union (choice/carrier-free). -/

/-- **R-6c-body-338 — the raw recovered-outer union** of the three concrete regions, discharged by the three
cross vertex-disjointnesses.  This is the `selectedOuterRawOf` shape WITHOUT the `recovered_raw_mem` carrier
gate (the model obligation, deferred). -/
noncomputable def regionRawUnion (M : ResolvedMultiStarDecontractionSupply D)
    (F : ResolvedCanonicalStarFacts D) (z : ForestBlockCodType D G) : ResolvedAdmissibleSubgraph G :=
  recoveredRawUnion (leftRegion z) (rightRegion z) (forestRegion M F z)
    (fun γ hγ δ hδ _ => left_right_cross z
      (by rwa [leftRegion_elements] at hγ) (by rwa [rightRegion_elements] at hδ))
    (fun γ hγ δ hδ _ => left_forest_cross M F z
      (by rwa [leftRegion_elements] at hγ) (by rwa [forestRegion_elements] at hδ))
    (fun γ hγ δ hδ _ => right_forest_cross M z
      (by rwa [rightRegion_elements] at hγ) (by rwa [forestRegion_elements] at hδ))

/-! ### The three tag exclusivities (cross + `cd_nonempty`). -/

/-- **R-6c-body-338 — right ∉ left.**  A right survivor is not a left-residual component (a graph in both
would be self-disjoint, but `cd_nonempty` makes it vertex-nonempty). -/
theorem right_notMem_left (N : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentNonemptySupply H)
    (z : ForestBlockCodType D G) {γ : ResolvedFeynmanSubgraph G}
    (hr : γ ∈ (rightRegion z).elements) : γ ∉ (leftRegion z).elements := by
  intro hl
  have hdisj : _root_.Disjoint γ.vertices γ.vertices :=
    left_right_cross z (by rwa [leftRegion_elements] at hl) (by rwa [rightRegion_elements] at hr)
  obtain ⟨v, hv⟩ := (N G).cd_nonempty γ ((rightRegion z).isConnectedDivergent γ hr)
  exact Finset.disjoint_left.mp hdisj hv hv

/-- **R-6c-body-338 — forest ∉ left.** -/
theorem forest_notMem_left (N : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentNonemptySupply H)
    (M : ResolvedMultiStarDecontractionSupply D) (F : ResolvedCanonicalStarFacts D)
    (z : ForestBlockCodType D G) {γ : ResolvedFeynmanSubgraph G}
    (hf : γ ∈ (forestRegion M F z).elements) : γ ∉ (leftRegion z).elements := by
  intro hl
  have hdisj : _root_.Disjoint γ.vertices γ.vertices :=
    left_forest_cross M F z (by rwa [leftRegion_elements] at hl) (by rwa [forestRegion_elements] at hf)
  obtain ⟨v, hv⟩ := (N G).cd_nonempty γ ((forestRegion M F z).isConnectedDivergent γ hf)
  exact Finset.disjoint_left.mp hdisj hv hv

/-- **R-6c-body-338 — forest ∉ right.** -/
theorem forest_notMem_right (N : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentNonemptySupply H)
    (M : ResolvedMultiStarDecontractionSupply D) (F : ResolvedCanonicalStarFacts D)
    (z : ForestBlockCodType D G) {γ : ResolvedFeynmanSubgraph G}
    (hf : γ ∈ (forestRegion M F z).elements) : γ ∉ (rightRegion z).elements := by
  intro hr
  have hdisj : _root_.Disjoint γ.vertices γ.vertices :=
    right_forest_cross M z (by rwa [rightRegion_elements] at hr) (by rwa [forestRegion_elements] at hf)
  obtain ⟨v, hv⟩ := (N G).cd_nonempty γ ((forestRegion M F z).isConnectedDivergent γ hf)
  exact Finset.disjoint_left.mp hdisj hv hv

end GaugeGeometry.QFT.Combinatorial
