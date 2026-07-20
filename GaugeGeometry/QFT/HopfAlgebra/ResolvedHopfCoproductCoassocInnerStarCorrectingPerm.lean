import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocResolvedStarRenamePerm
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocHardcodedStarSwap

/-!
# R-6c-body-450 — the inner cross-ambient correcting permutation (PROVED)

Four-hundred-and-fiftieth genuine-body step — instantiating the body-449 engine for the inner socket.  Both star maps
already live on the SAME `innerRaw.elements` (body-350/351), so the correcting permutation `ρ` is exactly a body-449
`resolvedStarRenamePerm` between the hardcoded parent star `D.starOf parent innerRaw` and the touched outer star
`touchedInnerStarTotal`.  `ρ` fixes only the PARENT ambient's vertices — never a global `G` survivor.

* `touchedInnerStar_fresh` — the touched star avoids the parent's vertices (its value is the OUTER star of the source
  component, fresh w.r.t. `G ⊇ parent.vertices`);
* `touchedInnerStar_injOn` — the touched star is injective on `innerRaw.elements` (`starOf_injective` + `innerSource_spec`);
* `innerStarCorrectingPerm` — `ρ` via the body-449 engine, orientation `ρ (hardcodedStar B) = touchedInnerStarTotal B`;
* `innerStarCorrectingPerm_on_parent_vertices` / `_on_inner_stars` — projections of the body-449 laws.

Per the HALT/guards: `innerSource` is reused (not re-implemented); `innerStar_agrees_raw` / strict `StarProm` are NOT
used; `ρ` fixes only the parent vertices; no graph equality / round-trip / `Concrete` wiring (body-451+); body-445 stays
a valid conditional.  NOT the unconditional theorem.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO
`promote_collapse` / singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}
  (Fstar : ResolvedCanonicalStarFacts D) (M : ResolvedMultiStarDecontractionSupply D)
  (z : ForestBlockCodType D G)
  (δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) // x ∈ forestDomain z})

include Fstar

/-- **R-6c-body-450 — the touched inner star avoids the parent's vertices.** -/
theorem touchedInnerStar_fresh {B : ResolvedFeynmanSubgraph (M.parent z δ).toResolvedFeynmanGraph}
    (hB : B ∈ (innerRaw z δ.1 (M.legLift z δ) (M.hE z) (M.hL z)).elements) :
    touchedInnerStarTotal z δ.1 (M.legLift z δ) (M.hE z) (M.hL z) B
      ∉ (M.parent z δ).toResolvedFeynmanGraph.vertices := by
  rw [touchedInnerStarTotal_of_mem z δ.1 (M.legLift z δ) (M.hE z) (M.hL z) B hB, touchedInnerStar]
  intro hmem
  have hmemG : D.starOf G z.1.1 (innerSource z δ.1 (M.legLift z δ) (M.hE z) (M.hL z) ⟨B, hB⟩).1
      ∈ G.vertices := (M.parent z δ).vertices_subset hmem
  exact Fstar.starOf_fresh G z.1.1 (innerSource z δ.1 (M.legLift z δ) (M.hE z) (M.hL z) ⟨B, hB⟩).1
    (mem_touchedOuterComponents.mp (innerSource z δ.1 (M.legLift z δ) (M.hE z) (M.hL z) ⟨B, hB⟩).2).1 hmemG

/-- **R-6c-body-450 — the touched inner star is injective on the inner forest.** -/
theorem touchedInnerStar_injOn
    {B₁ : ResolvedFeynmanSubgraph (M.parent z δ).toResolvedFeynmanGraph}
    (hB₁ : B₁ ∈ (innerRaw z δ.1 (M.legLift z δ) (M.hE z) (M.hL z)).elements)
    {B₂ : ResolvedFeynmanSubgraph (M.parent z δ).toResolvedFeynmanGraph}
    (hB₂ : B₂ ∈ (innerRaw z δ.1 (M.legLift z δ) (M.hE z) (M.hL z)).elements)
    (heq : touchedInnerStarTotal z δ.1 (M.legLift z δ) (M.hE z) (M.hL z) B₁
      = touchedInnerStarTotal z δ.1 (M.legLift z δ) (M.hE z) (M.hL z) B₂) : B₁ = B₂ := by
  rw [touchedInnerStarTotal_of_mem z δ.1 (M.legLift z δ) (M.hE z) (M.hL z) B₁ hB₁, touchedInnerStar,
    touchedInnerStarTotal_of_mem z δ.1 (M.legLift z δ) (M.hE z) (M.hL z) B₂ hB₂, touchedInnerStar] at heq
  set src₁ := innerSource z δ.1 (M.legLift z δ) (M.hE z) (M.hL z) ⟨B₁, hB₁⟩ with hs₁
  set src₂ := innerSource z δ.1 (M.legLift z δ) (M.hE z) (M.hL z) ⟨B₂, hB₂⟩ with hs₂
  have hsrc : src₁ = src₂ :=
    Subtype.ext (Fstar.starOf_injective G z.1.1 (η := src₁.1) (δ := src₂.1)
      (mem_touchedOuterComponents.mp src₁.2).1 (mem_touchedOuterComponents.mp src₂.2).1 heq)
  have h1 := innerSource_spec z δ.1 (M.legLift z δ) (M.hE z) (M.hL z) ⟨B₁, hB₁⟩
  have h2 := innerSource_spec z δ.1 (M.legLift z δ) (M.hE z) (M.hL z) ⟨B₂, hB₂⟩
  rw [← hs₁] at h1
  rw [← hs₂] at h2
  rw [hsrc] at h1
  exact h1.symm.trans h2

/-- **R-6c-body-450 — the hardcoded parent star is injective on the inner forest.** -/
theorem hardcodedInnerStar_injOn :
    ∀ γ₁ ∈ (innerRaw z δ.1 (M.legLift z δ) (M.hE z) (M.hL z)).elements,
    ∀ γ₂ ∈ (innerRaw z δ.1 (M.legLift z δ) (M.hE z) (M.hL z)).elements,
      D.starOf (M.parent z δ).toResolvedFeynmanGraph
          (innerRaw z δ.1 (M.legLift z δ) (M.hE z) (M.hL z)) γ₁
        = D.starOf (M.parent z δ).toResolvedFeynmanGraph
          (innerRaw z δ.1 (M.legLift z δ) (M.hE z) (M.hL z)) γ₂ → γ₁ = γ₂ :=
  fun _ h₁ _ h₂ heq => Fstar.starOf_injective (M.parent z δ).toResolvedFeynmanGraph
    (innerRaw z δ.1 (M.legLift z δ) (M.hE z) (M.hL z)) h₁ h₂ heq

/-- **R-6c-body-450 ∎ — the inner cross-ambient correcting permutation.**  Orientation `ρ (hardcodedStar B) =
touchedInnerStarTotal B`; fixing domain = the parent's vertices only. -/
noncomputable def innerStarCorrectingPerm : Equiv.Perm VertexId :=
  resolvedStarRenamePerm (innerRaw z δ.1 (M.legLift z δ) (M.hE z) (M.hL z))
    (D.starOf (M.parent z δ).toResolvedFeynmanGraph (innerRaw z δ.1 (M.legLift z δ) (M.hE z) (M.hL z)))
    (touchedInnerStarTotal z δ.1 (M.legLift z δ) (M.hE z) (M.hL z))
    (hardcodedInnerStar_injOn Fstar M z δ)
    (fun _ h₁ _ h₂ heq => touchedInnerStar_injOn Fstar M z δ h₁ h₂ heq)

/-- **R-6c-body-450 — `ρ` fixes the parent's vertices** (LOCAL, never a global `G` survivor). -/
theorem innerStarCorrectingPerm_on_parent_vertices {v : VertexId}
    (hvH : v ∈ (M.parent z δ).toResolvedFeynmanGraph.vertices) :
    innerStarCorrectingPerm Fstar M z δ v = v :=
  resolvedStarRenamePerm_on_ambient _ _ _ _ _
    (fun γ hγ => Fstar.starOf_fresh (M.parent z δ).toResolvedFeynmanGraph
      (innerRaw z δ.1 (M.legLift z δ) (M.hE z) (M.hL z)) γ hγ)
    (fun _ hγ => touchedInnerStar_fresh Fstar M z δ hγ) hvH

/-- **R-6c-body-450 — `ρ` sends each hardcoded star to the touched star.** -/
theorem innerStarCorrectingPerm_on_inner_stars
    {γ : ResolvedFeynmanSubgraph (M.parent z δ).toResolvedFeynmanGraph}
    (hγ : γ ∈ (innerRaw z δ.1 (M.legLift z δ) (M.hE z) (M.hL z)).elements) :
    innerStarCorrectingPerm Fstar M z δ
        (D.starOf (M.parent z δ).toResolvedFeynmanGraph
          (innerRaw z δ.1 (M.legLift z δ) (M.hE z) (M.hL z)) γ)
      = touchedInnerStarTotal z δ.1 (M.legLift z δ) (M.hE z) (M.hL z) γ :=
  resolvedStarRenamePerm_on_stars _ _ _ _ _ hγ

end GaugeGeometry.QFT.Combinatorial
