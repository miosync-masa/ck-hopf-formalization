import GaugeGeometry.QFT.HopfAlgebra.Phi4StableForestBlockInverseForwardParent

/-!
# QFT-R1-body-647b-1 — the STABLE forward-native INNER FOREST raw element recovery (left inverse, part b-1)

Body-647a recovered the FOREST parent OWNER (`recoveredParent = o.γ.1`).  The LEFT inverse continues; body-647b
is split into **647b-1 (this)** — the AMBIENT-FREE COMBINATORIAL core — and **647b-2 (later)** — the typed
aligned inner forest + `choice = Sum.inr o.B`.

This body proves ONLY the raw `Finset (ResolvedFeynmanSubgraph G)` image equality: the elements of the touched
outer forest of `stableForestBlockForward s` at the remnant component `stableRemnantComponent o` are EXACTLY the
root-lifts `stableRootRelativeInner o.γ.1` of the inner forest `o.B.1`'s elements.  NO aligned
component/forest construction, NO `Sum.inr`, NO dependent transport, NO cross-ambient `Eq`.  Both sides are raw
`Finset (ResolvedFeynmanSubgraph G)` — fully ambient-free.

## Steps
* **Step 1 (vertex presentation anchors, rfl/defeq)** — `stableForwardForest_remnantComponent_vertices_image`
  (`(stableRemnantComponent o).vertices = (stableLocalContractGraph o).vertices.image (stableRemnantTau o)`, the
  `ResolvedFeynmanGraph.mapPerm` vertex form) and `stableForwardForest_localContract_vertices` (the
  `contractWithStars_vertices` union `(SLBCG γ).vertices \ B.vertices ∪ B.starVertices (localStar)`).  NO new
  graph construction.
* **Steps 2+3 (HEADLINE)** — `stableForwardForest_touchedOuterForest_eq`, closed by `Finset.ext`:
  - **Step 2 (reverse, touched ⊆ image)** — for `γ ∈ stableSelectedOuter s.1` whose canonical star lands in the
    remnant, the star is `stableRemnantTau o x` for `x ∈ stableLocalContractGraph o` vertices.  Classify `x`:
    * SURVIVOR (`x ∈ (SLBCG γ).vertices \ B.vertices`) — `stableRemnantTau_fix` pins the star `= x ∈ o.γ.1.vertices
      ⊆ G.vertices`, yet the canonical `stableSelectedOuter` star is FRESH (`stableRemnant_gen_star_not_mem`,
      `∉ G.vertices`).  CONTRADICTION.
    * LOCAL-STAR (`x = localStar δᵢ`, `δᵢ ∈ B.elements`) — `stableRemnantTau_map` gives the star `= starOf G
      (stableSelectedOuter s.1) (stableRootRelativeInner o.γ.1 δᵢ)`; canonical `stableSelectedOuter` star
      injectivity (`stableRemnant_gen_star_injOn`, both elements via `stableRemnant_promoted_mem`) forces `γ =
      stableRootRelativeInner o.γ.1 δᵢ ∈ image`.
  - **Step 3 (forward, image ⊆ touched)** — for `δᵢ ∈ B.elements`, `stableRootRelativeInner o.γ.1 δᵢ` is a
    `stableSelectedOuter` element (`stableRemnant_promoted_mem`) whose canonical star `= stableRemnantTau o
    (localStar δᵢ)` (`stableRemnantTau_map`) lies in the remnant's mapPerm vertices (the local star is a
    `contractWithStars` star vertex, mapped by `stableRemnantTau`).  So it passes the touched filter.
* **Step 4 (multiplicity anchor)** — `stableForwardForest_touchedOuterForest_card_eq`: the HEADLINE +
  `Finset.card_image_of_injOn` (`stableRootRelativeInner_injOn_elements`, `B`'s nonempty components) — NO term
  lost to dedup.

## Ownership boundary — MUST NOT consume as terms
Reused AS STATED: body-608 `phi4WTriplePrime_touchedOuterForest{,_elements}`; body-640 forward package
(`stableForestBlockForward{,_fst}`); body-639b `stableRemnantComponent_mem_quotientForest`; body-635
`stableRemnantComponent{,_vertices}` / `stableLocalContractGraph` / `stableRemnantTau_fix` / `stableRemnantTau_map`
/ `stableRemnant_gen_star_not_mem` / `stableRemnant_gen_star_injOn` / `stableRemnant_promoted_mem` /
`stableForestOcc_B_isProperForest` / `stableSelectedOuter_isProperForest` / `stableLocalBoundaryCompletedGraph_vertices`;
body-632 `stableSelectedOuter` / `stableRootRelativeInner{,_injOn_elements}`; core `contractWithStars_vertices` /
`mem_starVertices` / `Finset.card_image_of_injOn`.  The OLD 622b terms are NEVER consumed (mirror shape only).

## HALT / red lines
NO aligned inner component/forest construction; NO `stableRecoveredChoice … = Sum.inr o.B`; NO recovered-parent
dependent transport; NO recoveredOuter equality / choice funext / left inverse (those are 647b-2/647c).  ZERO
public OR private `HEq` / `cast` / graph-data transport `▸` (Prop-membership `▸` OK).  NO fabricated homogeneous
`Eq` between the parent ambient and `o.γ.1` ambient.  NO global `τ` / orbit quotient / dedup.  NO
`Bijective` / bare `Equiv` / `sum_bij` / alpha / coassoc.  ZERO old-622b term consume.  ZERO new
`structure` / `class` / permanent `instance` (one file-local `local instance`).  ZERO forbidden divergence class
in any declaration TYPE.  ZERO `sorry` / `admit` / `native_decide`.  Axiom-clean (`propext`, `Classical.choice`,
`Quot.sound`).
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

open ResolvedFeynmanSubgraph

variable {G : ResolvedFeynmanGraph}

set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-- The concrete φ⁴ divergence measure family, registered file-locally (providable instance, NO forbidden
class). -/
noncomputable local instance instPhi4DivergenceMeasureFamily647b1 :
    (H : FeynmanGraph) → DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

variable {hSt : StableResolvedBoundaryIds G}

/-! ## Step 1 — vertex presentation anchors (defeq / rfl) -/

/-- **body-647b-1 (Step 1) — the remnant component's vertices are the `mapPerm` image of the local
contraction's vertices** (definitional `ResolvedFeynmanGraph.mapPerm` vertex form).  Thin anchor — NO new
construction. -/
theorem stableForwardForest_remnantComponent_vertices_image
    {s : StablePhi4MixedSplitChoice G hSt} (o : StableForestChoiceOccurrence s) :
    (stableRemnantComponent o).vertices
      = (stableLocalContractGraph o).vertices.image (stableRemnantTau o) :=
  rfl

/-- **body-647b-1 (Step 1) — the local contraction's vertices as a `contractWithStars` union.**  Thin anchor —
NO new construction. -/
theorem stableForwardForest_localContract_vertices
    {s : StablePhi4MixedSplitChoice G hSt} (o : StableForestChoiceOccurrence s) :
    (stableLocalContractGraph o).vertices
      = ((stableLocalBoundaryCompletedGraph o.γ.1).vertices \ o.B.1.vertices)
        ∪ o.B.1.starVertices
            (phi4WTriplePrimeCanonicalSupply.starOf
              (stableLocalBoundaryCompletedGraph o.γ.1) o.B.1) := by
  rw [stableLocalContractGraph, ResolvedAdmissibleSubgraph.contractWithStars_vertices]

/-! ## Steps 2+3 — the ambient-free touched-forest exact image equality (HEADLINE) -/

/-- **body-647b-1 (Steps 2+3, HEADLINE) — the touched outer forest's elements ARE the root-lifts of `o.B.1`.**
For `z := stableForestBlockForward s` (so `z.1.1 = stableSelectedOuter s.1` defeq and the touched vertex set is
`stableRemnantComponent o`), the outer components whose canonical star lands in the remnant are EXACTLY the
promoted inner components `stableRootRelativeInner o.γ.1 δᵢ`, `δᵢ ∈ o.B.1.elements`.  A raw
`Finset (ResolvedFeynmanSubgraph G)` equality — fully ambient-free (both sides live over the SAME `G`), with NO
`τ` value read, NO aligned inner forest, and NO cross-ambient transport. -/
theorem stableForwardForest_touchedOuterForest_eq
    (s : StablePhi4MixedSplitChoice G hSt) (o : StableForestChoiceOccurrence s) :
    (phi4WTriplePrime_touchedOuterForest (stableForestBlockForward s)
        ⟨stableRemnantComponent o, stableRemnantComponent_mem_quotientForest s o⟩).elements
      = o.B.1.elements.image (stableRootRelativeInner o.γ.1) := by
  rw [phi4WTriplePrime_touchedOuterForest_elements]
  apply Finset.ext
  intro γ
  constructor
  · -- Step 2 (reverse): touched ⊆ image
    intro hγ
    rw [Finset.mem_filter] at hγ
    obtain ⟨hγelt, hγstar⟩ := hγ
    have hγelt' : γ ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G
        (stableSelectedOuter s.1) := hγelt
    have hstarV : phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1) γ
        ∈ ((stableLocalContractGraph o).mapPerm (stableRemnantTau o)).vertices := hγstar
    obtain ⟨x, hx, hxeq⟩ := Finset.mem_image.mp hstarV
    rw [stableLocalContractGraph, ResolvedAdmissibleSubgraph.contractWithStars_vertices,
      Finset.mem_union] at hx
    rcases hx with hxsurv | hxstar
    · -- SURVIVOR branch: the star would be an ambient vertex, but it is FRESH → contradiction
      rw [Finset.mem_sdiff, stableLocalBoundaryCompletedGraph_vertices] at hxsurv
      rw [stableRemnantTau_fix o (Finset.mem_sdiff.mpr hxsurv)] at hxeq
      exact absurd (hxeq ▸ o.γ.1.vertices_subset hxsurv.1)
        (stableRemnant_gen_star_not_mem (stableSelectedOuter s.1)
          (stableSelectedOuter_isProperForest s.1) hγelt')
    · -- LOCAL-STAR branch: recover `γ` via `stableSelectedOuter` canonical-star injectivity
      rw [ResolvedAdmissibleSubgraph.mem_starVertices] at hxstar
      obtain ⟨δᵢ, hδᵢ, hδᵢeq⟩ := hxstar
      rw [← hδᵢeq, stableRemnantTau_map o ⟨δᵢ, hδᵢ⟩] at hxeq
      have hγeq : γ = stableRootRelativeInner o.γ.1 δᵢ :=
        stableRemnant_gen_star_injOn (stableSelectedOuter s.1)
          (stableSelectedOuter_isProperForest s.1) hγelt'
          (stableRemnant_promoted_mem o hδᵢ) hxeq.symm
      rw [hγeq]
      exact Finset.mem_image.mpr ⟨δᵢ, hδᵢ, rfl⟩
  · -- Step 3 (forward): image ⊆ touched
    intro hγ
    obtain ⟨δᵢ, hδᵢ, rfl⟩ := Finset.mem_image.mp hγ
    refine Finset.mem_filter.mpr ⟨stableRemnant_promoted_mem o hδᵢ, ?_⟩
    have hlocal : phi4WTriplePrimeCanonicalSupply.starOf
        (stableLocalBoundaryCompletedGraph o.γ.1) o.B.1 δᵢ
        ∈ (stableLocalContractGraph o).vertices := by
      rw [stableLocalContractGraph, ResolvedAdmissibleSubgraph.contractWithStars_vertices]
      exact Finset.mem_union_right _
        (ResolvedAdmissibleSubgraph.mem_starVertices.mpr ⟨δᵢ, hδᵢ, rfl⟩)
    show phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1)
        (stableRootRelativeInner o.γ.1 δᵢ)
        ∈ ((stableLocalContractGraph o).mapPerm (stableRemnantTau o)).vertices
    rw [← stableRemnantTau_map o ⟨δᵢ, hδᵢ⟩]
    exact Finset.mem_image.mpr ⟨_, hlocal, rfl⟩

/-! ## Step 4 — the multiplicity anchor -/

/-- **body-647b-1 (Step 4) — the touched outer forest has EXACTLY `o.B.1.elements.card` elements.**  The
HEADLINE presents the elements as an image of `stableRootRelativeInner o.γ.1`, injective on `o.B.1.elements`
(nonempty components), so NO term is lost to `Finset.image` dedup. -/
theorem stableForwardForest_touchedOuterForest_card_eq
    (s : StablePhi4MixedSplitChoice G hSt) (o : StableForestChoiceOccurrence s) :
    (phi4WTriplePrime_touchedOuterForest (stableForestBlockForward s)
        ⟨stableRemnantComponent o, stableRemnantComponent_mem_quotientForest s o⟩).elements.card
      = o.B.1.elements.card := by
  rw [stableForwardForest_touchedOuterForest_eq s o]
  exact Finset.card_image_of_injOn
    (stableRootRelativeInner_injOn_elements o.γ.1 o.B.1
      (stableForestOcc_B_isProperForest o).2.1)

end GaugeGeometry.QFT.Combinatorial
