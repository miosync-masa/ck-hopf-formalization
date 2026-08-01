import GaugeGeometry.QFT.HopfAlgebra.Phi4StableForestBlockForwardInverse

/-!
# QFT-R1-body-647a — the STABLE forward-native FOREST parent RAW recovery (left inverse, part a)

Body-646 closed the STABLE forest-block RIGHT inverse (`forward ∘ inverse = id`).  The LEFT inverse
`stableRecoveredSplitChoice (stableForestBlockForward s) = s` is split per the OLD body-622 shape.  This body
(647a) fixes ONLY the FOREST parent OWNER raw recovery: for a source occurrence `o` of a stable mixed split
choice `s`, the inverse decontraction of the forward package's remnant component `stableRemnantComponent o`
recovers `o.γ.1` EXACTLY, as a RAW `ResolvedFeynmanSubgraph G` (SAME ambient `G`, no relabeling).  It MIRRORS
the OLD body-622a proof shape on the STABLE carrier; the OLD 622a terms are NEVER consumed (mirror only).

## Steps
* **Step 0 (star-touching)** — `stableRemnant_star_touching`: the remnant component of the forward package is a
  FOREST image of `z := stableForestBlockForward s` (`phi4WTriplePrime_inv_isForestImage`).  Freshly proved by
  the designated star witness `remnantTau (localStar δ₀)`, which lies in the remnant's vertex set and, via
  `stableRemnantTau_map`, IS the global `stableSelectedOuter` star of the promoted inner component (a
  `stableSelectedOuter`-element).  `z.1.1 = stableSelectedOuter s.1` defeq.  NO strict star equality.
* **Step 1 (helper)** — `stableInternalEdges_eq_filter_of_edgeComplete`: an internal-edge-complete component's
  internal edges ARE the ambient's induced filter (`le_antisymm` of `internalEdges_le`+`edges_supported` vs.
  edge-completeness).  Mirror of old 622a's filter helper — NOT consumed as a term.
* **Step 2 (vertex bridge, HEADLINE core)** — `stableForwardForest_recoveredParent_vertices`: the recovered
  parent's region equals `o.γ.1.vertices`.  Composes body-609's inverse `inv_retarget_mem_delta_iff` (region ⇔
  `A`-retarget in `δ`) with body-635's forward `stableRemnant_phi_mem_Ltau_iff` (`A`-retarget in the remnant ⇔
  in `o.γ`); the two share the IDENTICAL retarget LHS (`z.1.1 = stableSelectedOuter s.1` defeq).  `Finset.ext`
  over both sides' `⊆ G.vertices`.  NO `τ` value / NO star equality read — same ambient `G`.
* **Step 3 (HEADLINE)** — `stableForwardForest_recoveredParent_eq`: the recovered parent equals `o.γ.1` as a
  raw `ResolvedFeynmanSubgraph G` (`ext`: vertices from Step 2; internal edges from Step 1 + `o.γ.1`'s outer W‴
  edge-completeness; external legs from `o.γ.1`'s outer W‴ saturation).  All induced-filter identities on the
  SAME vertex set in the SAME ambient `G`.  Mirror of old 622a's HEADLINE.

## Ownership boundary — MUST NOT consume as terms
The OLD 622a `phi4WTriplePrime_internalEdges_eq_filter_of_edgeComplete` / `_forwardForest_recoveredParent_verts_eq`
/ `_forwardForest_recoveredParent_eq` are NEVER consumed (proof shape mirrored only).  Reused AS STATED: body-640
forward package (`stableForestBlockForward` / `_fst`), body-639b remnant membership
(`stableRemnantComponent_mem_quotientForest`), body-635 remnant carrier + `stableRemnant_phi_mem_Ltau_iff` +
`stableRemnant_gamma_saturated` + `stableRemnantTau_map` + `stableRemnant_promoted_mem`, body-608 inverse
sectors (`phi4WTriplePrime_inv_isForestImage` / `_forestDecontractionInput_of_starTouching`), body-609 inverse
recovered parent (`phi4WTriplePrime_inv_recoveredParent{,_verts,_vertices,_internalEdges,_externalLegs}` +
`_retarget_mem_delta_iff`).

## Left-inverse roadmap (per old body-622)
* **647a (this body)** — FOREST parent OWNER raw recovery `recoveredParent = o.γ.1` (RAW subgraph, SAME `G`).
* **647b** — the recovered INNER forest / the FOREST `choice = Sum.inr o.B` value equation (the cross-ambient
  `boundaryCompletedResolvedGraph` transport that old 622a deferred to 622b).
* **647c** — the FOREST `recoveredOuter` / `recoveredChoice` funext assembling the outer coordinate.
* **648** — the RIGHT / survivor coordinate of the left inverse.
* **649** — the FULL left inverse `stableRecoveredSplitChoice (stableForestBlockForward s) = s`.

## HALT / red lines
NO entry into the recovered INNER forest; NO `stableRecoveredChoice … = Sum.inr o.B`; NO recoveredOuter equality
/ choice funext / full left inverse (those are 647b/c/648/649).  NO `subst` between FIXED owners; NO
cross-ambient subgraph `Eq` beyond the SAME-`G` HEADLINE; ZERO public `HEq` / `cast` / graph-data transport `▸`
(Prop-membership `▸` OK — none used).  NO `τ` value / star equality / recontraction re-expansion.  NO
`Bijective` / bare `Equiv` / `sum_bij` / alpha / coassoc.  ZERO old-622a term consume (mirror only).  ZERO new
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
noncomputable local instance instPhi4DivergenceMeasureFamily647a :
    (H : FeynmanGraph) → DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

variable {hSt : StableResolvedBoundaryIds G}

/-! ## Step 0 — the remnant is star-touching in the forward codomain -/

/-- **body-647a (Step 0) — the forward package's remnant component is a FOREST image.**  Fresh mirror of old
607's `phi4WTriplePrime_remnant_star_touching` on the STABLE carrier: the designated star witness
`stableRemnantTau o (localStar δ₀)` for a chosen inner component `δ₀ ∈ o.B.1.elements` lands in the remnant's
vertex set (its local star is a `stableLocalContractGraph` star vertex, then mapped by `remnantTau`) and, via
`stableRemnantTau_map`, IS the global `stableSelectedOuter` star of the promoted `stableRootRelativeInner o.γ.1
δ₀` (a `stableSelectedOuter`-element).  `(stableForestBlockForward s).1.1 = stableSelectedOuter s.1` defeq.
Designated-star witness — NO strict star equality. -/
theorem stableRemnant_star_touching (s : StablePhi4MixedSplitChoice G hSt)
    (o : StableForestChoiceOccurrence s) :
    phi4WTriplePrime_inv_isForestImage (stableForestBlockForward s)
      ⟨stableRemnantComponent o, stableRemnantComponent_mem_quotientForest s o⟩ := by
  obtain ⟨δ₀, hδ₀⟩ := (stableForestOcc_B_isProperForest o).1
  refine ⟨stableRemnantTau o
      (phi4WTriplePrimeCanonicalSupply.starOf
        (stableLocalBoundaryCompletedGraph o.γ.1) o.B.1 δ₀), ?_, ?_⟩
  · rw [stableRemnantComponent_vertices]
    apply Finset.mem_image.mpr
    refine ⟨phi4WTriplePrimeCanonicalSupply.starOf
        (stableLocalBoundaryCompletedGraph o.γ.1) o.B.1 δ₀, ?_, rfl⟩
    rw [stableLocalContractGraph, ResolvedAdmissibleSubgraph.contractWithStars_vertices]
    exact Finset.mem_union_right _
      (ResolvedAdmissibleSubgraph.mem_starVertices.mpr ⟨δ₀, hδ₀, rfl⟩)
  · rw [stableRemnantTau_map o ⟨δ₀, hδ₀⟩]
    exact ResolvedAdmissibleSubgraph.mem_starVertices.mpr
      ⟨stableRootRelativeInner o.γ.1 δ₀, stableRemnant_promoted_mem o hδ₀, rfl⟩

/-! ## Step 1 — an internal-edge-complete component's internal edges ARE the ambient induced filter -/

/-- **body-647a (Step 1) — internal edges of an internal-edge-complete component are the induced filter.**  The
forward `≤` is `internalEdges_le` + `edges_supported`; the reverse `≤` is edge-completeness itself.  Mirror of
old 622a's `phi4WTriplePrime_internalEdges_eq_filter_of_edgeComplete` — NOT consumed as a term. -/
theorem stableInternalEdges_eq_filter_of_edgeComplete
    (γ : ResolvedFeynmanSubgraph G) (hEC : ResolvedInternalEdgeComplete γ) :
    γ.internalEdges
      = G.internalEdges.filter (fun e => e.source ∈ γ.vertices ∧ e.target ∈ γ.vertices) :=
  le_antisymm
    (Multiset.le_filter.mpr ⟨γ.internalEdges_le, fun e he => γ.edges_supported e he⟩)
    hEC

/-! ## Step 2 — the forward-native recovered-parent vertex bridge -/

/-- **body-647a (Step 2, vertex bridge) — the recovered-parent region of the remnant `δ = stableRemnantComponent
o` is `o.γ.1`'s vertex set.**  For `z := stableForestBlockForward s`, `z.1.1` is definitionally `stableSelectedOuter
s.1`, so body-609's region membership iff (`phi4WTriplePrime_inv_retarget_mem_delta_iff`) and body-635's remnant
membership iff (`stableRemnant_phi_mem_Ltau_iff`) share the same `A`-retarget LHS: a `G`-vertex lies in the
recovered-parent region iff its retarget lands in the remnant iff it lies in `o.γ`.  Both regions sit inside
`G.vertices`, so the membership iff on `G.vertices` upgrades to a `Finset` equality.  NO `τ` value read. -/
theorem stableForwardForest_recoveredParent_vertices (s : StablePhi4MixedSplitChoice G hSt)
    (o : StableForestChoiceOccurrence s) :
    phi4WTriplePrime_inv_recoveredParent_verts (stableForestBlockForward s)
        ⟨stableRemnantComponent o, stableRemnantComponent_mem_quotientForest s o⟩
      = o.γ.1.vertices := by
  have I := phi4WTriplePrime_forestDecontractionInput_of_starTouching
    (stableForestBlockForward s) (stableRemnant_star_touching s o)
  apply Finset.ext
  intro v
  constructor
  · intro hv
    have hvG : v ∈ G.vertices :=
      phi4WTriplePrime_inv_recoveredParent_verts_subset _ _ hv
    exact (stableRemnant_phi_mem_Ltau_iff o hvG).mp
      ((phi4WTriplePrime_inv_retarget_mem_delta_iff I hvG).mpr hv)
  · intro hv
    have hvG : v ∈ G.vertices := o.γ.1.vertices_subset hv
    exact (phi4WTriplePrime_inv_retarget_mem_delta_iff I hvG).mp
      ((stableRemnant_phi_mem_Ltau_iff o hvG).mpr hv)

/-! ## Step 3 — the forward-native recovered-parent identification (raw `G`-subgraph equality) -/

/-- **body-647a (Step 3, HEADLINE) — the inverse decontraction of `stableRemnantComponent o` recovers `o.γ.1`
EXACTLY.**  A raw `ResolvedFeynmanSubgraph G` equality (SAME ambient `G`, no relabeling): the vertices are Step
2's bridge, and because both the recovered parent (induced) and `o.γ.1` (outer W‴ edge-complete + saturated)
present their internal edges / external legs as the SAME `G`-induced filter on the SAME vertex set, all three
carrier fields coincide.  This is the FOREST forward-native OWNER core of the STABLE left inverse — closed from
635/609 alone, with NO correcting permutation `τ` value and NO cross-ambient transport. -/
theorem stableForwardForest_recoveredParent_eq (s : StablePhi4MixedSplitChoice G hSt)
    (o : StableForestChoiceOccurrence s) :
    phi4WTriplePrime_inv_recoveredParent
        (phi4WTriplePrime_forestDecontractionInput_of_starTouching
          (stableForestBlockForward s)
          (δ := ⟨stableRemnantComponent o,
            stableRemnantComponent_mem_quotientForest s o⟩)
          (stableRemnant_star_touching s o))
      = o.γ.1 := by
  have hV := stableForwardForest_recoveredParent_vertices s o
  have hSat : ResolvedExternalLegSaturated G o.γ.1 := stableRemnant_gamma_saturated o
  have hEC : ResolvedInternalEdgeComplete o.γ.1 :=
    (((mem_phi4WTriplePrimeIndex G s.1.outer).mp s.1.outer_mem).2.2.2.2.2.2) o.γ.1 o.γ.2
  apply ResolvedFeynmanSubgraph.ext
  · rw [phi4WTriplePrime_inv_recoveredParent_vertices]
    exact hV
  · rw [phi4WTriplePrime_inv_recoveredParent_internalEdges, hV]
    exact (stableInternalEdges_eq_filter_of_edgeComplete o.γ.1 hEC).symm
  · rw [phi4WTriplePrime_inv_recoveredParent_externalLegs, hV]
    exact (externalLegs_eq_filter_of_saturated o.γ.1 hSat).symm

end GaugeGeometry.QFT.Combinatorial
