import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaSaturationAlgebra
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocConcreteRightRegion
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRepresentedByTouched
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocMultiStarDecontraction

/-!
# R-6c-body-535 — recovered-union external-leg saturation audit (left FREE, right DERIVED, forest normalized)

Five-hundred-and-thirty-fifth genuine-body step — the region-by-region audit of external-leg saturation for the `W″`
recovered raw union `recoveredRawUnion` (body-269).  The intrinsic predicates
(`ResolvedExternalLegSaturated` / `ResolvedForestExternalLegSaturated`, body-532) and the closure algebra
(`resolvedForestExternalLegSaturated_union`, body-534 Step 1) are reused verbatim; nothing here is derived from a target
membership, no `W″` `LegModel` supply is applied to any target parent, `parentCD` is never touched, and no saturation
failure is re-labelled as a physics law.

## The three regions

* **Left residual (FREE).**  `leftResidualTouched z = z.1.1.elements.filter (¬ representedByTouched z ·)` is a
  sub-filter of the input outer's components, so `leftResidualTouched_forestExternalLegSaturated` reads the saturation off
  the supplied input-outer saturation `hOuter : ResolvedForestExternalLegSaturated z.1.1` component-by-component — a pure
  `Finset.mem_filter` projection.

* **Right recovered (DERIVED — the crux).**  A star-avoiding survivor `δ ∈ rightDomain z` re-embeds straight back to `G`
  (`rightReembed`, body-337) with the SAME vertices/legs.  `rightReembed_externalLegSaturated` transports the quotient
  component's saturation `hsrc : ResolvedExternalLegSaturated (z.1.1.contractWithStars …) δ.1` across the contraction.
  The genuine work is the filter EQUALITY
  `(contracted).externalLegs.filter (attachedTo ∈ δ.1.vertices) = G.externalLegs.filter (attachedTo ∈ δ.1.vertices)`:
  `contracted.externalLegs = G.externalLegs.map (retargetExternalLeg)`, the retarget is the identity on a star-avoiding
  `δ`'s carrier (an on-`A` leg retargets to a star ∉ δ.1.vertices; an off-`A` leg is fixed), so `map`/`filter` commute to
  the identity on the filtered submultiset (`Multiset.filter_map` + `Multiset.filter_congr` + `Multiset.map_congr`).  A
  multiplicity-safe equality — no membership-only shortcut.

* **Forest parent (NORMALIZED to the exact residual).**  `M.parent z δ`'s external legs are exactly the datum preimage
  `(M.legLift z δ).legs`, so `localizedParent_externalLegSaturated_target_shape` records (by `Iff.rfl`) that the target
  `ResolvedExternalLegSaturated G (M.parent z δ)` is DEFEQ to
  `G.externalLegs.filter (attachedTo ∈ (M.parent z δ).vertices) ≤ (M.legLift z δ).legs`.

### The forest-parent residual (recorded, NOT discharged, NOT socketed)

`(M.parent z δ).vertices` is `G.vertices.filter` of three disjuncts: (i) a touched-outer-forest vertex, (ii) a
quotient-edge-preimage endpoint, (iii) an attach point of some datum leg (`∃ ℓ ∈ datum.legs, ℓ.attachedTo = v`).  The
datum (`ResolvedTouchedLegLiftDatum`) supplies only `touched_le : (touchedOuterForest z δ).externalLegs ≤ datum.legs`
and `map_eq` (the retarget image).  These bound the touched-forest legs and the retarget image but give NO per-attach-
point leg-count bound: a `G`-leg `ℓ` with `ℓ.attachedTo = v` for `v` an attach point of a *different* datum leg `ℓ'`
(disjunct (iii)), or `v` a quotient-edge-preimage endpoint (disjunct (ii)), need NOT itself occur in `datum.legs` with
matching multiplicity.  The precise missing inequality — per forest component `δ ∈ forestDomain z` —

```text
G.externalLegs.filter (fun ℓ => ℓ.attachedTo ∈ (M.parent z δ).vertices) ≤ (M.legLift z δ).legs
```

restricted to routes (ii)/(iii), is exactly the touched-leg-saturation model law audited at body-530/531; it is NOT
derivable from the datum fields alone and is NOT a physics (divergence) law.  The audit therefore legitimately stops at
"left FREE, right DERIVED, forest normalized to residual"; Step 4 (union assembly) is intentionally NOT performed because
the forest region is not closed.

Per the HALT/guards: saturation is sourced ONLY from the explicit `z.1` / `z.2` live hypotheses (`hOuter`, `hsrc`), never
from `recoveredRawUnion`'s own `W″` membership; no `houter` / forward reconstruction / round-trip; no `W″` `LegModel`
supply on any target parent; `parentCD` is untouched; the residual is recorded as an honest multiplicity obligation, NOT
classified as a physics law; the coassoc theorem is NOT re-issued; strict `StarProm` / `InnerStarRaw` stay ZERO; NO
unconditional-coassoc claim.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` /
singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-! ## Step 1 — the left residual (FREE): a sub-filter of the saturated input outer. -/

/-- **R-6c-body-535 ∎ — left-residual external-leg saturation (FREE).**  Every untouched (left-residual) component sits
in the input outer's components, so its saturation is read off the supplied input-outer saturation. -/
theorem leftResidualTouched_forestExternalLegSaturated (z : ForestBlockCodType D G)
    (hOuter : ResolvedForestExternalLegSaturated z.1.1) :
    ∀ δ ∈ leftResidualTouched z, ResolvedExternalLegSaturated G δ := by
  intro δ hδ
  simp only [leftResidualTouched, Finset.mem_filter] at hδ
  exact hOuter δ hδ.1

/-! ## Step 2 — the right recovered survivor (DERIVED): contraction transport. -/

/-- **R-6c-body-535 ∎ — right-recovered external-leg saturation (DERIVED).**  A star-avoiding survivor
`δ ∈ rightDomain z` re-embeds to `G` with the same carrier; its saturation transports from the quotient component's
saturation `hsrc` because the star-contraction retarget is the identity on `δ`'s star-avoiding carrier, so the `G`-side
and quotient-side attach filters coincide (multiplicity-safe equality). -/
theorem rightReembed_externalLegSaturated (z : ForestBlockCodType D G)
    (δ : {x // x ∈ rightDomain z})
    (hsrc : ResolvedExternalLegSaturated (z.1.1.contractWithStars (D.starOf G z.1.1)) δ.1) :
    ResolvedExternalLegSaturated G (rightReembed z δ) := by
  have hstar : Disjoint δ.1.vertices (z.1.1.starVertices (D.starOf G z.1.1)) :=
    (Finset.mem_filter.mp δ.2).2
  -- A star-avoiding `δ` avoids `A = z.1.1` entirely (its vertices sit in `G \ A`).
  have hδnotA : ∀ v ∈ δ.1.vertices, v ∉ z.1.1.vertices := by
    intro v hv hvA
    have hmem := δ.1.vertices_subset hv
    rw [ResolvedAdmissibleSubgraph.contractWithStars_vertices, Finset.mem_union] at hmem
    cases hmem with
    | inl h => exact (Finset.mem_sdiff.mp h).2 hvA
    | inr h => exact (Finset.disjoint_left.mp hstar hv) h
  -- On `G.externalLegs`, "attached to `δ`" is unchanged by the retarget.
  have hiff : ∀ ℓ ∈ G.externalLegs,
      (ℓ.attachedTo ∈ δ.1.vertices ↔
        (z.1.1.retargetExternalLeg (D.starOf G z.1.1) ℓ).attachedTo ∈ δ.1.vertices) := by
    intro ℓ _
    by_cases hA : ℓ.attachedTo ∈ z.1.1.vertices
    · have hnotδ : ℓ.attachedTo ∉ δ.1.vertices := fun h => hδnotA _ h hA
      have hstarr : (z.1.1.retargetExternalLeg (D.starOf G z.1.1) ℓ).attachedTo
          ∈ z.1.1.starVertices (D.starOf G z.1.1) := by
        unfold ResolvedAdmissibleSubgraph.retargetExternalLeg
        rw [ResolvedExternalLeg.retarget_attachedTo]
        exact retargetVertex_mem_starVertices z.1.1 (D.starOf G z.1.1) hA
      have hnotδ2 : (z.1.1.retargetExternalLeg (D.starOf G z.1.1) ℓ).attachedTo ∉ δ.1.vertices :=
        fun h => (Finset.disjoint_left.mp hstar h) hstarr
      exact ⟨fun h => absurd h hnotδ, fun h => absurd h hnotδ2⟩
    · have hid : (z.1.1.retargetExternalLeg (D.starOf G z.1.1) ℓ).attachedTo = ℓ.attachedTo := by
        unfold ResolvedAdmissibleSubgraph.retargetExternalLeg
        rw [ResolvedExternalLeg.retarget_attachedTo,
          z.1.1.retargetVertex_of_not_mem (D.starOf G z.1.1) hA]
      exact (iff_of_eq (congrArg (fun v => v ∈ δ.1.vertices) hid)).symm
  -- The retarget is the identity on the `δ`-attached submultiset.
  have hmapid : (G.externalLegs.filter (fun ℓ => ℓ.attachedTo ∈ δ.1.vertices)).map
        (z.1.1.retargetExternalLeg (D.starOf G z.1.1))
      = G.externalLegs.filter (fun ℓ => ℓ.attachedTo ∈ δ.1.vertices) := by
    conv_rhs => rw [← Multiset.map_id (G.externalLegs.filter (fun ℓ => ℓ.attachedTo ∈ δ.1.vertices))]
    apply Multiset.map_congr rfl
    intro ℓ hℓ
    have hℓPv : ℓ.attachedTo ∈ δ.1.vertices := (Multiset.mem_filter.mp hℓ).2
    have hnA : ℓ.attachedTo ∉ z.1.1.vertices := hδnotA _ hℓPv
    unfold ResolvedAdmissibleSubgraph.retargetExternalLeg ResolvedExternalLeg.retarget
    rw [z.1.1.retargetVertex_of_not_mem (D.starOf G z.1.1) hnA]
    rfl
  -- The `G`-side and quotient-side attach filters coincide.
  have hfm : (G.externalLegs.map (z.1.1.retargetExternalLeg (D.starOf G z.1.1))).filter
        (fun ℓ => ℓ.attachedTo ∈ δ.1.vertices)
      = G.externalLegs.filter (fun ℓ => ℓ.attachedTo ∈ δ.1.vertices) := by
    rw [Multiset.filter_map, ← hmapid]
    exact congrArg (Multiset.map (z.1.1.retargetExternalLeg (D.starOf G z.1.1)))
      (Multiset.filter_congr (fun ℓ hℓ => (hiff ℓ hℓ).symm))
  -- Transport `hsrc` across the equality.
  unfold ResolvedExternalLegSaturated
  show G.externalLegs.filter (fun ℓ => ℓ.attachedTo ∈ δ.1.vertices) ≤ δ.1.externalLegs
  rw [← hfm]
  have hsrc' := hsrc
  unfold ResolvedExternalLegSaturated at hsrc'
  rw [ResolvedAdmissibleSubgraph.contractWithStars_externalLegs] at hsrc'
  exact hsrc'

/-! ## Step 3 — the forest parent: normalize to the exact residual (Iff.rfl); residual recorded above. -/

/-- **R-6c-body-535 ∎ — forest-parent saturation target shape (DEFEQ normalization).**  `M.parent z δ`'s external legs
are exactly the datum preimage `(M.legLift z δ).legs`, so external-leg saturation of the de-contracted parent is DEFEQ
to the exact `G`-leg residual inequality against the datum legs.  This is the honest normal form of the forest-parent
obligation; the module docstring records the precise multiplicity gap (routes (ii)/(iii)) that the datum fields do NOT
discharge — it is the touched-leg-saturation model law (body-530/531), not a physics law and not socketed here. -/
theorem localizedParent_externalLegSaturated_target_shape
    (M : ResolvedMultiStarDecontractionSupply D) (z : ForestBlockCodType D G)
    (δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))
      // x ∈ forestDomain z}) :
    ResolvedExternalLegSaturated G (M.parent z δ)
      ↔ G.externalLegs.filter (fun ℓ => ℓ.attachedTo ∈ (M.parent z δ).vertices)
        ≤ (M.legLift z δ).legs :=
  Iff.rfl

end GaugeGeometry.QFT.Combinatorial
