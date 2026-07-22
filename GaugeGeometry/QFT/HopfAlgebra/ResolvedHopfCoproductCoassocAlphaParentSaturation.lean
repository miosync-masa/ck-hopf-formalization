import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaSaturationAlgebra
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaRecoveredSaturationAudit
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocLocalizedParentRetarget
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAmbientRetargetTransport
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocMultiStarDecontraction
import GaugeGeometry.QFT.HopfAlgebra.BoundarySemanticCorrespondence

/-!
# R-6c-body-536 — forest-parent external-leg saturation via boundary-ID map cancellation (PROVED)

Five-hundred-and-thirty-sixth genuine-body step.  This **OVERTURNS body-535's pessimistic verdict.**  Body-535 recorded
the forest-parent residual

```text
G.externalLegs.filter (fun ℓ => ℓ.attachedTo ∈ (M.parent z δ).vertices) ≤ (M.legLift z δ).legs
```

as an un-dischargeable "touched-leg-saturation model law" (the routes-(ii)/(iii) multiplicity gap).  That verdict was too
pessimistic: the residual IS dischargeable — **not** by resurrecting a `LegModel` physics law, but by a purely combinatorial
**boundary-ID map-cancellation theorem** that consumes the same per-component source saturation `hInner` already available
region-by-region (the quotient component `touchedLocalComponent z δ.1` is externally-leg-saturated inside its contracted
ambient) plus the ambient `G.LegIdsUnique`.

## The cancellation mechanism

Write `P := G.externalLegs.filter (attachedTo ∈ (M.parent z δ).vertices)`,
`f := (touchedOuterForest z δ.1).retargetExternalLeg (D.starOf G z.1.1)`, `datum := M.legLift z δ`.

1. **`P.map f ≤ datum.legs.map f`** (Step 3 + `datum.map_eq`).  Every parent-attached `G`-leg `ℓ` retargets (via the
   D4 crux `localizedParentVertex_retargets`, body-329) to a leg landing in `δ.1.vertices`, so `P.map f` sits inside the
   `δ.1`-attach filter of the contracted ambient; that filter is `≤ (touchedLocalComponent z δ.1).externalLegs = δ.1.externalLegs`
   by the supplied source saturation `hInner`; and `datum.map_eq` says `datum.legs.map f = δ.1.externalLegs` exactly.
2. **`f` is `InjOn G.externalLegs`** (Step 2), because `f = ResolvedExternalLeg.retarget (retargetVertex …)` is the
   identity-preserving leg retarget, injective on submultiples of `G.externalLegs` under `G.LegIdsUnique`
   (the R-3b engine `resolvedLegRetargetInjectiveOn`).
3. **`P ≤ datum.legs`** (Step 1 + Step 4): a generic multiset-order cancellation
   `M₁.map f ≤ M₂.map f` + `f` `InjOn S` + `M₁, M₂ ≤ S` ⇒ `M₁ ≤ M₂` (via `count_map_eq_count_of_injOn_mem`, body-436).

The boundary IDs (`legId`, preserved by `retarget`) cancel the gluing multiplicity that body-535 feared was ambiguous:
because the retarget is an injection on the `G`-leg boundary, the map inequality descends to the un-mapped multisets with
matching multiplicity.  **No datum field is added, no socket is created, no physics law is invoked.**

## What is proved

* `le_of_map_le_map_of_injOn_le` — generic multiplicity-safe map-cancellation of multiset order (Step 1).
* `retargetExternalLeg_injOn_externalLegs` — the leg retarget is `InjOn G.externalLegs` under `LegIdsUnique` (Step 2).
* `localizedParent_externalLegFilter_map_le` — the parent-filter map bound `P.map f ≤ δ.1.externalLegs` (Step 3).
* `localizedParent_externalLegSaturated_of_source` — **the load-bearing result**: from the per-component source
  saturation `hInner` and `hId`, the de-contracted parent `M.parent z δ` is externally-leg-saturated in `G` (Step 4).
* `multiStarForestRecovered_forestExternalLegSaturated` — the whole recovered forest region `M.forestRecoveredMulti F z`
  is forest-saturated, given a per-component source-saturation hypothesis `hInnerAll` and `hId` (Step 5, dispatch over
  `forestRecoveredMulti_elements`).

## The full recovered-union (recorded recipe, NOT forced)

With this forest-recovered closure in hand, the canonical `W″` recovered raw union is closed by
`resolvedForestExternalLegSaturated_union` (body-534) applied twice, combining body-535's `leftResidualTouched_…`
(left, FREE) + `rightReembed_externalLegSaturated` (right, DERIVED) + this forest-recovered closure.  Wiring the union
requires identifying the concrete three region admissible-subgraphs feeding `recoveredRawUnion` and their cross-disjoint
`hCross` witnesses; per the HALT/guards it is NOT forced here (no target recovered-union membership is read).  All three
per-region closures are now individually proved; only the concrete union assembly remains.

Per the HALT/guards: `hId` and the source saturations `hInner`/`hInnerAll` are explicit HYPOTHESES (sourced from the live
`z.1`/`z.2` `W″` membership at the call site, never read here); no target recovered-union membership; `parentCD` is
untouched; no `houter` / forward reconstruction / round-trip; no new datum field or model socket; the coassoc theorem is
NOT re-issued; strict `StarProm` / `InnerStarRaw` stay ZERO; NO unconditional-coassoc claim.
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

/-! ## Step 1 — generic multiset-order cancellation under an `InjOn` map. -/

/-- **R-6c-body-536 ∎ — map-cancellation of multiset order (multiplicity-safe).**  If `f` is injective on a set `S`
containing both `M₁` and `M₂`, then `M₁.map f ≤ M₂.map f` descends to `M₁ ≤ M₂` — the mapped inequality cancels because
`f` preserves per-element occurrence counts on `S` (`count_map_eq_count_of_injOn_mem`, body-436). -/
theorem le_of_map_le_map_of_injOn_le {α β : Type*} [DecidableEq α] [DecidableEq β] {f : α → β}
    {M₁ M₂ S : Multiset α} (hInj : Set.InjOn f {x | x ∈ S})
    (hM₁ : M₁ ≤ S) (hM₂ : M₂ ≤ S) (hmap : M₁.map f ≤ M₂.map f) : M₁ ≤ M₂ := by
  rw [Multiset.le_iff_count]
  intro x
  by_cases hx : x ∈ M₁
  · have hxS : x ∈ {x | x ∈ S} := Multiset.mem_of_le hM₁ hx
    have h1 : (M₁.map f).count (f x) = M₁.count x :=
      count_map_eq_count_of_injOn_mem hInj (fun a ha => Multiset.mem_of_le hM₁ ha) hxS
    have h2 : (M₂.map f).count (f x) = M₂.count x :=
      count_map_eq_count_of_injOn_mem hInj (fun a ha => Multiset.mem_of_le hM₂ ha) hxS
    have hc := Multiset.count_le_of_le (f x) hmap
    rw [h1, h2] at hc
    exact hc
  · rw [Multiset.count_eq_zero_of_notMem hx]
    exact Nat.zero_le _

/-! ## Step 2 — the leg retarget is `InjOn G.externalLegs` under `LegIdsUnique`. -/

/-- **R-6c-body-536 ∎ — the identity-preserving leg retarget is `InjOn` the ambient external legs.**  Singleton-by-
singleton via the R-3b engine `resolvedLegRetargetInjectiveOn`, under `LegIdsUnique` (mirrors body-436's
`retargetEdge_injOn_internalEdges`). -/
theorem retargetExternalLeg_injOn_externalLegs (hId : G.LegIdsUnique) (g : VertexId → VertexId) :
    Set.InjOn (ResolvedExternalLeg.retarget g) {ℓ : ResolvedExternalLeg | ℓ ∈ G.externalLegs} := by
  intro ℓ₁ h₁ ℓ₂ h₂ heq
  have h1G : ({ℓ₁} : Multiset ResolvedExternalLeg) ≤ G.externalLegs := Multiset.singleton_le.mpr h₁
  have h2G : ({ℓ₂} : Multiset ResolvedExternalLeg) ≤ G.externalLegs := Multiset.singleton_le.mpr h₂
  have hmap : ({ℓ₁} : Multiset ResolvedExternalLeg).map (ResolvedExternalLeg.retarget g)
      = ({ℓ₂} : Multiset ResolvedExternalLeg).map (ResolvedExternalLeg.retarget g) := by
    simp only [Multiset.map_singleton]
    exact congrArg (fun x => ({x} : Multiset ResolvedExternalLeg)) heq
  exact Multiset.singleton_inj.mp
    (GaugeGeometry.QFT.HopfAlgebra.resolvedLegRetargetInjectiveOn G hId g h1G h2G hmap)

/-! ## Step 3 — the parent-filter map bound. -/

/-- **R-6c-body-536 ∎ — the parent-attach filter, mapped through the touched-forest retarget, lands in `δ.1`'s
external legs.**  Every `G`-leg attached to a parent vertex retargets into `δ.1.vertices` (the D4 crux
`localizedParentVertex_retargets`, body-329), so the mapped filter sits inside the `δ.1`-attach filter of the contracted
ambient, which the supplied source saturation `hInner` bounds by `(touchedLocalComponent z δ.1).externalLegs = δ.1.externalLegs`. -/
theorem localizedParent_externalLegFilter_map_le (M : ResolvedMultiStarDecontractionSupply D)
    (z : ForestBlockCodType D G)
    (δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))
      // x ∈ forestDomain z})
    (hInner : ResolvedExternalLegSaturated
        ((touchedOuterForest z δ.1).contractWithStars (D.starOf G z.1.1))
        (touchedLocalComponent z δ.1)) :
    (G.externalLegs.filter (fun ℓ => ℓ.attachedTo ∈ (M.parent z δ).vertices)).map
        ((touchedOuterForest z δ.1).retargetExternalLeg (D.starOf G z.1.1))
      ≤ δ.1.externalLegs := by
  have hstep_a :
      (G.externalLegs.filter (fun ℓ => ℓ.attachedTo ∈ (M.parent z δ).vertices)).map
          ((touchedOuterForest z δ.1).retargetExternalLeg (D.starOf G z.1.1))
        ≤ ((touchedOuterForest z δ.1).contractWithStars (D.starOf G z.1.1)).externalLegs.filter
            (fun ℓ => ℓ.attachedTo ∈ δ.1.vertices) := by
    rw [Multiset.le_filter]
    refine ⟨?_, ?_⟩
    · rw [ResolvedAdmissibleSubgraph.contractWithStars_externalLegs]
      exact Multiset.map_le_map (Multiset.filter_le _ _)
    · intro a ha
      obtain ⟨ℓ, hℓ, rfl⟩ := Multiset.mem_map.mp ha
      have hℓP : ℓ.attachedTo ∈ (M.parent z δ).vertices := (Multiset.mem_filter.mp hℓ).2
      have hattach :
          ((touchedOuterForest z δ.1).retargetExternalLeg (D.starOf G z.1.1) ℓ).attachedTo
            = (touchedOuterForest z δ.1).retargetVertex (D.starOf G z.1.1) ℓ.attachedTo := by
        unfold ResolvedAdmissibleSubgraph.retargetExternalLeg
        rw [ResolvedExternalLeg.retarget_attachedTo]
      rw [hattach]
      exact localizedParentVertex_retargets z δ.1 (M.legLift z δ) (M.hE z) (M.hL z) hℓP
  exact le_trans hstep_a hInner

/-! ## Step 4 — boundary-ID cancellation closes forest-parent saturation. -/

/-- **R-6c-body-536 ∎ — the de-contracted parent is externally-leg-saturated (BOUNDARY-ID CANCELLATION).**  This is the
load-bearing result that overturns body-535.  From the per-component source saturation `hInner` (Step 3 gives
`P.map f ≤ δ.1.externalLegs = datum.legs.map f`) and the leg-retarget injectivity (Step 2, under `hId`), the generic
map-cancellation (Step 1) descends the mapped inequality to `P ≤ datum.legs = (M.parent z δ).externalLegs`.  No datum
field, no socket, no physics law. -/
theorem localizedParent_externalLegSaturated_of_source (M : ResolvedMultiStarDecontractionSupply D)
    (z : ForestBlockCodType D G)
    (δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))
      // x ∈ forestDomain z})
    (hId : G.LegIdsUnique)
    (hInner : ResolvedExternalLegSaturated
        ((touchedOuterForest z δ.1).contractWithStars (D.starOf G z.1.1))
        (touchedLocalComponent z δ.1)) :
    ResolvedExternalLegSaturated G (M.parent z δ) := by
  have hstep3 := localizedParent_externalLegFilter_map_le M z δ hInner
  show G.externalLegs.filter (fun ℓ => ℓ.attachedTo ∈ (M.parent z δ).vertices) ≤ (M.legLift z δ).legs
  have hmap :
      (G.externalLegs.filter (fun ℓ => ℓ.attachedTo ∈ (M.parent z δ).vertices)).map
          ((touchedOuterForest z δ.1).retargetExternalLeg (D.starOf G z.1.1))
        ≤ (M.legLift z δ).legs.map
            ((touchedOuterForest z δ.1).retargetExternalLeg (D.starOf G z.1.1)) := by
    rw [(M.legLift z δ).map_eq, touchedLocalComponent_externalLegs]
    exact hstep3
  exact le_of_map_le_map_of_injOn_le
    (retargetExternalLeg_injOn_externalLegs hId
      ((touchedOuterForest z δ.1).retargetVertex (D.starOf G z.1.1)))
    (Multiset.filter_le _ _) (M.legLift z δ).legs_le hmap

/-! ## Step 5 — the recovered forest region is forest-saturated. -/

/-- **R-6c-body-536 ∎ — the recovered forest region is forest external-leg-saturated.**  Given a per-component source
saturation `hInnerAll` and `hId`, each parent-image component `M.parent z δ` is saturated by Step 4; dispatch over
`forestRecoveredMulti_elements` (the parent image). -/
theorem multiStarForestRecovered_forestExternalLegSaturated
    (F : ResolvedCanonicalStarFacts D) (M : ResolvedMultiStarDecontractionSupply D)
    (z : ForestBlockCodType D G) (hId : G.LegIdsUnique)
    (hInnerAll : ∀ δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))
        // x ∈ forestDomain z},
        ResolvedExternalLegSaturated
          ((touchedOuterForest z δ.1).contractWithStars (D.starOf G z.1.1))
          (touchedLocalComponent z δ.1)) :
    ResolvedForestExternalLegSaturated (M.forestRecoveredMulti F z) := by
  intro γ hγ
  rw [ResolvedMultiStarDecontractionSupply.forestRecoveredMulti_elements] at hγ
  obtain ⟨δ, -, rfl⟩ := Finset.mem_image.mp hγ
  exact localizedParent_externalLegSaturated_of_source M z δ hId (hInnerAll δ)

end GaugeGeometry.QFT.Combinatorial
