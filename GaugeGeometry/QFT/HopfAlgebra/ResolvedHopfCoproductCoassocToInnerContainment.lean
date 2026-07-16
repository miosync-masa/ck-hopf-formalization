import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRepresentedByTouched

/-!
# R-6c-body-324 — M3 `toInner` containments: vertices/internalEdges PROVED; external-leg gap = verdict (b)

Three-hundred-and-twenty-fourth genuine-body step — Front-1 M3, the single-component `toInner` retype (a touched outer
component `A` re-typed into `localizedParent`).  Two of the three subgraph-containments needed for
`toInner A : ResolvedFeynmanSubgraph (localizedParent z δ hE hL).toResolvedFeynmanGraph` (data `:= A`'s) are PROVED here
(vertices, internalEdges).  The THIRD — external legs — is BLOCKED (verdict **(b)**): it is not a mathematical falsehood
but is underivable from the current base API, because `localizedParent.externalLegs` is a `Classical.choose`.

## Banked here (the two clean containments)

* `touched_component_vertices_subset` — `A.vertices ⊆ (localizedParent z δ hE hL).vertices`
  (`parentOfQuotient_vertices` filter, first disjunct via `mem_vertices` + `A.vertices_subset`).
* `touched_component_internalEdges_le` — `A.internalEdges ≤ (localizedParent z δ hE hL).internalEdges`
  (`Finset.single_le_sum` on `internalEdges = elements.sum` then `parentOfQuotient_containsAoutEdges`).

Once the leg containment lands, `toInner A` (data `:= A`'s + these three) is constructible, and — by `promote_vertices`/
`_internalEdges`/`_externalLegs` (all `rfl`) + `ResolvedFeynmanSubgraph.ext` — `promote (localizedParent …) (toInner A) = A`
holds by `ext` with three `rfl`s; `toInner_isConnectedDivergent` transports via `promote_forget_toFeynmanGraph` + M2a's
ambient-invariance pattern; `toInner_injective` is same-data injectivity.  All light — gated only on the leg field.

## The external-leg gap (verdict b, the M3 crux)

`localizedParent.externalLegs = quotientLegPreimage (touchedOuterForest z δ) (D.starOf G z.1.1) (touchedLocalComponent z δ)`
(ActualSigmaCover.lean:894-906), and `quotientLegPreimage` is a **`Classical.choose`** of
`∃ L ≤ G.externalLegs, L.map (Aout.retargetExternalLeg starOf) = δ.externalLegs` (ActualSigmaCover.lean:837-852),
exposing ONLY `quotientLegPreimage_le` (:855) and `quotientLegPreimage_map` (:863).  Because `retargetExternalLeg`
(ResolvedSubGraph.lean:278) is NON-injective (each component's attach-vertex collapses to its star), a `≤` on the
`retarget`-IMAGES (`A.externalLegs.map retarget ≤ δ.externalLegs`) does NOT lift to a `≤` on the preimages — the chosen
`L` is an arbitrary preimage of the WHOLE `δ.externalLegs` and need not contain `A`'s own legs.  So
`A.externalLegs ≤ localizedParent.externalLegs` is **underivable** and `toInner A` cannot carry `externalLegs := A.externalLegs`
and typecheck.  Not falsehood (c): a preimage containing every touched `A`'s legs DOES exist (`A.externalLegs.map retarget`
attaches to `starOf A ∈ δ.vertices`, so it is `≤ δ.externalLegs`); the `.choose` just isn't pinned to it.

The edge side has the canonical containment `parentOfQuotient_containsAoutEdges` (`Aout.internalEdges ≤ result`, :958);
the leg side LACKS the analogous `quotientLegPreimage_containsAoutLegs`.  That missing lemma is the whole gap.

## The minimal fix (next body — a base-API strengthening, NOT constructible in one downstream file)

Strengthen `quotientLegPreimage_exists` (ActualSigmaCover.lean:837) to additionally choose
`L` with `(touchedOuterForest z δ).externalLegs ≤ L` (both `≤ G.externalLegs`; the aggregate `elements.sum (·.externalLegs)`
already `map`-retargets onto `δ.externalLegs`, so such an `L` exists), exposing a new
`quotientLegPreimage_containsAoutLegs : Aout.externalLegs ≤ quotientLegPreimage Aout starOf δ` paralleling
`parentOfQuotient_containsAoutEdges`.  Then `A.externalLegs ≤ (touchedOuterForest z δ).externalLegs`
(`Finset.single_le_sum` on `externalLegs = elements.sum`) `≤ localizedParent.externalLegs` closes Q4 as verdict (a), and
the whole `toInner` API is light.  This edits the base `ResolvedActualSigmaCover` (the `Classical.choose` witness), so it
is NOT a one-new-file downstream body — it is flagged for the user's decision (strengthen the base `choose`, or introduce
a canonical-leg parent variant).

Per the HALT: only the vertices/internalEdges containments are proved; the external-leg containment / `toInner` /
`promote_toInner` / CD / injectivity are NOT built (gated on the leg gap); no carrier / `ForestIdx`; no singleton collapse;
the M2b parent CD is not used; no facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

variable {D : ResolvedCoproductProperForestData}

set_option linter.unusedSectionVars false

/-- **R-6c-body-324 — M3 containment (1): a touched component's vertices lie in the localized parent.** -/
theorem touched_component_vertices_subset {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
    (hE : ∀ e ∈ G.internalEdges, e.source ∈ G.vertices ∧ e.target ∈ G.vertices)
    (hL : ∀ ℓ ∈ G.externalLegs, ℓ.attachedTo ∈ G.vertices)
    {A : ResolvedFeynmanSubgraph G} (hA : A ∈ (touchedOuterForest z δ).elements) :
    A.vertices ⊆ (localizedParent z δ hE hL).vertices := by
  intro v hv
  rw [localizedParent, parentOfQuotient_vertices, Finset.mem_filter]
  exact ⟨A.vertices_subset hv, Or.inl (ResolvedAdmissibleSubgraph.mem_vertices.mpr ⟨A, hA, hv⟩)⟩

/-- **R-6c-body-324 — M3 containment (2): a touched component's internal edges lie in the localized parent.** -/
theorem touched_component_internalEdges_le {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
    (hE : ∀ e ∈ G.internalEdges, e.source ∈ G.vertices ∧ e.target ∈ G.vertices)
    (hL : ∀ ℓ ∈ G.externalLegs, ℓ.attachedTo ∈ G.vertices)
    {A : ResolvedFeynmanSubgraph G} (hA : A ∈ (touchedOuterForest z δ).elements) :
    A.internalEdges ≤ (localizedParent z δ hE hL).internalEdges :=
  le_trans (Finset.single_le_sum (fun _ _ => Multiset.zero_le _) hA)
    (parentOfQuotient_containsAoutEdges (touchedOuterForest z δ) (D.starOf G z.1.1)
      (touchedLocalComponent z δ) hE hL)

end GaugeGeometry.QFT.Combinatorial
