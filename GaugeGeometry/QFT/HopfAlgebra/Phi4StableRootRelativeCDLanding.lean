import GaugeGeometry.QFT.HopfAlgebra.Phi4StableLeftFactorProduct

/-!
# QFT-R1-body-631 — the NATIVE stable root-relative CD landing (root-coordinate φ⁴ count)

Body-630 rebuilt, on the STABLE carrier, the left-factor product that body-625's no-go broke: the RAW
idempotence `stableLocalBoundaryCompletedGraph δ = stableLocalBoundaryCompletedGraph (stableRootRelativeInner
γ δ)` and, INSIDE that proof, the exact edge-complete boundary split
`(stableRootRelativeInner γ δ).resolvedBoundaryEdges = stableInheritedOuter γ δ + δ.resolvedBoundaryEdges`
plus the external-leg decomposition
`δ.externalLegs = (stableRootRelativeInner γ δ).externalLegs + (stableInheritedOuter γ δ).map γ.boundaryExternalLeg`.

The STABLE carrier's boundary split is EXACT — there is NO `hiddenRootBoundary` residual (contrast the OLD
`γ.boundaryCompletedResolvedGraph` route of body-599, which had to gate CD transport by
`RootRelativeBoundaryClosed`).  Consequently the φ⁴ **physical external-leg count** of `R = stableRootRelativeInner
γ δ` computed in ROOT coordinates equals that of `δ` OUTRIGHT, with no ambient transport:

```text
Eφ4(R.forget) = |R.ext| + |R.∂|            (physical count of a resolved subgraph's forget)
             = |R.ext| + |inherited| + |δ.∂|   (edge-complete boundary split, body-630)
             = |δ.ext| + |δ.∂|              (external-leg decomposition: |δ.ext| = |R.ext| + |inherited|)
             = Eφ4(δ.forget).
```

Hence the φ⁴ superficial degree is preserved and divergence transports NATIVELY — the connected /
1PI clauses move DEFINITIONALLY (`R.forget` and `δ.forget` share `vertices` / `internalEdges`), the divergent
clause moves through the DEGREE equality (Step 2), NEVER through a general ambient-congruence lemma or an
HEq/cast of different-ambient graph data (body-630's forbidden wall).  This unblocks body-630's Steps 4-5.

## Steps
* Step 1 — publish body-630's external-leg decomposition `stableRootRelativeInner_externalLegs_decompose`.
* Step 2 — the root-coordinate φ⁴ count/degree/divergent equalities
  (`stableRootRelativeInner_physicalExternalLegCount_eq` / `_phi4SuperficialDegree_eq` / `_isDivergent_iff`).
* Step 3 — topology: connected / 1PI iffs, closed by `Iff.rfl` (shared `vertices` / `internalEdges`).
* Step 4 — the HEADLINE `stableRootRelativeInner_forget_isConnectedDivergent` and the body-629-constructor
  corollary `stableRootRelativeInner_stableLocalCompletion_exists_self_isConnectedDivergent`.
* Step 5 — the live W‴ consumer `stableSplitChoice_rootRelativeInner_isConnectedDivergent` (every premise
  recovered FROM THE TYPES).

## HALT / red lines
NO general ambient-congruence lemma; NO homogeneous equality of different-ambient subgraphs; NO graph-data
`HEq` / `cast` / `▸`.  We do NOT enter `stablePromotedOf` / `selectedOuter` / product assembly / right factor
/ `quot_eq` / summand agreement / coassoc (that is body-632).  ZERO new `structure` / `class` / permanent
`instance` (one file-local `local instance` for the φ⁴ divergence family, as in body-630).  ZERO forbidden
divergence classes in any declaration TYPE; ZERO `sorry` / `admit` / `native_decide`.  body-625's no-go,
body-630, the OLD carrier, and every existing file are UNEDITED.  Axiom-clean (`propext`, `Classical.choice`,
`Quot.sound`).
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

open ResolvedFeynmanSubgraph

variable {G : ResolvedFeynmanGraph}

/-- The ONLY instance in this file: the concrete φ⁴ divergence measure family (mirrors body-630), so the
`.forget.IsDivergent` / `IsConnectedDivergent` / carrier plumbing elaborates against the φ⁴ family. -/
local instance instPhi4DivergenceMeasureFamily631 : ∀ H : FeynmanGraph, DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

/-! ## Step 1 — publish body-630's external-leg decomposition -/

/-- **body-631 (Step 1) — the lift's external-leg decomposition (published from body-630).**  Under both
saturation hypotheses, `δ`'s external legs split as the lift's own external legs plus the inherited outer
boundary legs, VERBATIM.  This is exactly the decomposition body-630 proved internally inside
`stableLocalBoundaryIterate_idempotent`; it reads only `δ.vertices` and re-uses body-597's inherited legs
with ZERO re-encode. -/
theorem stableRootRelativeInner_externalLegs_decompose (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph (stableLocalBoundaryCompletedGraph γ))
    (hγsat : ResolvedExternalLegSaturated G γ)
    (hδsat : ResolvedExternalLegSaturated (stableLocalBoundaryCompletedGraph γ) δ) :
    δ.externalLegs
      = (stableRootRelativeInner γ δ).externalLegs
        + (stableInheritedOuter γ δ).map γ.boundaryExternalLeg := by
  have hsub : δ.vertices ⊆ γ.vertices := δ.vertices_subset
  rw [externalLegs_eq_filter_of_saturated δ hδsat, stableLocalBoundaryCompletedGraph_externalLegs,
    Multiset.filter_add]
  congr 1
  · show γ.externalLegs.filter (fun ℓ => ℓ.attachedTo ∈ δ.vertices)
        = G.externalLegs.filter (fun ℓ => ℓ.attachedTo ∈ δ.vertices)
    rw [externalLegs_eq_filter_of_saturated γ hγsat, Multiset.filter_filter]
    exact Multiset.filter_congr (fun ℓ _ =>
      ⟨fun h => h.1, fun h => ⟨h, hsub h⟩⟩)
  · rw [← Multiset.map_filter_of_iff γ.boundaryExternalLeg γ.resolvedBoundaryEdges
          (fun e => γ.resolvedInsideEndpoint e ∈ δ.vertices) (fun ℓ => ℓ.attachedTo ∈ δ.vertices)
          (fun _ => Iff.rfl)]
    rfl

/-! ## Step 2 — the root-coordinate φ⁴ count / degree / divergent equalities (the crux) -/

/-- **body-631 (Step 2) — a resolved subgraph's forget physical external count.**  `Eη = |η.ext| + |η.∂|`,
via the body-589 forget compatibility of external legs and resolved boundary edges.  Card-exact.
File-local re-derivation (fresh name, no dependency on the OLD body-599 landing file). -/
theorem stableResolvedSubgraph_physicalExternalLegCount_forget {H : ResolvedFeynmanGraph}
    (η : ResolvedFeynmanSubgraph H) :
    η.forget.physicalExternalLegCount = η.externalLegs.card + η.resolvedBoundaryEdges.card := by
  unfold FeynmanSubgraph.physicalExternalLegCount FeynmanSubgraph.externalLegCount
    FeynmanSubgraph.boundaryEdgeCount
  rw [ResolvedFeynmanSubgraph.forget_externalLegs, Multiset.card_map,
    ← ResolvedFeynmanSubgraph.resolvedBoundaryEdges_forget, Multiset.card_map]

/-- **body-631 (Step 2, CRUX — root-coordinate φ⁴ count equality).**  The stable-carrier lift preserves the
physical external-leg count OUTRIGHT: `Eφ4(R.forget) = Eφ4(δ.forget)`.  The inherited legs cancel exactly —
`|δ.ext| = |R.ext| + |inherited|` (Step 1) and `|R.∂| = |inherited| + |δ.∂|` (body-630's edge-complete
boundary split), so `|R.ext| + |R.∂| = |R.ext| + |inherited| + |δ.∂| = |δ.ext| + |δ.∂|`.  NO hidden root
boundary, NO gate, NO ambient transport. -/
theorem stableRootRelativeInner_physicalExternalLegCount_eq (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph (stableLocalBoundaryCompletedGraph γ))
    (hγsat : ResolvedExternalLegSaturated G γ)
    (hδsat : ResolvedExternalLegSaturated (stableLocalBoundaryCompletedGraph γ) δ)
    (hEC : ResolvedInternalEdgeComplete γ) :
    (stableRootRelativeInner γ δ).forget.physicalExternalLegCount
      = δ.forget.physicalExternalLegCount := by
  have hR : (stableRootRelativeInner γ δ).forget.physicalExternalLegCount
      = (stableRootRelativeInner γ δ).externalLegs.card
        + (stableRootRelativeInner γ δ).resolvedBoundaryEdges.card :=
    stableResolvedSubgraph_physicalExternalLegCount_forget (stableRootRelativeInner γ δ)
  have hδ : δ.forget.physicalExternalLegCount = δ.externalLegs.card + δ.resolvedBoundaryEdges.card :=
    stableResolvedSubgraph_physicalExternalLegCount_forget δ
  have hA : δ.externalLegs.card
      = (stableRootRelativeInner γ δ).externalLegs.card + (stableInheritedOuter γ δ).card := by
    rw [stableRootRelativeInner_externalLegs_decompose γ δ hγsat hδsat, Multiset.card_add,
      Multiset.card_map]
  have hB : (stableRootRelativeInner γ δ).resolvedBoundaryEdges.card
      = (stableInheritedOuter γ δ).card + δ.resolvedBoundaryEdges.card := by
    rw [stableRootRelativeInner_resolvedBoundaryEdges_eq_of_edgeComplete γ δ hEC, Multiset.card_add]
  rw [hR, hδ]
  omega

/-- **body-631 (Step 2) — the φ⁴ superficial degree is preserved.**  `ωφ4(R.forget) = ωφ4(δ.forget)`, from
the Step-2 physical-count equality and `ωφ4 = 4 − E`.  No gate. -/
theorem stableRootRelativeInner_phi4SuperficialDegree_eq (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph (stableLocalBoundaryCompletedGraph γ))
    (hγsat : ResolvedExternalLegSaturated G γ)
    (hδsat : ResolvedExternalLegSaturated (stableLocalBoundaryCompletedGraph γ) δ)
    (hEC : ResolvedInternalEdgeComplete γ) :
    (stableRootRelativeInner γ δ).forget.phi4SuperficialDegree
      = δ.forget.phi4SuperficialDegree := by
  unfold FeynmanSubgraph.phi4SuperficialDegree
  rw [stableRootRelativeInner_physicalExternalLegCount_eq γ δ hγsat hδsat hEC]

/-- **body-631 (Step 2) — divergence transports both ways, NATIVELY.**  `R.forget` is φ⁴-divergent iff
`δ.forget` is, because their superficial degrees coincide (Step 2).  Unfolds through the φ⁴ family's
`IsDivergent := 0 ≤ phi4SuperficialDegree`.  No ambient-invariance, no measure transport. -/
theorem stableRootRelativeInner_isDivergent_iff (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph (stableLocalBoundaryCompletedGraph γ))
    (hγsat : ResolvedExternalLegSaturated G γ)
    (hδsat : ResolvedExternalLegSaturated (stableLocalBoundaryCompletedGraph γ) δ)
    (hEC : ResolvedInternalEdgeComplete γ) :
    (stableRootRelativeInner γ δ).forget.IsDivergent ↔ δ.forget.IsDivergent := by
  show (0 : Int) ≤ (stableRootRelativeInner γ δ).forget.phi4SuperficialDegree
      ↔ (0 : Int) ≤ δ.forget.phi4SuperficialDegree
  rw [stableRootRelativeInner_phi4SuperficialDegree_eq γ δ hγsat hδsat hEC]

/-! ## Step 3 — topology (thin: `R.forget` and `δ.forget` share `vertices` / `internalEdges`) -/

/-- **body-631 (Step 3) — support connectivity is shared.**  `IsConnected` reads only the induced support
graph (`vertices` / `internalEdges`), which `R.forget` and `δ.forget` carry VERBATIM; so the predicate is
definitionally the same.  Closed by `Iff.rfl`. -/
theorem stableRootRelativeInner_isSupportConnected_iff (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph (stableLocalBoundaryCompletedGraph γ)) :
    (stableRootRelativeInner γ δ).forget.IsConnected ↔ δ.forget.IsConnected := Iff.rfl

/-- **body-631 (Step 3) — 1PI is shared.**  `IsOnePI` reads only `vertices` / `internalEdges`
(support-connectivity + bridge-freeness), shared VERBATIM; definitional.  Closed by `Iff.rfl`. -/
theorem stableRootRelativeInner_isOnePI_iff (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph (stableLocalBoundaryCompletedGraph γ)) :
    (stableRootRelativeInner γ δ).forget.IsOnePI ↔ δ.forget.IsOnePI := Iff.rfl

/-! ## Step 4 — the HEADLINE native CD landing + the body-629 constructor corollary -/

/-- **body-631 (Step 4, HEADLINE) — the NATIVE stable root-relative CD landing.**  From `δ.forget`'s
connected-divergent property, the root lift `R = stableRootRelativeInner γ δ` is connected divergent on
`G.forget`: connectivity and 1PI move DEFINITIONALLY (Step 3), divergence moves through the root-coordinate
DEGREE equality (Step 2).  This is body-599's `rootRelativeInner_forget_isConnectedDivergent_of_closed`
argument re-derived NATIVELY on the stable carrier — with NO boundary-closed gate (the stable carrier's
boundary split is already exact) and NO ambient transport.  Unblocks body-630's Steps 4-5. -/
theorem stableRootRelativeInner_forget_isConnectedDivergent (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph (stableLocalBoundaryCompletedGraph γ))
    (hγsat : ResolvedExternalLegSaturated G γ)
    (hδsat : ResolvedExternalLegSaturated (stableLocalBoundaryCompletedGraph γ) δ)
    (hEC : ResolvedInternalEdgeComplete γ)
    (hδCD : δ.forget.IsConnectedDivergent) :
    (stableRootRelativeInner γ δ).forget.IsConnectedDivergent :=
  ⟨(stableRootRelativeInner_isSupportConnected_iff γ δ).mpr hδCD.1,
   (stableRootRelativeInner_isOnePI_iff γ δ).mpr hδCD.2.1,
   (stableRootRelativeInner_isDivergent_iff γ δ hγsat hδsat hEC).mpr hδCD.2.2⟩

/-- **body-631 (Step 4, body-629-constructor corollary) — the root lift's own stable completion carries a
self connected-divergent certificate.**  Feed the HEADLINE conclusion into body-629's
`stableLocalBoundaryCompletedGraph_exists_self_isConnectedDivergent`; this is precisely the `hCDR`-shaped
`∃`-certificate that body-630's `stableForestLeftFactor_gen_eq_promoted` (and the downstream stable
generator constructor) consumes for the root-promoted completion. -/
theorem stableRootRelativeInner_stableLocalCompletion_exists_self_isConnectedDivergent
    (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph (stableLocalBoundaryCompletedGraph γ))
    (hγsat : ResolvedExternalLegSaturated G γ)
    (hδsat : ResolvedExternalLegSaturated (stableLocalBoundaryCompletedGraph γ) δ)
    (hEC : ResolvedInternalEdgeComplete γ)
    (hδCD : δ.forget.IsConnectedDivergent) :
    ∃ hWF : (stableLocalBoundaryCompletedGraph (stableRootRelativeInner γ δ)).forget.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent
        (stableLocalBoundaryCompletedGraph (stableRootRelativeInner γ δ)).forget
        (phi4DivergenceMeasureFamily
          (stableLocalBoundaryCompletedGraph (stableRootRelativeInner γ δ)).forget)
        (FeynmanSubgraph.self
          (stableLocalBoundaryCompletedGraph (stableRootRelativeInner γ δ)).forget hWF) :=
  stableLocalBoundaryCompletedGraph_exists_self_isConnectedDivergent (stableRootRelativeInner γ δ)
    (stableRootRelativeInner_forget_isConnectedDivergent γ δ hγsat hδsat hEC hδCD)

/-! ## Step 5 — the live W‴ consumer (every premise recovered FROM THE TYPES) -/

/-- **body-631 (Step 5, LIVE CONSUMER) — the split-choice root-relative CD landing.**  For a live stable
resolved split choice `s`, a live OUTER component `γ`, a live inner forest `B` over
`stableLocalBoundaryCompletedGraph γ.1`, and a live inner component `δ`, the root lift `stableRootRelativeInner
γ.1 δ.1` is connected divergent on `G.forget`.  EVERY premise is recovered from the types with ZERO added
gate: outer saturation `hγsat` and outer edge-completeness `hEC` from `s.outer_mem` via the W‴ membership
criterion; inner saturation `hδsat` from `B.2` via the same criterion on the stable completion; inner CD
`hδCD` from `B.1`'s `isConnectedDivergent` field at `δ.2`. -/
theorem stableSplitChoice_rootRelativeInner_isConnectedDivergent {hSt : StableResolvedBoundaryIds G}
    (s : StablePhi4ResolvedSplitChoice G hSt)
    (γ : {γ // γ ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G s.outer})
    (B : StableLocalForestIdx γ.1)
    (δ : {δ // δ ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily
        (stableLocalBoundaryCompletedGraph γ.1) B.1}) :
    (stableRootRelativeInner γ.1 δ.1).forget.IsConnectedDivergent := by
  have hO := (mem_phi4WTriplePrimeIndex G s.outer).mp s.outer_mem
  have hγsat : ResolvedExternalLegSaturated G γ.1 := hO.2.2.2.2.2.1 γ.1 γ.2
  have hEC : ResolvedInternalEdgeComplete γ.1 := hO.2.2.2.2.2.2 γ.1 γ.2
  have hB := (mem_phi4WTriplePrimeIndex (stableLocalBoundaryCompletedGraph γ.1) B.1).mp B.2
  have hδsat : ResolvedExternalLegSaturated (stableLocalBoundaryCompletedGraph γ.1) δ.1 :=
    hB.2.2.2.2.2.1 δ.1 δ.2
  have hδCD : δ.1.forget.IsConnectedDivergent := B.1.isConnectedDivergent δ.1 δ.2
  exact stableRootRelativeInner_forget_isConnectedDivergent γ.1 δ.1 hγsat hδsat hEC hδCD

end GaugeGeometry.QFT.Combinatorial
