import GaugeGeometry.QFT.HopfAlgebra.Phi4StableForwardInverseForestRecontraction

/-!
# QFT-R1-body-645b — stable FOREST completion reconciliation HEADLINE (Steps 5–6)

Body-645a delivered the RAW inverse recontraction
`(stableInvLocalContractGraph hSt I).mapPerm (stableInvReconTau hSt I) = stableLocalBoundaryCompletedGraph δ.1`.
This body (645b) closes the HEADLINE: the stable remnant of the recovered forward occurrence, DECOMPLETED and
RE-COMPLETED, equals the original star-touching target `δ.1` RE-COMPLETED — as AMBIENT-FREE plain
`ResolvedFeynmanGraph`s.

The forward correcting permutation `stableRemnantTau o` (body-635) and the inverse correcting permutation
`stableInvReconTau hSt I` (body-645a) are **NEVER equated globally**.  Only their ACTION on the FINITE visible
support of the (shared) local contract graph is used: they AGREE on every visible vertex, hence their `mapPerm`
images of that one graph coincide, and body-635's `stableRemnant_contractTwice` + body-645a's
`stableInvRecontraction_raw` close the loop.

## Steps (this file)
* **Step 1** — owner alignment: the body-645a defeq anchor `stableInvLocalContractGraph_eq_stableLocalContractGraph`
  identifies the two local contract graphs (`rfl`); `o.γ.1 = recoveredParent I`, `o.B.1 = innerForest` are `rfl`.
* **Step 2** — `stableForwardInverse_localContract_vertex_cases`: a visible vertex is either a survivor
  (`o.γ.1.vertices \ o.B.1.vertices`) or a canonical inner star (from a touched outer component), via
  `contractWithStars_vertices` + `mem_starVertices` + body-642 `element_origin`.
* **Step 3** — `stableForwardInverse_tau_agree_on_localContract_vertices` (CRUX): on each visible vertex the two
  τ agree.  Survivors are FIXED by both (`stableRemnantTau_fix` / `stableInvReconTau_fix`, DEFEQ regions).  Stars:
  `stableRemnantTau_map` lands `starOf G (stableSelectedOuter s.1) (stableRootRelativeInner o.γ.1 …)`, aligned to
  `stableInvReconTau_map`'s `starOf G z.1.1 γ` by body-642 `rootRelativeInner_eq` (`stableRootRelativeInner
  (recoveredParent I) (innerComponent γ) = γ`) + body-644 `stableSelectedOuter (recoveredResolved) = z.1.1` —
  BOTH in the SAME ambient `G`, NO cross-ambient transport.
* **Step 4** — `stableForwardInverse_localContract_mapPerm_eq`: a `private` clean mapPerm-congruence
  (`resolvedGraph_mapPerm_congr_of_agree`: equal graph + vertex-set agreement ⇒ equal `mapPerm`; edges/legs use
  only endpoints/attachments ∈ vertices) projects Step 3 onto all three `mapPerm` fields.
* **Step 5 (HEADLINE)** — `stableForwardInverse_forest_completion_reconcile`: `stableRemnant_contractTwice o`
  → Step 4 → body-645a `stableInvRecontraction_raw`.  A homogeneous `ResolvedFeynmanGraph` RAW equality.

## Ownership boundary — MUST NOT consume as terms
The OLD forward map / OLD τ / OLD recontraction / the 623 Equiv are NEVER consumed.  Body-635's occurrence /
τ / `contractTwice`, body-644's occurrence + outer equality, body-642's inner forest + `rootRelativeInner_eq`
+ `element_origin`, and body-645a's inverse τ + RAW recontraction are reused as STATED.  The two permutations
are used ONLY through their per-point action lemmas.

## HALT / red lines
NO cross-ambient subgraph `Eq` (`stableRemnantComponent o = δ.1` FORBIDDEN — only the AMBIENT-FREE completion
`Eq`); NEVER `stableRemnantTau o = stableInvReconTau hSt I` / global τ / strict star equality.  NO whole
quotient forest / `Sigma.ext` / right inverse / `Bijective` / bare `Equiv` (`Equiv.Perm` fine) / `sum_bij` /
alpha / coassoc / orbit quotient / dedup.  ZERO PUBLIC `HEq` / `cast` / graph-data transport `▸` (Prop-membership
`▸` only).  ZERO new `structure` / `class` / permanent `instance` (one file-local `local instance`); every
transport / clean re-derivation helper is `private`.  ZERO forbidden divergence class in any declaration TYPE.
Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

open ResolvedFeynmanSubgraph

variable {G : ResolvedFeynmanGraph}

set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-- The concrete φ⁴ divergence measure family, registered file-locally (providable instance, NO forbidden
class). -/
noncomputable local instance instPhi4DivergenceMeasureFamily645b :
    (H : FeynmanGraph) → DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

/-! ## Step 0 — file-local clean helpers (a mapPerm congruence + two support facts) -/

/-- **body-645b (Step 0, PRIVATE) — clean `mapPerm` congruence.**  Two vertex permutations that AGREE on a
graph's vertices, its edge endpoints, and its leg attachments produce the SAME id-preserving relabeling.  A pure
`Finset.image_congr` / `Multiset.map_congr` fact; NO divergence class in the type; `private`. -/
private theorem resolvedGraph_mapPerm_congr_of_agree {K : ResolvedFeynmanGraph}
    {π σ : Equiv.Perm VertexId}
    (hV : ∀ v ∈ K.vertices, π v = σ v)
    (hE : ∀ e ∈ K.internalEdges, π e.source = σ e.source ∧ π e.target = σ e.target)
    (hL : ∀ ℓ ∈ K.externalLegs, π ℓ.attachedTo = σ ℓ.attachedTo) :
    K.mapPerm π = K.mapPerm σ := by
  have hv : K.vertices.image π = K.vertices.image σ :=
    Finset.image_congr (fun v hv => hV v hv)
  have hi : K.internalEdges.map (ResolvedFeynmanEdge.map π)
      = K.internalEdges.map (ResolvedFeynmanEdge.map σ) := by
    apply Multiset.map_congr rfl
    intro e he
    obtain ⟨hs, ht⟩ := hE e he
    show ResolvedFeynmanEdge.map π e = ResolvedFeynmanEdge.map σ e
    unfold ResolvedFeynmanEdge.map
    rw [hs, ht]
  have hl : K.externalLegs.map (ResolvedExternalLeg.map π)
      = K.externalLegs.map (ResolvedExternalLeg.map σ) := by
    apply Multiset.map_congr rfl
    intro ℓ hℓ
    show ResolvedExternalLeg.map π ℓ = ResolvedExternalLeg.map σ ℓ
    unfold ResolvedExternalLeg.map
    rw [hL ℓ hℓ]
  show ResolvedFeynmanGraph.mapPerm π K = ResolvedFeynmanGraph.mapPerm σ K
  unfold ResolvedFeynmanGraph.mapPerm
  rw [hv, hi, hl]

/-- **body-645b (Step 0, PRIVATE) — an inner component lands in the stable recovered inner forest's elements.**
Re-derivation of body-645a's `private` `stableInvInnerComponent_mem` (that one is not exported).  Prop-only. -/
private theorem stableInvInnerComponent_mem' (hSt : StableResolvedBoundaryIds G)
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ)
    {γ : ResolvedFeynmanSubgraph G} (hγ : γ ∈ (phi4WTriplePrime_touchedOuterForest z δ).elements) :
    stableInvInnerComponent hSt I γ hγ ∈ (stableInvRecoveredInnerForest hSt I).elements := by
  rw [stableInvRecoveredInnerForest_elements]
  exact Finset.mem_image.mpr ⟨⟨γ, hγ⟩, Finset.mem_attach _ _, rfl⟩

/-- **body-645b (Step 0, PRIVATE) — leg attachments of the local contract graph lie in its vertices.**  The
contract graph's legs are the inner ambient's completed legs retargeted; each attachment lands in the contracted
vertex set (`retargetVertex_mem_contractWithStars_vertices`, feeding the completed-leg support).  Prop-only. -/
private theorem stableLocalContract_leg_attached {hSt : StableResolvedBoundaryIds G}
    {s : StablePhi4MixedSplitChoice G hSt} (o : StableForestChoiceOccurrence s)
    {ℓ : ResolvedExternalLeg} (hℓ : ℓ ∈ (stableLocalContractGraph o).externalLegs) :
    ℓ.attachedTo ∈ (stableLocalContractGraph o).vertices := by
  rw [stableLocalContractGraph, ResolvedAdmissibleSubgraph.contractWithStars_externalLegs] at hℓ
  obtain ⟨ℓ₀, hℓ₀, rfl⟩ := Multiset.mem_map.mp hℓ
  have ha0 : ℓ₀.attachedTo ∈ (stableLocalBoundaryCompletedGraph o.γ.1).vertices := by
    rw [stableLocalBoundaryCompletedGraph_externalLegs] at hℓ₀
    rw [stableLocalBoundaryCompletedGraph_vertices]
    rcases Multiset.mem_add.mp hℓ₀ with h | h
    · exact o.γ.1.legs_supported ℓ₀ h
    · obtain ⟨e, he, rfl⟩ := Multiset.mem_map.mp h
      exact o.γ.1.resolvedInsideEndpoint_mem e
        (ResolvedFeynmanSubgraph.resolvedBoundaryEdges_mem.mp he).2
  rw [stableLocalContractGraph]
  simp only [ResolvedAdmissibleSubgraph.retargetExternalLeg, ResolvedExternalLeg.retarget_attachedTo]
  exact o.B.1.retargetVertex_mem_contractWithStars_vertices _ ha0

/-! ## Step 2 — visible-vertex classification -/

/-- **body-645b (Step 2) — the visible-vertex dichotomy.**  A vertex of the local contract graph of the stable
recovered forward occurrence is either a survivor (`o.γ.1.vertices \ o.B.1.vertices`) or the canonical local star
of a stable inner component coming from a touched outer component `γ` (body-642 `element_origin`).  Uses ONLY the
`contractWithStars_vertices` union + `mem_starVertices`; no claim over all `VertexId`. -/
theorem stableForwardInverse_localContract_vertex_cases (hSt : StableResolvedBoundaryIds G)
    (z : Phi4WTriplePrimeInverseCodomain G) {δ : {x // x ∈ z.2.1.elements}}
    (hδ : phi4WTriplePrime_inv_isForestImage z δ) {v : VertexId}
    (hv : v ∈ (stableLocalContractGraph (stableRecoveredForwardOccurrence hSt z hδ)).vertices) :
    (v ∈ (stableRecoveredForwardOccurrence hSt z hδ).γ.1.vertices
        ∧ v ∉ (stableRecoveredForwardOccurrence hSt z hδ).B.1.vertices)
      ∨ (∃ (γ : ResolvedFeynmanSubgraph G)
            (hγ : γ ∈ (phi4WTriplePrime_touchedOuterForest z δ).elements),
          v = phi4WTriplePrimeCanonicalSupply.starOf
              (stableLocalBoundaryCompletedGraph (stableRecoveredForwardOccurrence hSt z hδ).γ.1)
              (stableRecoveredForwardOccurrence hSt z hδ).B.1
              (stableInvInnerComponent hSt
                (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδ) γ hγ)) := by
  rw [stableLocalContractGraph, ResolvedAdmissibleSubgraph.contractWithStars_vertices,
    Finset.mem_union] at hv
  rcases hv with hsurv | hstar
  · rw [Finset.mem_sdiff] at hsurv
    exact Or.inl hsurv
  · rw [ResolvedAdmissibleSubgraph.mem_starVertices] at hstar
    obtain ⟨δ', hδ', hveq⟩ := hstar
    obtain ⟨γ, hγ, rfl⟩ :=
      stableInvRecoveredInnerForest_element_origin hSt
        (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδ) hδ'
    exact Or.inr ⟨γ, hγ, hveq.symm⟩

/-! ## Step 3 — τ action agreement on the visible vertices (the crux) -/

/-- **body-645b (Step 3, CRUX) — the two correcting permutations agree on every visible vertex.**  Survivors are
FIXED by both τ (`stableRemnantTau_fix` / `stableInvReconTau_fix`; the two survivor regions
`o.γ.1.vertices \ o.B.1.vertices` and `(recoveredParent I).vertices \ innerForest.vertices` are DEFEQ).  A star
`starOf (SLBCG o.γ.1) o.B.1 (innerComponent γ)` maps under `stableRemnantTau` to
`starOf G (stableSelectedOuter (recoveredResolved)) (stableRootRelativeInner o.γ.1 (innerComponent γ))`, and
under `stableInvReconTau` to `starOf G z.1.1 γ`; body-642 `rootRelativeInner_eq` and body-644
`stableSelectedOuter (recoveredResolved) = z.1.1` (SAME ambient `G`) identify the two targets.  NEVER asserts the
two permutations are globally equal. -/
theorem stableForwardInverse_tau_agree_on_localContract_vertices (hSt : StableResolvedBoundaryIds G)
    (z : Phi4WTriplePrimeInverseCodomain G) {δ : {x // x ∈ z.2.1.elements}}
    (hδ : phi4WTriplePrime_inv_isForestImage z δ) {v : VertexId}
    (hv : v ∈ (stableLocalContractGraph (stableRecoveredForwardOccurrence hSt z hδ)).vertices) :
    stableRemnantTau (stableRecoveredForwardOccurrence hSt z hδ) v
      = stableInvReconTau hSt (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδ) v := by
  rcases stableForwardInverse_localContract_vertex_cases hSt z hδ hv with hsurv | ⟨γ, hγ, rfl⟩
  · -- survivor: both τ fix it
    rw [stableRemnantTau_fix (stableRecoveredForwardOccurrence hSt z hδ)
      (Finset.mem_sdiff.mpr hsurv)]
    exact (stableInvReconTau_fix hSt
      (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδ)
      (Finset.mem_sdiff.mpr hsurv)).symm
  · -- star: align the two targets
    have hmem : stableInvInnerComponent hSt
        (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδ) γ hγ
        ∈ (stableRecoveredForwardOccurrence hSt z hδ).B.1.elements :=
      stableInvInnerComponent_mem' hSt
        (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδ) hγ
    have h1 : stableRemnantTau (stableRecoveredForwardOccurrence hSt z hδ)
          (phi4WTriplePrimeCanonicalSupply.starOf
            (stableLocalBoundaryCompletedGraph (stableRecoveredForwardOccurrence hSt z hδ).γ.1)
            (stableRecoveredForwardOccurrence hSt z hδ).B.1
            (stableInvInnerComponent hSt
              (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδ) γ hγ))
        = phi4WTriplePrimeCanonicalSupply.starOf G
            (stableSelectedOuter (stableRecoveredResolvedSplitChoice hSt z))
            (stableRootRelativeInner
              (phi4WTriplePrime_inv_recoveredParent
                (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδ))
              (stableInvInnerComponent hSt
                (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδ) γ hγ)) :=
      stableRemnantTau_map (stableRecoveredForwardOccurrence hSt z hδ)
        ⟨stableInvInnerComponent hSt
          (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδ) γ hγ, hmem⟩
    have h2 : stableInvReconTau hSt
          (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδ)
          (phi4WTriplePrimeCanonicalSupply.starOf
            (stableLocalBoundaryCompletedGraph (stableRecoveredForwardOccurrence hSt z hδ).γ.1)
            (stableRecoveredForwardOccurrence hSt z hδ).B.1
            (stableInvInnerComponent hSt
              (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδ) γ hγ))
        = phi4WTriplePrimeCanonicalSupply.starOf G z.1.1 γ :=
      stableInvReconTau_map hSt
        (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδ) ⟨γ, hγ⟩
    rw [h1, h2,
      stableInvInnerComponent_rootRelativeInner_eq hSt
        (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδ) hγ,
      stableSelectedOuter_recoveredSplitChoice hSt z]

/-! ## Step 4 — raw `mapPerm` congruence -/

/-- **body-645b (Step 4) — the two `mapPerm` images of the (shared) local contract graph coincide.**  The
underlying graph is aligned by body-645a's defeq anchor; Step 3 gives vertex-set agreement, the local-contract
edge-endpoint / leg-attachment support facts lift it to the edge / leg fields, and `edgeId` / `legId` / `sector`
/ multiplicity are `mapPerm`-structural.  A RAW `ResolvedFeynmanGraph` equality. -/
theorem stableForwardInverse_localContract_mapPerm_eq (hSt : StableResolvedBoundaryIds G)
    (z : Phi4WTriplePrimeInverseCodomain G) {δ : {x // x ∈ z.2.1.elements}}
    (hδ : phi4WTriplePrime_inv_isForestImage z δ) :
    (stableLocalContractGraph (stableRecoveredForwardOccurrence hSt z hδ)).mapPerm
        (stableRemnantTau (stableRecoveredForwardOccurrence hSt z hδ))
      = (stableInvLocalContractGraph hSt
          (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδ)).mapPerm
          (stableInvReconTau hSt (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδ)) := by
  rw [← stableInvLocalContractGraph_eq_stableLocalContractGraph hSt z hδ]
  apply resolvedGraph_mapPerm_congr_of_agree
  · intro v hv
    exact stableForwardInverse_tau_agree_on_localContract_vertices hSt z hδ hv
  · intro e he
    obtain ⟨hs, ht⟩ :=
      stableRemnant_localContract_edge_endpoints (stableRecoveredForwardOccurrence hSt z hδ) he
    exact ⟨stableForwardInverse_tau_agree_on_localContract_vertices hSt z hδ hs,
      stableForwardInverse_tau_agree_on_localContract_vertices hSt z hδ ht⟩
  · intro ℓ hℓ
    exact stableForwardInverse_tau_agree_on_localContract_vertices hSt z hδ
      (stableLocalContract_leg_attached (stableRecoveredForwardOccurrence hSt z hδ) hℓ)

/-! ## Step 5 — HEADLINE: the FOREST completion reconciliation -/

/-- **body-645b (Step 5, HEADLINE) — the FOREST completion reconciliation.**  The stable remnant of the recovered
forward occurrence, DECOMPLETED then RE-COMPLETED, equals the original star-touching target `δ.1` RE-COMPLETED —
a homogeneous, AMBIENT-FREE, RAW `ResolvedFeynmanGraph` equality (exact IDs / sectors / multiplicities).  Chains
body-635 `stableRemnant_contractTwice` → the Step-4 `mapPerm` congruence → body-645a `stableInvRecontraction_raw`.
The two correcting permutations are used ONLY through their per-point action; they are NEVER equated globally. -/
theorem stableForwardInverse_forest_completion_reconcile (hSt : StableResolvedBoundaryIds G)
    (z : Phi4WTriplePrimeInverseCodomain G) {δ : {x // x ∈ z.2.1.elements}}
    (hδ : phi4WTriplePrime_inv_isForestImage z δ) :
    stableLocalBoundaryCompletedGraph
        (stableRemnantComponent (stableRecoveredForwardOccurrence hSt z hδ))
      = stableLocalBoundaryCompletedGraph δ.1 := by
  rw [stableRemnant_contractTwice (stableRecoveredForwardOccurrence hSt z hδ),
    stableForwardInverse_localContract_mapPerm_eq hSt z hδ]
  exact stableInvRecontraction_raw hSt
    (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδ)

end GaugeGeometry.QFT.Combinatorial
