import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaTouchedStarDescent
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaParentArchitectureAudit
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRetargetForget
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocContractForget
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecontractSection
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecontractVertexEq
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocLocalizedParentCD
import GaugeGeometry.QFT.HopfAlgebra.ResolvedCoproductIndex
import GaugeGeometry.QFT.HopfAlgebra.Coassoc

/-!
# R-6c-body-555 — Residual 2 of the Parent-divergence reflection: the INTRINSIC remainder graph equality (PROVED)

Five-hundred-and-fifty-fifth genuine-body step — **Residual 2** of the Parent-divergence reflection (body-553, Step 6).
It closes the "remainder = δ" alignment as an **intrinsic graph equality** on the flat carrier:

```text
(admissibleSubgraphQuotientRemainderSubgraph
    (innerRaw z δ.1 …).forget
    (canonicalLegSaturatedFlatTouchedInnerStar z δ)
    (FeynmanSubgraph.self ((canonicalLegSaturatedParentForget z δ).toFeynmanGraph) hH)).toFeynmanGraph
  = δ.1.forget.toFeynmanGraph
```

★It deliberately does **not** force the literal cross-ambient `remainder = δ.forget` (those live over different ambients);
it is the honest `.toFeynmanGraph` intrinsic equality, with **no** dependent `cast`/`HEq` introduced up front.★

★Circularity RED-LINE (continues from 554): this is a **Parent-ELIMINATION** step — **no `R`, `R.Core`, `Parent`, or
Parent-dependent `Core`** appears in any signature or body.  The canonical `innerRaw` nonemptiness / positive-edge / star
facts are replayed directly from the Parent-FREE `canonicalLegSaturatedCarrierProperProvider.carrier_isProperForest` and
body-554's `canonicalLegSaturatedFlatTouchedInnerStar` owner (no fresh flat star is issued).★

## Steps closed

* **Step 1 — arbitrary-star forget coherence** (`forget_contractWithStarsOf`): the generic-star generalisation of body-422
  `forget_contractWithStars_resolvedStar`, keyed to an *arbitrary* component star via body-554's `resolvedStarOnForgetOf`,
  weakened from `IsProperForest` to `HasNonemptyComponents`.  Re-keys body-421's `retargetVertex_forget_eq` /
  `starVertices_forget_eq` to the generic star (`retargetVertex_forget_eqOf` / `starVertices_forget_eqOf`), using only
  `HasNonemptyComponents` + `resolvedStarOnForgetOf_spec` (NO full `IsProperForest`, NO global `forget` injectivity).
* **Step 2 — resolved recontraction = δ graph** (`canonicalLegSaturated_innerRaw_contract_eq_deltaGraph`, PARENT-FREE):
  fed the body-330 recontraction projections `recontract_innerRaw_{vertices,internalEdges,externalLegs}` with Parent-free
  hypotheses (`hConn` from `z.2.1.isConnectedDivergent`, `hPos` from the Parent-free carrier proper-forest's
  positive-edge conjunct, `Fstar := canonicalLegSaturatedStarFacts`).
* **Step 3 — flat contraction = δ intrinsic** (`canonicalLegSaturated_innerRawForget_contract_eq_deltaGraph`):
  Step 1 (reusing body-554's flat star owner) + `congr`/`forget` of Step 2 + the rfl-level `forget_toFeynmanGraph`
  commutation.
* **Step 4 — generic self-remainder = self-of-contraction** (`admissibleSubgraphQuotientRemainder_self_eq_self`):
  the remainder of the *whole* graph is the self-subgraph of the contraction; externalLegs/internalEdges by `rfl`,
  vertices by the image/star-vertex split (survivors are fixed, component vertices hit their star, every star hit by
  `HasNonemptyComponents`).
* **Step 5 — final composition** (`canonicalLegSaturated_quotientRemainder_toFeynmanGraph_eq_delta`): Step 4 at the
  canonical parent (fed body-553's `legSaturated_innerRawForget_isPairwiseDisjoint` +
  `legSaturated_innerRawForget_hasNonemptyComponents` on body-554's Parent-free resolved nonemptiness), then
  `(self K).toFeynmanGraph = K` (rfl) + Step 3.

## Scoreboard

```text
arbitrary-star forget coherence           PROVED (HasNonemptyComponents; generic star)
resolved recontraction = δ graph          PARENT-FREE (body-330 projections)
flat contraction = δ intrinsic            PROVED (Step 1 ∘ Step 2 ∘ forget_toFeynmanGraph)
generic self-remainder = self-of-contract PROVED
final intrinsic remainder = δ graph       PROVED  ★target reached (intrinsic .toFeynmanGraph)★
reflection applied / remainder divergence NOT (body-556)
circularity guard (no Parent-derived Core) HELD
```

Per the HALT/guards: NO `R` / `R.Core` / `Parent` / Parent-dependent Core in any signature or body; reflection NOT
applied; remainder divergence NOT proved; no `parentDivergent` / `Parent` supply; the target is the INTRINSIC
`.toFeynmanGraph` equality (no forced cross-ambient equality, no `HEq`/`cast` up front); body-554's flat star owner is
reused (no fresh flat star); NO global `forget` injectivity; NO new class/structure/instance; old private flat theorems
untouched.  No facade, no `sorry`/`admit`.
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
set_option maxHeartbeats 3200000

/-! ## Local extensionality helpers (carrier-field determinacy). -/

/-- A flat subgraph is determined by its carrier fields (proof-valued fields are proof-irrelevant). -/
private theorem feynmanSubgraph_ext {G : FeynmanGraph} {γ₁ γ₂ : FeynmanSubgraph G}
    (hv : γ₁.vertices = γ₂.vertices) (hi : γ₁.internalEdges = γ₂.internalEdges)
    (he : γ₁.externalLegs = γ₂.externalLegs) : γ₁ = γ₂ := by
  cases γ₁; cases γ₂; cases hv; cases hi; cases he; rfl

/-- A resolved Feynman graph is determined by its vertices / internal edges / external legs. -/
private theorem resolvedGraph_ext {G₁ G₂ : ResolvedFeynmanGraph}
    (hv : G₁.vertices = G₂.vertices) (hi : G₁.internalEdges = G₂.internalEdges)
    (he : G₁.externalLegs = G₂.externalLegs) : G₁ = G₂ := by
  cases G₁; cases G₂; cases hv; cases hi; cases he; rfl

/-! ## Step 1 — arbitrary-star forget coherence. -/

/-- **R-6c-body-555 (Step 1a) — the retarget maps agree, generic star.**  Generic-star re-key of body-421's
`retargetVertex_forget_eq`: `HasNonemptyComponents` (via body-554's `resolvedStarOnForgetOf_spec`) replaces
`IsProperForest`.  In-forest via the `componentAt` correspondence; off-forest both are the identity. -/
theorem retargetVertex_forget_eqOf {G : ResolvedFeynmanGraph} (A : ResolvedAdmissibleSubgraph G)
    (star : ResolvedFeynmanSubgraph G → VertexId) (hne : A.HasNonemptyComponents) (v : VertexId) :
    A.forget.retargetVertex (resolvedStarOnForgetOf A star) v = A.retargetVertex star v := by
  by_cases hv : v ∈ A.vertices
  · have hv' : v ∈ A.forget.vertices := by rw [forget_vertices_eq]; exact hv
    rw [ResolvedAdmissibleSubgraph.retargetVertex,
        ResolvedAdmissibleSubgraph.componentAt?_of_mem _ hv,
        AdmissibleSubgraph.retargetVertex, AdmissibleSubgraph.componentAt?_of_mem _ hv']
    have hcomp : A.forget.componentAt hv' = (A.componentAt hv).forget := by
      apply AdmissibleSubgraph.componentAt_eq_of_mem_vertices (forget_isPairwiseDisjoint A)
        (Finset.mem_image_of_mem _ (A.componentAt_mem hv))
      rw [ResolvedFeynmanSubgraph.forget_vertices]; exact A.componentAt_vertex_mem hv
    show resolvedStarOnForgetOf A star (A.forget.componentAt hv') = _
    rw [hcomp, resolvedStarOnForgetOf_spec A star hne (A.componentAt_mem hv)]
  · have hv' : v ∉ A.forget.vertices := by rw [forget_vertices_eq]; exact hv
    rw [ResolvedAdmissibleSubgraph.retargetVertex_of_not_mem _ _ hv,
        AdmissibleSubgraph.retargetVertex_of_not_mem _ _ hv']

/-- **R-6c-body-555 (Step 1b) — the star-vertex sets agree, generic star.**  Generic-star re-key of body-421's
`starVertices_forget_eq`. -/
theorem starVertices_forget_eqOf {G : ResolvedFeynmanGraph} (A : ResolvedAdmissibleSubgraph G)
    (star : ResolvedFeynmanSubgraph G → VertexId) (hne : A.HasNonemptyComponents) :
    A.forget.starVertices (resolvedStarOnForgetOf A star) = A.starVertices star := by
  unfold AdmissibleSubgraph.starVertices ResolvedAdmissibleSubgraph.starVertices
  rw [ResolvedAdmissibleSubgraph.forget_elements, Finset.image_image]
  exact Finset.image_congr (fun γ hγ => resolvedStarOnForgetOf_spec A star hne hγ)

/-- **R-6c-body-555 (Step 1) ∎ — arbitrary-star forget/contraction commutativity.**  Generic-star generalisation of
body-422 `forget_contractWithStars_resolvedStar`: forgetting the resolved star-contraction is the FLAT contraction of the
forgotten forest with the descended star, for an *arbitrary* component `star`, from `HasNonemptyComponents` alone (no
`IsProperForest`, no global `forget` injectivity). -/
theorem forget_contractWithStarsOf {H : ResolvedFeynmanGraph} (A : ResolvedAdmissibleSubgraph H)
    (star : ResolvedFeynmanSubgraph H → VertexId) (hne : A.HasNonemptyComponents) :
    (A.contractWithStars star).forget = A.forget.contractWithStars (resolvedStarOnForgetOf A star) := by
  rw [ResolvedAdmissibleSubgraph.forget_contractWithStars]
  have hv : (H.vertices \ A.vertices) ∪ A.starVertices star
      = (H.forget.vertices \ A.forget.vertices) ∪ A.forget.starVertices (resolvedStarOnForgetOf A star) := by
    rw [forget_vertices_eq, starVertices_forget_eqOf A star hne]
    rfl
  have hi : (A.complementEdges.map ResolvedFeynmanEdge.forget).map
        (fun e => ({ source := A.retargetVertex star e.source,
                     target := A.retargetVertex star e.target, sector := e.sector } : FeynmanEdge))
      = A.forget.complementEdges.map (A.forget.retargetEdge (resolvedStarOnForgetOf A star)) := by
    rw [forget_complementEdges_eq A hne]
    simp only [Multiset.map_map]
    refine Multiset.map_congr rfl (fun e _ => ?_)
    simp only [Function.comp_apply, AdmissibleSubgraph.retargetEdge, ResolvedFeynmanEdge.forget,
      retargetVertex_forget_eqOf A star hne]
  have he : (H.externalLegs.map ResolvedExternalLeg.forget).map
        (fun l => ({ attachedTo := A.retargetVertex star l.attachedTo,
                     sector := l.sector } : ExternalLeg))
      = H.forget.externalLegs.map (A.forget.retargetExternalLeg (resolvedStarOnForgetOf A star)) := by
    rw [show H.forget.externalLegs = H.externalLegs.map ResolvedExternalLeg.forget from rfl]
    simp only [Multiset.map_map]
    refine Multiset.map_congr rfl (fun l _ => ?_)
    simp only [Function.comp_apply, AdmissibleSubgraph.retargetExternalLeg, ResolvedExternalLeg.forget,
      retargetVertex_forget_eqOf A star hne]
  exact congr (congr (congrArg FeynmanGraph.mk hv) hi) he

/-! ## Step 2 — resolved canonical recontraction = δ graph (PARENT-FREE). -/

/-- **R-6c-body-555 (Step 2) — resolved recontraction = δ's intrinsic graph, PARENT-FREE.**  Fed the body-330
recontraction projections with Parent-free hypotheses: `hConn` from the resolved forest's `isConnectedDivergent`
accessor, `hPos` from the Parent-FREE carrier proper-forest's positive-internal-edges conjunct, `Fstar :=
canonicalLegSaturatedStarFacts`.  ★No `R`/`Core`/`Parent`.★ -/
theorem canonicalLegSaturated_innerRaw_contract_eq_deltaGraph {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalLegSaturatedCarrierProperSupply.toData G)
    (δ : {x : ResolvedFeynmanSubgraph
        (z.1.1.contractWithStars (canonicalLegSaturatedCarrierProperSupply.toData.starOf G z.1.1)) //
          x ∈ forestDomain z}) :
    (innerRaw z δ.1
        (touchedLegLiftDatum_of_complete z δ.1 (canonicalLegSaturated_touchedLegComplete z δ))
        (liveAmbient_edges_supported ambientSupportOfW'' z)
        (liveAmbient_legs_supported ambientSupportOfW'' z)).contractWithStars
      (touchedInnerStarTotal z δ.1
        (touchedLegLiftDatum_of_complete z δ.1 (canonicalLegSaturated_touchedLegComplete z δ))
        (liveAmbient_edges_supported ambientSupportOfW'' z)
        (liveAmbient_legs_supported ambientSupportOfW'' z))
      = δ.1.toResolvedFeynmanGraph := by
  have hConn : (touchedLocalComponent z δ.1).forget.IsConnected :=
    (touchedLocalComponent_isConnectedDivergent z δ.1
      (z.2.1.isConnectedDivergent δ.1 (Finset.mem_filter.mp δ.2).1)).1
  have hPos : 0 < (touchedLocalComponent z δ.1).internalEdges.card := by
    rw [touchedLocalComponent_internalEdges]
    exact (canonicalLegSaturatedCarrierProperProvider.carrier_isProperForest _ z.2.1 z.2.2).2.2.2.1
      δ.1 (Finset.mem_filter.mp δ.2).1
  refine resolvedGraph_ext ?_ ?_ ?_
  · exact recontract_innerRaw_vertices z δ.1
        (touchedLegLiftDatum_of_complete z δ.1 (canonicalLegSaturated_touchedLegComplete z δ))
        (liveAmbient_edges_supported ambientSupportOfW'' z)
        (liveAmbient_legs_supported ambientSupportOfW'' z) canonicalLegSaturatedStarFacts hConn hPos
  · exact recontract_innerRaw_internalEdges z δ.1
        (touchedLegLiftDatum_of_complete z δ.1 (canonicalLegSaturated_touchedLegComplete z δ))
        (liveAmbient_edges_supported ambientSupportOfW'' z)
        (liveAmbient_legs_supported ambientSupportOfW'' z)
  · exact recontract_innerRaw_externalLegs z δ.1
        (touchedLegLiftDatum_of_complete z δ.1 (canonicalLegSaturated_touchedLegComplete z δ))
        (liveAmbient_edges_supported ambientSupportOfW'' z)
        (liveAmbient_legs_supported ambientSupportOfW'' z)

/-! ## Step 3 — flat contraction = δ intrinsic graph. -/

/-- **R-6c-body-555 (Step 3) — flat contraction of `(innerRaw …).forget` with body-554's flat star = `δ`'s intrinsic
graph.**  Step 1 (reusing `canonicalLegSaturatedFlatTouchedInnerStar` unchanged) + `forget` of Step 2 + the rfl-level
`forget_toFeynmanGraph`. -/
theorem canonicalLegSaturated_innerRawForget_contract_eq_deltaGraph {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalLegSaturatedCarrierProperSupply.toData G)
    (δ : {x : ResolvedFeynmanSubgraph
        (z.1.1.contractWithStars (canonicalLegSaturatedCarrierProperSupply.toData.starOf G z.1.1)) //
          x ∈ forestDomain z}) :
    (innerRaw z δ.1
        (touchedLegLiftDatum_of_complete z δ.1 (canonicalLegSaturated_touchedLegComplete z δ))
        (liveAmbient_edges_supported ambientSupportOfW'' z)
        (liveAmbient_legs_supported ambientSupportOfW'' z)).forget.contractWithStars
      (canonicalLegSaturatedFlatTouchedInnerStar z δ)
      = δ.1.forget.toFeynmanGraph := by
  have hne := canonicalLegSaturated_innerRaw_hasNonemptyComponents z δ
  have h1 := forget_contractWithStarsOf
    (innerRaw z δ.1
      (touchedLegLiftDatum_of_complete z δ.1 (canonicalLegSaturated_touchedLegComplete z δ))
      (liveAmbient_edges_supported ambientSupportOfW'' z)
      (liveAmbient_legs_supported ambientSupportOfW'' z))
    (touchedInnerStarTotal z δ.1
      (touchedLegLiftDatum_of_complete z δ.1 (canonicalLegSaturated_touchedLegComplete z δ))
      (liveAmbient_edges_supported ambientSupportOfW'' z)
      (liveAmbient_legs_supported ambientSupportOfW'' z)) hne
  unfold canonicalLegSaturatedFlatTouchedInnerStar
  rw [← h1, canonicalLegSaturated_innerRaw_contract_eq_deltaGraph z δ]
  exact (ResolvedFeynmanSubgraph.forget_toFeynmanGraph δ.1).symm

/-! ## Step 4 — the generic self-remainder theorem. -/

/-- **R-6c-body-555 (Step 4) — the quotient remainder of the *whole* graph is the self-subgraph of the contraction.**
externalLegs / internalEdges by `rfl`; vertices by the image/star-vertex split (survivors fixed via
`retargetVertex_of_not_mem`, component vertices hit their star via `retargetVertex_of_mem_component`, and every star is
covered because `HasNonemptyComponents` gives each component a vertex).  Freshness is NOT required. -/
theorem admissibleSubgraphQuotientRemainder_self_eq_self {H : FeynmanGraph}
    (A : AdmissibleSubgraph H) (hDisj : A.IsPairwiseDisjoint) (hCompNE : A.HasNonemptyComponents)
    (star : FeynmanSubgraph H → VertexId) (hH : H.WellFormed) :
    admissibleSubgraphQuotientRemainderSubgraph A star (FeynmanSubgraph.self H hH)
      = FeynmanSubgraph.self (A.contractWithStars star) (A.contractWithStars_wellFormed star hH) := by
  refine feynmanSubgraph_ext ?_ ?_ ?_
  · show H.vertices.image (A.retargetVertex star)
        = (H.vertices \ A.vertices) ∪ A.starVertices star
    ext v
    simp only [Finset.mem_image, Finset.mem_union, Finset.mem_sdiff,
      AdmissibleSubgraph.mem_starVertices]
    constructor
    · rintro ⟨w, hwH, rfl⟩
      by_cases hwA : w ∈ A.vertices
      · right
        rw [AdmissibleSubgraph.mem_vertices] at hwA
        obtain ⟨γ, hγ, hwγ⟩ := hwA
        exact ⟨γ, hγ,
          (AdmissibleSubgraph.retargetVertex_of_mem_component hDisj star hγ hwγ).symm⟩
      · left
        rw [AdmissibleSubgraph.retargetVertex_of_not_mem A star hwA]
        exact ⟨hwH, hwA⟩
    · rintro (⟨hvH, hvA⟩ | ⟨γ, hγ, rfl⟩)
      · exact ⟨v, hvH, AdmissibleSubgraph.retargetVertex_of_not_mem A star hvA⟩
      · have hγne : γ.IsNonempty := hCompNE γ hγ
        have hγverts : γ.vertices.Nonempty := by
          unfold FeynmanSubgraph.IsNonempty FeynmanSubgraph.vertexCount at hγne
          exact Finset.card_pos.mp hγne
        obtain ⟨w, hwγ⟩ := hγverts
        exact ⟨w, γ.vertices_subset hwγ,
          AdmissibleSubgraph.retargetVertex_of_mem_component hDisj star hγ hwγ⟩
  · rfl
  · rfl

/-! ## Step 5 — final intrinsic remainder equality (★target★). -/

/-- **R-6c-body-555 (Step 5) ∎ — Residual 2 closed as the intrinsic remainder graph equality.**  The flat quotient
remainder of the canonical `W″` parent's self-subgraph, under body-554's flat touched-inner star, has intrinsic graph
`δ`'s flat graph: `remainder.toFeynmanGraph = δ.1.forget.toFeynmanGraph`.  Step 4 at the canonical parent (fed body-553's
Parent-free disjoint / nonempty premises on body-554's Parent-free resolved nonemptiness) + `(self K).toFeynmanGraph = K`
(rfl) + Step 3.  ★NO `Parent`/`Core`/`R` in the type; NO `HEq`/`cast`; NO literal cross-ambient equality.★ -/
theorem canonicalLegSaturated_quotientRemainder_toFeynmanGraph_eq_delta {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalLegSaturatedCarrierProperSupply.toData G)
    (δ : {x : ResolvedFeynmanSubgraph
        (z.1.1.contractWithStars (canonicalLegSaturatedCarrierProperSupply.toData.starOf G z.1.1)) //
          x ∈ forestDomain z})
    (hH : ((canonicalLegSaturatedParentForget z δ).toFeynmanGraph).WellFormed) :
    (admissibleSubgraphQuotientRemainderSubgraph
        (innerRaw z δ.1
            (touchedLegLiftDatum_of_complete z δ.1 (canonicalLegSaturated_touchedLegComplete z δ))
            (liveAmbient_edges_supported ambientSupportOfW'' z)
            (liveAmbient_legs_supported ambientSupportOfW'' z)).forget
        (canonicalLegSaturatedFlatTouchedInnerStar z δ)
        (FeynmanSubgraph.self ((canonicalLegSaturatedParentForget z δ).toFeynmanGraph) hH)).toFeynmanGraph
      = δ.1.forget.toFeynmanGraph := by
  have h4 := admissibleSubgraphQuotientRemainder_self_eq_self
        (H := (canonicalLegSaturatedParentForget z δ).toFeynmanGraph)
        (innerRaw z δ.1
            (touchedLegLiftDatum_of_complete z δ.1 (canonicalLegSaturated_touchedLegComplete z δ))
            (liveAmbient_edges_supported ambientSupportOfW'' z)
            (liveAmbient_legs_supported ambientSupportOfW'' z)).forget
        (legSaturated_innerRawForget_isPairwiseDisjoint z δ.1
          (touchedLegLiftDatum_of_complete z δ.1 (canonicalLegSaturated_touchedLegComplete z δ))
          (liveAmbient_edges_supported ambientSupportOfW'' z)
          (liveAmbient_legs_supported ambientSupportOfW'' z))
        (legSaturated_innerRawForget_hasNonemptyComponents z δ.1
          (touchedLegLiftDatum_of_complete z δ.1 (canonicalLegSaturated_touchedLegComplete z δ))
          (liveAmbient_edges_supported ambientSupportOfW'' z)
          (liveAmbient_legs_supported ambientSupportOfW'' z)
          (canonicalLegSaturated_innerRaw_hasNonemptyComponents z δ))
        (canonicalLegSaturatedFlatTouchedInnerStar z δ) hH
  refine (congrArg FeynmanSubgraph.toFeynmanGraph h4).trans ?_
  show (innerRaw z δ.1
        (touchedLegLiftDatum_of_complete z δ.1 (canonicalLegSaturated_touchedLegComplete z δ))
        (liveAmbient_edges_supported ambientSupportOfW'' z)
        (liveAmbient_legs_supported ambientSupportOfW'' z)).forget.contractWithStars
      (canonicalLegSaturatedFlatTouchedInnerStar z δ)
      = δ.1.forget.toFeynmanGraph
  exact canonicalLegSaturated_innerRawForget_contract_eq_deltaGraph z δ

end GaugeGeometry.QFT.Combinatorial
