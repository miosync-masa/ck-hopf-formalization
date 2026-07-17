import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocTouchedLegLiftDatum

/-!
# R-6c-body-327 — the single-component `toInner` API (PROVED, value-only)

Three-hundred-and-twenty-seventh genuine-body step — Front-1 M3, the single-component retype `toInner` and its
round-trip / CD / injectivity / disjointness (the value-level foundation; the Finset `innerRaw` + M3 element equality is
body-328).  `toInner A` re-types a touched outer component `A` (data unchanged) into the custom localized parent, using
the body-326 datum containments.

## Banked here

* `toInner` — `A ↦ ResolvedFeynmanSubgraph (localizedParentWithTouchedLegs z δ datum hE hL).toResolvedFeynmanGraph`, data
  `:= A`'s; subset proofs are the three body-326 containments; `edges_supported`/`legs_supported` are `A`'s (defeq).
* `promote_toInner` — `(localizedParentWithTouchedLegs …).promote (toInner … A) = A.1` (ext + three `rfl`; `promote`
  keeps data).
* `toInner_isConnectedDivergent` — from `z.1.1.isConnectedDivergent A.1` (a touched component is a `z.1.1` component) +
  same-data ambient transport (`IsAmbientInvariantDivergence`, M2a pattern).
* `toInner_injective` — from `promote_toInner` (left inverse) + `Subtype.ext`.
* `toInner_disjoint` — `Disjoint = vertex-disjoint`, so `z.1.1.pairwiseDisjoint` transports (same vertices).

These feed body-328's `innerRaw = (touchedOuterComponents z δ).attach.image toInner` (`ofElements` with CD + pairwise) and
M3 `(promote parent innerRaw).elements = touchedOuterComponents z δ`.

Per the HALT: only the single-component `toInner` API is proved; `innerRaw` / M3 / the nested CD datum / D4 are NOT entered;
`innerRaw` is NOT lifted to `ForestIdx`; no carrier membership; no parent CD; the M3 element equality is body-328; no
facade, no flat term, no `forgetHopf`.  STATUS: M3/D4 remain proof residual.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}
  (z : ForestBlockCodType D G)
  (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
  (datum : ResolvedTouchedLegLiftDatum z δ)
  (hE : ∀ e ∈ G.internalEdges, e.source ∈ G.vertices ∧ e.target ∈ G.vertices)
  (hL : ∀ ℓ ∈ G.externalLegs, ℓ.attachedTo ∈ G.vertices)

set_option linter.unusedSectionVars false

/-- **R-6c-body-327 — the single-component retype.**  A touched outer component `A`, data unchanged, as a subgraph of the
custom localized parent (the three subset proofs are the body-326 containments). -/
noncomputable def toInner (A : {x : ResolvedFeynmanSubgraph G // x ∈ touchedOuterComponents z δ}) :
    ResolvedFeynmanSubgraph (localizedParentWithTouchedLegs z δ datum hE hL).toResolvedFeynmanGraph where
  vertices := A.1.vertices
  internalEdges := A.1.internalEdges
  externalLegs := A.1.externalLegs
  vertices_subset := touchedLegs_component_vertices_subset (datum := datum) (hE := hE) (hL := hL) A.2
  internalEdges_le := touchedLegs_component_internalEdges_le (datum := datum) (hE := hE) (hL := hL) A.2
  externalLegs_le := touchedLegs_component_externalLegs_le (datum := datum) (hE := hE) (hL := hL) A.2
  edges_supported := A.1.edges_supported
  legs_supported := A.1.legs_supported

/-- **R-6c-body-327 — the promote round-trip.**  Promoting the retype recovers the original component. -/
theorem promote_toInner (A : {x : ResolvedFeynmanSubgraph G // x ∈ touchedOuterComponents z δ}) :
    (localizedParentWithTouchedLegs z δ datum hE hL).promote (toInner z δ datum hE hL A) = A.1 :=
  ResolvedFeynmanSubgraph.ext rfl rfl rfl

/-- **R-6c-body-327 — the retype is connected-divergent.**  A touched component is a `z.1.1` component (CD), and
`toInner` keeps its data, so CD transports by ambient-invariance. -/
theorem toInner_isConnectedDivergent (A : {x : ResolvedFeynmanSubgraph G // x ∈ touchedOuterComponents z δ}) :
    (toInner z δ datum hE hL A).forget.IsConnectedDivergent := by
  obtain ⟨hC, hPI, hDiv⟩ :=
    z.1.1.isConnectedDivergent A.1 (mem_touchedOuterComponents.mp A.2).1
  refine ⟨hC, hPI, ?_⟩
  have hdeg : DivergenceMeasure.degree (toInner z δ datum hE hL A).forget
      = DivergenceMeasure.degree A.1.forget := by
    rw [← IsAmbientInvariantDivergence.degree_self_eq (toInner z δ datum hE hL A).forget,
      ← IsAmbientInvariantDivergence.degree_self_eq A.1.forget]
    rfl
  show (0 : ℤ) ≤ DivergenceMeasure.degree (toInner z δ datum hE hL A).forget
  rw [hdeg]; exact hDiv

/-- **R-6c-body-327 — `toInner` is injective** (left inverse `promote_toInner`). -/
theorem toInner_injective : Function.Injective (toInner z δ datum hE hL) := by
  intro A A' h
  apply Subtype.ext
  have hp := congrArg (localizedParentWithTouchedLegs z δ datum hE hL).promote h
  rwa [promote_toInner, promote_toInner] at hp

/-- **R-6c-body-327 — distinct retypes are disjoint** (`z.1.1`'s pairwise disjointness, same vertices). -/
theorem toInner_disjoint {A A' : {x : ResolvedFeynmanSubgraph G // x ∈ touchedOuterComponents z δ}} (hne : A ≠ A') :
    (toInner z δ datum hE hL A).Disjoint (toInner z δ datum hE hL A') :=
  z.1.1.pairwiseDisjoint (mem_touchedOuterComponents.mp A.2).1
    (mem_touchedOuterComponents.mp A'.2).1 (fun h => hne (Subtype.ext h))

end GaugeGeometry.QFT.Combinatorial
