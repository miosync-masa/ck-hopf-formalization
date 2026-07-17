import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocTouchedLegCompletenessAudit

/-!
# R-6c-body-326 — the touched-leg-lift datum + the custom localized parent (PROVED, value-only)

Three-hundred-and-twenty-sixth genuine-body step — Front-1 route (i): the coherent leg-lift datum (the concrete
strengthened preimage, NOT just a `Prop`) and the custom localized parent that uses it.  Because the base
`quotientLegPreimage` is an arbitrary `Classical.choose` (body-325 verdict), a bare `δ-leg-completeness : Prop` is
insufficient — the datum must CARRY the actual preimage multiset `legs` used, with the touched lower bound.

## The datum (structural CK well-formedness layer)

```lean
structure ResolvedTouchedLegLiftDatum z δ where
  legs       : Multiset ResolvedExternalLeg
  legs_le    : legs ≤ G.externalLegs
  map_eq     : legs.map ((touchedOuterForest z δ).retargetExternalLeg (D.starOf G z.1.1))
                 = (touchedLocalComponent z δ).externalLegs
  touched_le : (touchedOuterForest z δ).externalLegs ≤ legs
```

`map_eq` (a genuine leg-preimage, occurrence-faithful) + `touched_le` (the lower bound the base `.choose` cannot give) are
the structural CK-subgraph facts.  This is a MODEL DATUM (the concrete carrier's quotient components are leg-complete),
NOT derivable abstractly (body-325).

## The custom parent (value-only)

`localizedParentWithTouchedLegs z δ datum hE hL` re-implements `parentOfQuotient` with `Aout := touchedOuterForest z δ`,
`δ := touchedLocalComponent z δ`, but `externalLegs := datum.legs` (and the vertices leg-disjunct over `datum.legs`).  Its
vertices/internalEdges/edge-support proofs are `parentOfQuotient`'s verbatim (legs-independent); only `externalLegs_le`
(`datum.legs_le`) and `legs_supported` (via `datum.legs`) use the datum.

## The three toInner containments (for body-327)

* `touchedLegs_component_vertices_subset` — `A.vertices ⊆ parent.vertices` (first filter disjunct).
* `touchedLegs_component_internalEdges_le` — `A.internalEdges ≤ parent.internalEdges` (`single_le_sum` + `le_add_right`).
* `touchedLegs_component_externalLegs_le` — `A.externalLegs ≤ parent.externalLegs = datum.legs`
  (`A.externalLegs ≤ touchedOuterForest.externalLegs` via `single_le_sum`, then `datum.touched_le`) — the leg containment
  route A' needed, now available FROM the datum.

## Layer separation (per the design)

`legLift` = structural CK subgraph well-formedness (leg preimage + lower bound).  The parent CD (M2b) is a SEPARATE
power-counting/de-contraction datum, to be nested as `ResolvedTouchedDecontractionDatum` with
`parentCD : (localizedParentWithTouchedLegs …).forget.IsConnectedDivergent` (body-327+, when the parent is fixed).

Per the HALT: only the datum + custom parent + three containments are built; `toInner` / `innerRaw` / M3 / the nested CD
datum / D4 are NOT entered; the base `Classical.choose` is NOT edited (the strong witness is a downstream honest
interface); no facade, no flat term, no `forgetHopf`.  STATUS: M3/D4 remain proof residual — the outer-mixing geometry is
NOT yet fully floored.
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

/-- **R-6c-body-326 — membership in an admissible subgraph's internal edges** (public re-statement of the
`private` `resolvedAdmissible_mem_internalEdges`, needed downstream). -/
theorem resolvedAdmissible_mem_internalEdges' {G : ResolvedFeynmanGraph}
    {A : ResolvedAdmissibleSubgraph G} {e : ResolvedFeynmanEdge} :
    e ∈ A.internalEdges ↔ ∃ γ ∈ A.elements, e ∈ γ.internalEdges := by
  classical
  unfold ResolvedAdmissibleSubgraph.internalEdges
  induction A.elements using Finset.induction_on with
  | empty => simp
  | insert γ s hγs ih => simp [Finset.sum_insert, hγs, ih, Multiset.mem_add]

/-- **R-6c-body-326 — the touched-leg-lift datum.**  The coherent strengthened leg preimage (the concrete `legs` used,
with the touched lower bound) — a structural CK-subgraph model datum. -/
structure ResolvedTouchedLegLiftDatum {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))) where
  /-- The chosen external-leg preimage in `G`. -/
  legs : Multiset ResolvedExternalLeg
  /-- The preimage is a submultiset of `G`'s external legs. -/
  legs_le : legs ≤ G.externalLegs
  /-- Retargeting the preimage recovers the quotient component's external legs (occurrence-faithful). -/
  map_eq : legs.map ((touchedOuterForest z δ).retargetExternalLeg (D.starOf G z.1.1))
    = (touchedLocalComponent z δ).externalLegs
  /-- The touched forest's own external legs are contained in the preimage (the base `.choose` cannot give this). -/
  touched_le : (touchedOuterForest z δ).externalLegs ≤ legs

/-- **R-6c-body-326 — the custom localized parent** using the datum's leg preimage (value-only). -/
noncomputable def localizedParentWithTouchedLegs {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
    (datum : ResolvedTouchedLegLiftDatum z δ)
    (hE : ∀ e ∈ G.internalEdges, e.source ∈ G.vertices ∧ e.target ∈ G.vertices)
    (hL : ∀ ℓ ∈ G.externalLegs, ℓ.attachedTo ∈ G.vertices) :
    ResolvedFeynmanSubgraph G where
  vertices := G.vertices.filter (fun v =>
    v ∈ (touchedOuterForest z δ).vertices ∨
    (∃ e ∈ quotientEdgePreimage (touchedOuterForest z δ) (D.starOf G z.1.1)
        (touchedLocalComponent z δ), e.source = v ∨ e.target = v) ∨
    (∃ ℓ ∈ datum.legs, ℓ.attachedTo = v))
  internalEdges := (touchedOuterForest z δ).internalEdges
    + quotientEdgePreimage (touchedOuterForest z δ) (D.starOf G z.1.1) (touchedLocalComponent z δ)
  externalLegs := datum.legs
  vertices_subset := Finset.filter_subset _ _
  internalEdges_le := by
    have hle : (touchedOuterForest z δ).internalEdges ≤ G.internalEdges :=
      resolvedAdmissibleSubgraph_internalEdges_le_of_pairwise _
        (touchedOuterForest z δ).isPairwiseDisjoint
    calc (touchedOuterForest z δ).internalEdges
          + quotientEdgePreimage (touchedOuterForest z δ) (D.starOf G z.1.1) (touchedLocalComponent z δ)
        ≤ (touchedOuterForest z δ).internalEdges + (touchedOuterForest z δ).complementEdges := by
          gcongr; exact quotientEdgePreimage_le _ _ _
      _ = (touchedOuterForest z δ).internalEdges
            + (G.internalEdges - (touchedOuterForest z δ).internalEdges) := by
          rw [ResolvedAdmissibleSubgraph.complementEdges]
      _ = G.internalEdges := add_tsub_cancel_of_le hle
  externalLegs_le := datum.legs_le
  edges_supported := by
    intro e he
    rw [Multiset.mem_add] at he
    rcases he with heA | heM
    · obtain ⟨γ, hγ, heγ⟩ := resolvedAdmissible_mem_internalEdges'.mp heA
      obtain ⟨hs, ht⟩ := γ.edges_supported e heγ
      have heG : e ∈ G.internalEdges := Multiset.mem_of_le
        (resolvedAdmissibleSubgraph_internalEdges_le_of_pairwise _
          (touchedOuterForest z δ).isPairwiseDisjoint) heA
      obtain ⟨hsG, htG⟩ := hE e heG
      exact ⟨Finset.mem_filter.mpr ⟨hsG, Or.inl (ResolvedAdmissibleSubgraph.mem_vertices.mpr
              ⟨γ, hγ, hs⟩)⟩,
             Finset.mem_filter.mpr ⟨htG, Or.inl (ResolvedAdmissibleSubgraph.mem_vertices.mpr
              ⟨γ, hγ, ht⟩)⟩⟩
    · have hsub : quotientEdgePreimage (touchedOuterForest z δ) (D.starOf G z.1.1)
          (touchedLocalComponent z δ) ≤ G.internalEdges :=
        le_trans (quotientEdgePreimage_le _ _ _)
          (by rw [ResolvedAdmissibleSubgraph.complementEdges]; exact tsub_le_self)
      have heG : e ∈ G.internalEdges := Multiset.mem_of_le hsub heM
      obtain ⟨hsG, htG⟩ := hE e heG
      exact ⟨Finset.mem_filter.mpr ⟨hsG, Or.inr (Or.inl ⟨e, heM, Or.inl rfl⟩)⟩,
             Finset.mem_filter.mpr ⟨htG, Or.inr (Or.inl ⟨e, heM, Or.inr rfl⟩)⟩⟩
  legs_supported := by
    intro ℓ hℓ
    have hℓG : ℓ ∈ G.externalLegs := Multiset.mem_of_le datum.legs_le hℓ
    exact Finset.mem_filter.mpr ⟨hL ℓ hℓG, Or.inr (Or.inr ⟨ℓ, hℓ, rfl⟩)⟩

variable {G : ResolvedFeynmanGraph} {z : ForestBlockCodType D G}
  {δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))}
  {datum : ResolvedTouchedLegLiftDatum z δ}
  {hE : ∀ e ∈ G.internalEdges, e.source ∈ G.vertices ∧ e.target ∈ G.vertices}
  {hL : ∀ ℓ ∈ G.externalLegs, ℓ.attachedTo ∈ G.vertices}

/-- **R-6c-body-326 — vertices containment into the custom parent.** -/
theorem touchedLegs_component_vertices_subset {A : ResolvedFeynmanSubgraph G}
    (hA : A ∈ (touchedOuterForest z δ).elements) :
    A.vertices ⊆ (localizedParentWithTouchedLegs z δ datum hE hL).vertices := by
  intro v hv
  exact Finset.mem_filter.mpr
    ⟨A.vertices_subset hv, Or.inl (ResolvedAdmissibleSubgraph.mem_vertices.mpr ⟨A, hA, hv⟩)⟩

/-- **R-6c-body-326 — internal-edges containment into the custom parent.** -/
theorem touchedLegs_component_internalEdges_le {A : ResolvedFeynmanSubgraph G}
    (hA : A ∈ (touchedOuterForest z δ).elements) :
    A.internalEdges ≤ (localizedParentWithTouchedLegs z δ datum hE hL).internalEdges :=
  le_trans (Finset.single_le_sum (fun _ _ => Multiset.zero_le _) hA) (Multiset.le_add_right _ _)

/-- **R-6c-body-326 — external-legs containment into the custom parent** (the route-A' leg containment, from the
datum's touched lower bound). -/
theorem touchedLegs_component_externalLegs_le {A : ResolvedFeynmanSubgraph G}
    (hA : A ∈ (touchedOuterForest z δ).elements) :
    A.externalLegs ≤ (localizedParentWithTouchedLegs z δ datum hE hL).externalLegs :=
  le_trans (Finset.single_le_sum (fun _ _ => Multiset.zero_le _) hA) datum.touched_le

end GaugeGeometry.QFT.Combinatorial
