import GaugeGeometry.QFT.HopfAlgebra.Phi4WTriplePrimeEdgeCompleteCarrier
import GaugeGeometry.QFT.HopfAlgebra.Phi4WDoublePrimeCoassocSplitChoice

/-!
# QFT-R1-body-601 — family W‴ owner + ungated split-choice re-key

Body-600 introduced the **fifth axis** — vertex-induced internal-edge completeness — as a filter on the
W″ index (`phi4WTriplePrimeIndex`), and proved that forest edge-completeness DISCHARGES the body-599
split-choice boundary-closed gate (`rootRelativeBoundaryClosed_of_edgeComplete`).  Up to that point the
fifth axis was still just a *filter condition* one had to pass to a gated landing as a separate argument.

This body threads the fifth axis through the ENTIRE ownership chain so that it becomes **live ownership**
read by every consumer.  It issues:

* Step 1 — the two projection accessors `phi4WTriplePrime_mem_wDoublePrime` (W‴ member → W″ member) and
  `phi4WTriplePrime_forestEdgeComplete` (W‴ member → forest edge-completeness), the ONLY two places the
  seven fifth-axis conditions are consumed.
* Step 2 — the mapPerm-closure `phi4WTriplePrimeIndex_mapPerm` (the one substantive proof, via the fifth
  axis' clean `resolvedForestInternalEdgeComplete_mapPerm_iff`), the index data `phi4WTriplePrimeIndexData`,
  and the FULL W‴ canonical supply `phi4WTriplePrimeCanonicalSupply` (issued ONCE, reusing the W″ supply's
  `starOf` / `hCD` / `rightTerm_mapPerm` by projection).
* Step 3 — the W‴ coproduct owner `phi4WTriplePrimeResolvedCoproductSupply` and the genuine filtered
  coproduct `coproduct_resolved_edgeComplete_phi4`.  This is a **DIFFERENT** filtered coproduct from
  body-591's `coproduct_resolved_phi4` (different index → genuinely different filtered coproduct); NO
  equality / restriction / cast between the two is asserted anywhere.
* Step 4 — the W‴-keyed local + split choices, mechanical mirrors of body-594/595 with the supply swapped
  and `outer_mem` landing in `phi4WTriplePrimeIndex` (so both inner and outer carry the fifth axis in the
  TYPE).
* Step 5 — the VICTORY: `phi4EdgeCompleteSplitChoice_rootRelativeInner_isConnectedDivergent`, a final CD
  landing that takes NO external `Phi4StableSplitChoiceBoundaryClosed` / `RootRelativeBoundaryClosed`
  argument — the gate is auto-derived internally from the W‴ split choice's `outer_mem` (fifth-axis index
  membership → forest edge-completeness → body-600's `rootRelativeBoundaryClosed_of_edgeComplete`).

## HALT compliance

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only); ZERO forbidden divergence classes
(`IsPermInvariantDivergence` / `IsIsoInvariantDivergence` / `IsAmbientInvariantDivergence` /
`IsDivergencePreservedByContract` / `...ByAdmissibleForestContract` /
`IsDivergenceReflectedByAdmissibleForestContract`) in ANY declaration's type; the only divergence binders
are the concrete `phi4DivergenceMeasureFamily` / `phi4PermInvariantDivergenceMeasureFamily`.  Single-owner
WIRING only — no new geometry; no `selectedOuter` / `promotedOf` / quotient correspondence / forest_block /
alpha / coassoc; no flat-coproduct descent; NO equality / restriction / cast between the W‴ coproduct and
the body-591 W″ coproduct.  No `sorry` / `admit` / `native_decide`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct
open scoped Classical

open ResolvedFeynmanSubgraph

variable {G : ResolvedFeynmanGraph}

/-! ## Step 1 — W‴ → W″ projection accessors (the ONLY consumers of the seven conditions) -/

/-- **body-601 (Step 1) — a W‴ member is a W″ member.**  The fifth-axis index is the W″ index filtered by
forest edge-completeness, and `(phi4WDoublePrimeCanonicalSupply.index G).carrier` is defeq the W″ base index
`resolvedLegSaturatedIndexFor phi4… G`; strip the filter. -/
theorem phi4WTriplePrime_mem_wDoublePrime {G : ResolvedFeynmanGraph}
    {A : ResolvedAdmissibleSubgraphFor phi4DivergenceMeasureFamily G}
    (hA : A ∈ phi4WTriplePrimeIndex G) :
    A ∈ @ResolvedProperForestFiniteIndex.carrier phi4DivergenceMeasureFamily G
      (phi4WDoublePrimeCanonicalSupply.index G) := by
  have h : A ∈ resolvedLegSaturatedIndexFor phi4DivergenceMeasureFamily
      phi4PermInvariantDivergenceMeasureFamily G := by
    unfold phi4WTriplePrimeIndex resolvedEdgeCompleteIndexFor at hA
    exact (Finset.mem_filter.mp hA).1
  exact h

/-- **body-601 (Step 1) — a W‴ member is forest-internal-edge complete.**  The seventh conjunct of the
fifth-axis membership `iff`. -/
theorem phi4WTriplePrime_forestEdgeComplete {G : ResolvedFeynmanGraph}
    {A : ResolvedAdmissibleSubgraphFor phi4DivergenceMeasureFamily G}
    (hA : A ∈ phi4WTriplePrimeIndex G) :
    ResolvedForestInternalEdgeComplete phi4DivergenceMeasureFamily A :=
  ((mem_phi4WTriplePrimeIndex G A).mp hA).2.2.2.2.2.2

/-! ## Step 2 — the W‴ full canonical supply (issued ONCE) -/

/-- **body-601 (Step 2) — forest edge-completeness is invariant under vertex relabeling.**  Per-component
via body-600's clean `resolvedInternalEdgeComplete_mapPerm_iff` and the clean forest relabeling's
`elements = image`.  No divergence content, no forbidden-class binder. -/
theorem resolvedForestInternalEdgeComplete_mapPerm_iff (σ : Equiv.Perm VertexId)
    (A : ResolvedAdmissibleSubgraphFor phi4DivergenceMeasureFamily G) :
    ResolvedForestInternalEdgeComplete phi4DivergenceMeasureFamily
        (mapPermResolvedAdmissibleSubgraphFor phi4DivergenceMeasureFamily
          phi4PermInvariantDivergenceMeasureFamily (rfl : G.mapPerm σ = G.mapPerm σ) A)
      ↔ ResolvedForestInternalEdgeComplete phi4DivergenceMeasureFamily A := by
  letI : (H : FeynmanGraph) → DivergenceMeasure H := phi4DivergenceMeasureFamily
  unfold ResolvedForestInternalEdgeComplete
  constructor
  · intro h γ hγ
    have hmem : mapPermRFS (rfl : G.mapPerm σ = G.mapPerm σ) γ ∈
        (mapPermResolvedAdmissibleSubgraphFor phi4DivergenceMeasureFamily
          phi4PermInvariantDivergenceMeasureFamily (rfl : G.mapPerm σ = G.mapPerm σ) A).elements := by
      rw [mapPermResolvedAdmissibleSubgraphFor_elements]; exact Finset.mem_image_of_mem _ hγ
    exact (resolvedInternalEdgeComplete_mapPerm_iff σ γ).mp (h _ hmem)
  · intro h γ' hγ'
    rw [mapPermResolvedAdmissibleSubgraphFor_elements] at hγ'
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hγ'
    exact (resolvedInternalEdgeComplete_mapPerm_iff σ γ).mpr (h γ hγ)

/-- **body-601 (Step 2) — the fifth-axis index transports along the clean relabeling.**  Rewrite the W″
base with `resolvedLegSaturatedIndexFor_mapPerm`, then commute the edge-completeness filter past the image
using the predicate's mapPerm invariance (`Finset.ext`; no injectivity needed — the predicate transports
exactly). -/
theorem phi4WTriplePrimeIndex_mapPerm (G : ResolvedFeynmanGraph) (σ : Equiv.Perm VertexId) :
    phi4WTriplePrimeIndex (G.mapPerm σ)
      = (phi4WTriplePrimeIndex G).image
          (mapPermResolvedAdmissibleSubgraphFor phi4DivergenceMeasureFamily
            phi4PermInvariantDivergenceMeasureFamily (rfl : G.mapPerm σ = G.mapPerm σ)) := by
  unfold phi4WTriplePrimeIndex resolvedEdgeCompleteIndexFor
  rw [resolvedLegSaturatedIndexFor_mapPerm phi4DivergenceMeasureFamily
    phi4PermInvariantDivergenceMeasureFamily (G := G) σ]
  ext A
  simp only [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨B, hB, rfl⟩, hEC⟩
    exact ⟨B, ⟨hB, (resolvedForestInternalEdgeComplete_mapPerm_iff σ B).mp hEC⟩, rfl⟩
  · rintro ⟨B, ⟨hB, hEC⟩, rfl⟩
    exact ⟨⟨B, hB, rfl⟩, (resolvedForestInternalEdgeComplete_mapPerm_iff σ B).mpr hEC⟩

/-- **body-601 (Step 2) — the φ⁴ W‴ per-graph index payload** (so `(index G).carrier` reduces to
`phi4WTriplePrimeIndex G`).  `mem_proper` = the fifth conjunct (`IsProperForest`). -/
noncomputable def phi4WTriplePrimeIndexData (G : ResolvedFeynmanGraph) :
    @ResolvedProperForestFiniteIndex phi4DivergenceMeasureFamily G := by
  letI : (H : FeynmanGraph) → DivergenceMeasure H := phi4DivergenceMeasureFamily
  exact { carrier := phi4WTriplePrimeIndex G,
          mem_proper := fun A hA => ((mem_phi4WTriplePrimeIndex G A).mp hA).2.2.2.2.1 }

/-- **body-601 (Step 2) ∎ — the φ⁴ FULL W‴ carrier supply.**  Index = the fifth-axis (edge-complete) finite
index; `starOf` / `hCD` / `rightTerm_mapPerm` are the body-588 W″ supply's, projected through
`phi4WTriplePrime_mem_wDoublePrime` (star does not depend on the carrier; the reused proofs enter
proof-irrelevantly); `carrier_mapPerm` = Step 2. -/
noncomputable def phi4WTriplePrimeCanonicalSupply :
    ResolvedCanonicalCarrierProperSupplyFor phi4DivergenceMeasureFamily
      phi4PermInvariantDivergenceMeasureFamily where
  index := phi4WTriplePrimeIndexData
  starOf := phi4WDoublePrimeCanonicalSupply.starOf
  hCD := by
    letI : (H : FeynmanGraph) → DivergenceMeasure H := phi4DivergenceMeasureFamily
    intro G A hA
    exact phi4WDoublePrimeCanonicalSupply.hCD G A (phi4WTriplePrime_mem_wDoublePrime hA)
  carrier_mapPerm := by
    letI : (H : FeynmanGraph) → DivergenceMeasure H := phi4DivergenceMeasureFamily
    intro G σ
    exact phi4WTriplePrimeIndex_mapPerm G σ
  rightTerm_mapPerm := by
    letI : (H : FeynmanGraph) → DivergenceMeasure H := phi4DivergenceMeasureFamily
    intro G σ A hA hAσ
    exact phi4WDoublePrimeCanonicalSupply.rightTerm_mapPerm G σ A
      (phi4WTriplePrime_mem_wDoublePrime hA) (phi4WTriplePrime_mem_wDoublePrime hAσ)

/-! ## Step 3 — the W‴ coproduct owner (nearly free, generic in the supply) -/

/-- **body-601 (Step 3) — the concrete φ⁴ W‴ resolved coproduct owner.**  The Step-2 full carrier supply
read as an equivariant forest-summand supply family (`summandSupply` + `summandSupply_sum_mapPerm`, both
generic in the supply, body-591). -/
noncomputable def phi4WTriplePrimeResolvedCoproductSupply :
    ResolvedCoproductGenSupplyFor phi4DivergenceMeasureFamily
      phi4PermInvariantDivergenceMeasureFamily where
  supply := phi4WTriplePrimeCanonicalSupply.summandSupply
  sum_mapPerm := fun G σ => phi4WTriplePrimeCanonicalSupply.summandSupply_sum_mapPerm G σ

/-- **body-601 (Step 3, TARGET) — the genuine φ⁴ W‴ (edge-complete) resolved coproduct** `Δᵣ‴ :
ResolvedPhi4HopfH →ₐ ResolvedPhi4HopfH ⊗ ResolvedPhi4HopfH`, from the single owner
`phi4WTriplePrimeResolvedCoproductSupply`.

This is a **DIFFERENT** filtered coproduct from body-591's `coproduct_resolved_phi4`: it sums over the
fifth-axis edge-complete carrier `phi4WTriplePrimeIndex`, a strictly-filtered sub-index of the W″ carrier.
NO equality / restriction / cast between the two coproducts is asserted (different index → genuinely a
different filtered coproduct). -/
noncomputable def coproduct_resolved_edgeComplete_phi4 :
    ResolvedPhi4HopfH →ₐ[ℚ] ResolvedPhi4HopfH ⊗[ℚ] ResolvedPhi4HopfH :=
  phi4WTriplePrimeResolvedCoproductSupply.coproduct

/-! ## Step 4 — W‴-keyed local + split choice (re-key of body-594/595, supply swapped) -/

/-- **body-601 (Step 4) — the φ⁴ W‴ local choice carrier for a component `γ`.**  Mirror of body-594's
`phi4LocalChoiceCarrier` with the W‴ supply: the `Sum.inr` index type is now
`(phi4WTriplePrimeCanonicalSupply.summandSupply γ.boundaryCompletedResolvedGraph).ForestIdx =
{B // B ∈ phi4WTriplePrimeIndex γ.boundaryCompletedResolvedGraph}`, so the inner ambient's FIFTH AXIS is
carried in the TYPE. -/
noncomputable def phi4EdgeCompleteLocalChoiceCarrier {G : ResolvedFeynmanGraph}
    (γ : ResolvedFeynmanSubgraph G) :
    Finset (Bool ⊕
        (phi4WTriplePrimeCanonicalSupply.summandSupply γ.boundaryCompletedResolvedGraph).ForestIdx) :=
  (Finset.univ : Finset Bool).disjSum
    (phi4WTriplePrimeCanonicalSupply.summandSupply γ.boundaryCompletedResolvedGraph).forestCarrier

/-- **body-601 (Step 4) — the φ⁴ W‴ local choice term.**  Mirror of body-594's `phi4LocalChoiceTerm` with
the W‴ supply; the two primitive legs and, per live W‴ carrier member `B`, the forest summand
`leftTerm B ⊗ rightTerm B`. -/
noncomputable def phi4EdgeCompleteLocalChoiceTerm {G : ResolvedFeynmanGraph}
    (γ : ResolvedFeynmanSubgraph G)
    (hCD : ∃ hWF : γ.boundaryCompletedResolvedGraph.forget.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent γ.boundaryCompletedResolvedGraph.forget
        (phi4DivergenceMeasureFamily γ.boundaryCompletedResolvedGraph.forget)
        (FeynmanSubgraph.self γ.boundaryCompletedResolvedGraph.forget hWF)) :
    (Bool ⊕
        (phi4WTriplePrimeCanonicalSupply.summandSupply γ.boundaryCompletedResolvedGraph).ForestIdx) →
      ResolvedPhi4HopfH ⊗[ℚ] ResolvedPhi4HopfH :=
  Sum.elim
    (fun b => bif b then MvPolynomial.X (γ.toResolvedPhi4HopfGenBoundaryCompleted hCD) ⊗ₜ[ℚ]
        (1 : ResolvedPhi4HopfH)
      else (1 : ResolvedPhi4HopfH) ⊗ₜ[ℚ] MvPolynomial.X (γ.toResolvedPhi4HopfGenBoundaryCompleted hCD))
    (fun B => (phi4WTriplePrimeCanonicalSupply.summandSupply γ.boundaryCompletedResolvedGraph).leftTerm B
      ⊗ₜ[ℚ] (phi4WTriplePrimeCanonicalSupply.summandSupply γ.boundaryCompletedResolvedGraph).rightTerm B)

/-- **body-601 (Step 4) — the global component-choice carrier** (mirror of body-595
`phi4GlobalChoiceCarrier`, W‴ supply). -/
noncomputable def phi4EdgeCompleteGlobalChoiceCarrier {G : ResolvedFeynmanGraph}
    (A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G) :=
  (@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G A).attach.pi
    (fun γ => phi4EdgeCompleteLocalChoiceCarrier γ.1)

/-- **body-601 (Step 4) — the all-right pure primitive choice** (`Sum.inl false` everywhere). -/
noncomputable def phi4EdgeCompleteChoicePR {G : ResolvedFeynmanGraph}
    (A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G) :
    (γ : {x // x ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G A}) →
      γ ∈ (@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G A).attach →
        Bool ⊕ (phi4WTriplePrimeCanonicalSupply.summandSupply γ.1.boundaryCompletedResolvedGraph).ForestIdx :=
  fun _ _ => Sum.inl false

/-- **body-601 (Step 4) — the all-left pure primitive choice** (`Sum.inl true` everywhere). -/
noncomputable def phi4EdgeCompleteChoicePL {G : ResolvedFeynmanGraph}
    (A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G) :
    (γ : {x // x ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G A}) →
      γ ∈ (@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G A).attach →
        Bool ⊕ (phi4WTriplePrimeCanonicalSupply.summandSupply γ.1.boundaryCompletedResolvedGraph).ForestIdx :=
  fun _ _ => Sum.inl true

/-- **body-601 (Step 4) — the forest (non-pure) split-choice carrier** (the global choices with the two
pure primitives filtered out; every remaining choice has at least one live W‴ inner-forest `Sum.inr B`
leg). -/
noncomputable def phi4EdgeCompleteForestChoiceCarrier {G : ResolvedFeynmanGraph}
    (A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G) :=
  (phi4EdgeCompleteGlobalChoiceCarrier A).filter
    (fun p => p ≠ phi4EdgeCompleteChoicePR A ∧ p ≠ phi4EdgeCompleteChoicePL A)

/-- **body-601 (Step 4) — `phi4EdgeCompleteChoicePR` is a valid global choice.** -/
theorem phi4EdgeCompleteChoicePR_mem_global {G : ResolvedFeynmanGraph}
    (A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G) :
    phi4EdgeCompleteChoicePR A ∈ phi4EdgeCompleteGlobalChoiceCarrier A := by
  unfold phi4EdgeCompleteGlobalChoiceCarrier
  rw [Finset.mem_pi]
  exact fun γ hγ => Finset.inl_mem_disjSum.mpr (Finset.mem_univ false)

/-- **body-601 (Step 4) — `phi4EdgeCompleteChoicePL` is a valid global choice.** -/
theorem phi4EdgeCompleteChoicePL_mem_global {G : ResolvedFeynmanGraph}
    (A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G) :
    phi4EdgeCompleteChoicePL A ∈ phi4EdgeCompleteGlobalChoiceCarrier A := by
  unfold phi4EdgeCompleteGlobalChoiceCarrier
  rw [Finset.mem_pi]
  exact fun γ hγ => Finset.inl_mem_disjSum.mpr (Finset.mem_univ true)

/-- **body-601 (Step 4) — the two pure primitives are distinct** (given the outer forest has a
component). -/
theorem phi4EdgeCompleteChoicePR_ne_PL {G : ResolvedFeynmanGraph}
    (A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G)
    (hne : (@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G A).Nonempty) :
    phi4EdgeCompleteChoicePR A ≠ phi4EdgeCompleteChoicePL A := by
  obtain ⟨v, hv⟩ := hne
  intro h
  have hfalse := congrFun (congrFun h ⟨v, hv⟩) (Finset.mem_attach _ _)
  simp only [phi4EdgeCompleteChoicePR, phi4EdgeCompleteChoicePL, Sum.inl.injEq] at hfalse
  exact absurd hfalse Bool.false_ne_true

/-- **body-601 (Step 4) — the forest-choice membership `iff`.** -/
theorem mem_phi4EdgeCompleteForestChoiceCarrier {G : ResolvedFeynmanGraph}
    (A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G)
    {p : (γ : {x // x ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G A}) →
        γ ∈ (@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G A).attach →
          Bool ⊕
            (phi4WTriplePrimeCanonicalSupply.summandSupply γ.1.boundaryCompletedResolvedGraph).ForestIdx} :
    p ∈ phi4EdgeCompleteForestChoiceCarrier A ↔
      p ∈ phi4EdgeCompleteGlobalChoiceCarrier A
        ∧ p ≠ phi4EdgeCompleteChoicePR A ∧ p ≠ phi4EdgeCompleteChoicePL A := by
  unfold phi4EdgeCompleteForestChoiceCarrier
  exact Finset.mem_filter

/-- **body-601 (Step 4) — a resolved coassoc split choice, W‴-keyed.**  The outer forest `outer` is a LIVE
W‴ (fifth-axis) carrier member (`outer_mem ∈ phi4WTriplePrimeIndex G`), and each `Sum.inr B` leg of `choice`
has the W‴ supply's `ForestIdx` — so BOTH inner and outer carry the fifth axis in the TYPE. -/
structure Phi4EdgeCompleteResolvedCoassocSplitChoice (G : ResolvedFeynmanGraph) where
  /-- The outer W‴ (edge-complete) forest. -/
  outer : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G
  /-- The outer forest is a live W‴ carrier member (fifth-axis index membership). -/
  outer_mem : outer ∈ phi4WTriplePrimeIndex G
  /-- A global component choice: per component, a `phi4EdgeCompleteLocalChoiceCarrier` element on the
  boundary-completed inner ambient (its `Sum.inr` leg is a live W‴ inner carrier member). -/
  choice : (γ : {x // x ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G outer}) →
    γ ∈ (@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G outer).attach →
      Bool ⊕ (phi4WTriplePrimeCanonicalSupply.summandSupply γ.1.boundaryCompletedResolvedGraph).ForestIdx
  /-- The choice is a valid global choice. -/
  choice_mem : choice ∈ phi4EdgeCompleteGlobalChoiceCarrier outer

/-- **body-601 (Step 4) — a filtered (forest, non-pure) W‴ coassoc split choice.** -/
structure Phi4EdgeCompleteFilteredCoassocSplitChoice (G : ResolvedFeynmanGraph) extends
    Phi4EdgeCompleteResolvedCoassocSplitChoice G where
  /-- The choice avoids both pure primitives (lives in the forest-choice carrier). -/
  choice_filtered : toPhi4EdgeCompleteResolvedCoassocSplitChoice.choice ∈
    phi4EdgeCompleteForestChoiceCarrier toPhi4EdgeCompleteResolvedCoassocSplitChoice.outer

/-! ## Step 5 — gate elimination (the VICTORY) -/

/-- **body-601 (Step 5) — the outer forest of a W‴ split choice is forest-internal-edge complete.**  Pulled
straight off the fifth-axis membership `outer_mem`; the gate ingredient is LIVE OWNERSHIP, not a separate
argument. -/
theorem phi4EdgeCompleteSplitChoice_forestEdgeComplete
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) :
    ResolvedForestInternalEdgeComplete phi4DivergenceMeasureFamily s.outer :=
  phi4WTriplePrime_forestEdgeComplete s.outer_mem

/-- **body-601 (Step 5, VICTORY) — the ungated split-choice CD landing.**  For every outer component `γ` of
a W‴ split choice and every externally-leg-saturated inner `δ` carrying its own component CD, the nested
root lift `R = rootRelativeInner γ δ` is connected divergent on `G.forget`.

The KEY POINT: NO `Phi4StableSplitChoiceBoundaryClosed` / `RootRelativeBoundaryClosed` appears as a
HYPOTHESIS — the boundary-closed gate is DERIVED internally from `s.outer_mem` (fifth-axis membership →
forest edge-completeness → body-600's `rootRelativeBoundaryClosed_of_edgeComplete`).  The outer
external-leg saturation `hγsat` is likewise derived from `s.outer_mem` (projected to W″ then read off the
W″ membership `iff`).  The inner external-leg saturation `hδsat` is threaded as a hypothesis — it is inner
saturation, NOT the forbidden boundary-closed gate. -/
theorem phi4EdgeCompleteSplitChoice_rootRelativeInner_isConnectedDivergent
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G)
    {γ : ResolvedFeynmanSubgraph G}
    (hγ : γ ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G s.outer)
    {δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph}
    (hδsat : ResolvedExternalLegSaturated γ.boundaryCompletedResolvedGraph δ)
    (hδCD : @FeynmanSubgraph.IsConnectedDivergent γ.boundaryCompletedResolvedGraph.forget
      (phi4DivergenceMeasureFamily _) δ.forget) :
    @FeynmanSubgraph.IsConnectedDivergent G.forget (phi4DivergenceMeasureFamily _)
      (rootRelativeInner γ δ).forget := by
  have hEC : ResolvedInternalEdgeComplete γ :=
    phi4EdgeCompleteSplitChoice_forestEdgeComplete s γ hγ
  have hClosed : RootRelativeBoundaryClosed γ δ :=
    rootRelativeBoundaryClosed_of_edgeComplete γ δ hEC
  have hγsat : ResolvedExternalLegSaturated G γ := by
    have hmem : s.outer ∈ resolvedLegSaturatedIndexFor phi4DivergenceMeasureFamily
        phi4PermInvariantDivergenceMeasureFamily G := phi4WTriplePrime_mem_wDoublePrime s.outer_mem
    exact ((mem_resolvedLegSaturatedIndexFor phi4DivergenceMeasureFamily
      phi4PermInvariantDivergenceMeasureFamily G s.outer).mp hmem).2.2.2.2.2 γ hγ
  exact rootRelativeInner_forget_isConnectedDivergent_of_closed γ δ hClosed hγsat hδsat hδCD

end GaugeGeometry.QFT.Combinatorial
