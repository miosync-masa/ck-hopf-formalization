import GaugeGeometry.QFT.HopfAlgebra.Phi4WTriplePrimeRecoveredOuterComplement

/-!
# QFT-R1-body-619 — the recovered outer forest's W‴ membership + the source-independent inverse inhabitant

body-618 removed the last geometry gap (the recovered outer forest's POSITIVE complement in `G`).  This
body is **ownership assembly ONLY — ZERO new geometry**: it bundles the region-wise facts already owned by
the imported chain into `O := phi4WTriplePrime_recoveredOuter z`'s live W‴ membership, and packages the
source-independent `Phi4EdgeCompleteFilteredCoassocSplitChoice` inhabitant.

* **Step 1** — component properness leaves (origin dispatch over `O`'s components):
  `phi4WTriplePrime_inv_regionComponentOf_internalEdges_card_pos`,
  `phi4WTriplePrime_recoveredOuter_hasNonemptyComponents`,
  `phi4WTriplePrime_recoveredOuter_hasPositiveInternalEdgesComponents`,
  `phi4WTriplePrime_recoveredOuter_elements_nonempty`,
  `phi4WTriplePrime_recoveredOuter_internalEdges_card_pos`.  Dispatch: LEFT → `z.1.1.IsProperForest`
  component leaves; RIGHT → `recoveredRight` raw internal-edge equality + `z.2.1.IsProperForest`; FOREST →
  `recoveredParent_isNonempty` / `recoveredParent_internalEdges_card_pos`.  Pairwise disjointness / CD are
  already owned by the `recoveredOuter` constructor (body-614).
* **Step 2** — `phi4WTriplePrime_recoveredOuter_isProperForest`: the five `IsProperForest` conjuncts, the
  fifth being body-618's `phi4WTriplePrime_recoveredOuter_complementEdges_card_pos` plugged DIRECTLY (NO
  residual/count re-expansion).
* **Step 3** — sixth/seventh axes: `phi4WTriplePrime_recoveredOuter_forestSaturated` /
  `..._forestEdgeComplete`, component-origin dispatch (LEFT → `z.1.2` W‴ membership; RIGHT →
  `recoveredRight_saturated / edgeComplete`; FOREST → `recoveredParent_saturated / edgeComplete`).
* **Step 4 (TARGET 1)** — `phi4WTriplePrime_recoveredOuter_mem : O ∈ phi4WTriplePrimeIndex G`, via the
  seven-conjunct `mem_phi4WTriplePrimeIndex` criterion (four ambient gates project from `z.1.2`; the three
  forest gates are Steps 2–3).
* **Step 5 (TARGET 2)** — `phi4WTriplePrime_recoveredSplitChoice : Phi4EdgeCompleteFilteredCoassocSplitChoice
  G`, source-independent, ZERO external residual field, plus the two thin `@[simp]` anchors.

## HALT compliance
Axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only); ZERO forbidden divergence classes in any
declaration type.  Ownership assembly only: NO new geometry, NO body-618 count-proof re-run.  NO corrected
forward map / forward-after-inverse (620) / inverse-after-forward (621) / exact FOREST `Sum.inr` equation /
`Equiv` / summand / `sum_bij` / alpha / coassoc.  NO global `τ` / orbit quotient / dedup; NO `HEq` / `cast`;
NO new `class` / `structure` / permanent `instance`; NO polluted machinery; no `sorry` / `admit` /
`native_decide`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

open ResolvedFeynmanSubgraph

variable {G : ResolvedFeynmanGraph}

set_option maxHeartbeats 3200000

/-- The concrete φ⁴ divergence measure family, registered file-locally (providable instance, NO forbidden
class). -/
noncomputable local instance phi4Inst619 : (H : FeynmanGraph) → DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

/-! ## Step 1 — component properness leaves (origin dispatch over `O`'s components) -/

/-- **body-619 (Step 1) — every recovered quotient-region component has positive internal edge count.**
FOREST `δ` → `recoveredParent_internalEdges_card_pos`; RIGHT (star-free) `δ` → `recoveredRight`'s raw
internal-edge equality with `δ` + `z.2.1`'s positive-edge component leaf. -/
theorem phi4WTriplePrime_inv_regionComponentOf_internalEdges_card_pos
    (z : Phi4WTriplePrimeInverseCodomain G) (δ : {x // x ∈ z.2.1.elements}) :
    0 < (phi4WTriplePrime_inv_regionComponentOf z δ).internalEdges.card := by
  by_cases h : phi4WTriplePrime_inv_isForestImage z δ
  · rw [phi4WTriplePrime_inv_regionComponentOf_eq_parent z h]
    exact phi4WTriplePrime_inv_recoveredParent_internalEdges_card_pos _
  · rw [phi4WTriplePrime_inv_regionComponentOf_eq_right z h,
      phi4WTriplePrime_recoveredRight_internalEdges z h]
    exact (phi4WTriplePrime_inv_B_isProperForest z).2.2.2.1 δ.1 δ.2

/-- **body-619 (Step 1) — every recovered-outer component is vertex-nonempty.**  LEFT `A`-components reuse
`z.1.1`'s `HasNonemptyComponents` leaf; recovered quotient-region components reuse body-614's
`regionComponentOf_nonempty`. -/
theorem phi4WTriplePrime_recoveredOuter_hasNonemptyComponents
    (z : Phi4WTriplePrimeInverseCodomain G) :
    (phi4WTriplePrime_recoveredOuter z).HasNonemptyComponents := by
  intro γ hγ
  rcases phi4WTriplePrime_recoveredOuter_component_origin z hγ with ⟨hγA, _hL⟩ | ⟨δ, rfl⟩
  · exact (phi4WTriplePrime_inv_A_isProperForest z).2.1 γ hγA
  · exact Finset.card_pos.mpr (phi4WTriplePrime_inv_regionComponentOf_nonempty z δ)

/-- **body-619 (Step 1) — every recovered-outer component has positive internal edge count.**  LEFT reuses
`z.1.1`'s positive-edge leaf; recovered quotient-region components reuse the Step-1 helper above. -/
theorem phi4WTriplePrime_recoveredOuter_hasPositiveInternalEdgesComponents
    (z : Phi4WTriplePrimeInverseCodomain G) :
    (phi4WTriplePrime_recoveredOuter z).HasPositiveInternalEdgesComponents := by
  intro γ hγ
  rcases phi4WTriplePrime_recoveredOuter_component_origin z hγ with ⟨hγA, _hL⟩ | ⟨δ, rfl⟩
  · exact (phi4WTriplePrime_inv_A_isProperForest z).2.2.2.1 γ hγA
  · exact phi4WTriplePrime_inv_regionComponentOf_internalEdges_card_pos z δ

/-- **body-619 (Step 1) — the recovered outer forest has at least one component.**  `z.2.1` is nonempty, so
some `δ`'s recovered quotient-region component lands in `O`. -/
theorem phi4WTriplePrime_recoveredOuter_elements_nonempty
    (z : Phi4WTriplePrimeInverseCodomain G) :
    (phi4WTriplePrime_recoveredOuter z).IsNonempty := by
  obtain ⟨d, hd⟩ := (phi4WTriplePrime_inv_B_isProperForest z).1
  exact ⟨phi4WTriplePrime_inv_regionComponentOf z ⟨d, hd⟩,
    phi4WTriplePrime_inv_regionComponent_mem_recoveredOuter z ⟨d, hd⟩⟩

/-- **body-619 (Step 1) — the recovered outer forest carries a positive total internal edge count.**  Any
single recovered quotient-region component (positively edged, Step-1 helper) is a sub-multiset of `O`'s total
edges. -/
theorem phi4WTriplePrime_recoveredOuter_internalEdges_card_pos
    (z : Phi4WTriplePrimeInverseCodomain G) :
    0 < (phi4WTriplePrime_recoveredOuter z).internalEdges.card := by
  obtain ⟨d, hd⟩ := (phi4WTriplePrime_inv_B_isProperForest z).1
  set δ : {x // x ∈ z.2.1.elements} := ⟨d, hd⟩ with hδ
  have hmem : phi4WTriplePrime_inv_regionComponentOf z δ ∈ (phi4WTriplePrime_recoveredOuter z).elements :=
    phi4WTriplePrime_inv_regionComponent_mem_recoveredOuter z δ
  have hle : (phi4WTriplePrime_inv_regionComponentOf z δ).internalEdges
      ≤ (phi4WTriplePrime_recoveredOuter z).internalEdges := by
    rw [ResolvedAdmissibleSubgraph.internalEdges]
    exact Finset.single_le_sum (f := fun x : ResolvedFeynmanSubgraph G => x.internalEdges)
      (fun i _ => Multiset.zero_le _) hmem
  exact lt_of_lt_of_le (phi4WTriplePrime_inv_regionComponentOf_internalEdges_card_pos z δ)
    (Multiset.card_le_card hle)

/-! ## Step 2 — IsProperForest assembly -/

/-- **body-619 (Step 2, HEADLINE) — the recovered outer forest is a proper forest.**  Its five conjuncts are
the four Step-1 leaves and body-618's positive complement (`complementEdges_card_pos`), plugged directly. -/
theorem phi4WTriplePrime_recoveredOuter_isProperForest
    (z : Phi4WTriplePrimeInverseCodomain G) :
    (phi4WTriplePrime_recoveredOuter z).IsProperForest :=
  ⟨phi4WTriplePrime_recoveredOuter_elements_nonempty z,
    phi4WTriplePrime_recoveredOuter_hasNonemptyComponents z,
    phi4WTriplePrime_recoveredOuter_internalEdges_card_pos z,
    phi4WTriplePrime_recoveredOuter_hasPositiveInternalEdgesComponents z,
    phi4WTriplePrime_recoveredOuter_complementEdges_card_pos z⟩

/-! ## Step 3 — sixth / seventh axes -/

/-- **body-619 (Step 3, sixth axis) — the recovered outer forest is external-leg saturated.**  Origin
dispatch: LEFT → `z.1.2`'s W‴ membership; RIGHT → `recoveredRight_saturated`; FOREST →
`recoveredParent_saturated`, transported along `regionComponentOf_eq_parent/right`. -/
theorem phi4WTriplePrime_recoveredOuter_forestSaturated
    (z : Phi4WTriplePrimeInverseCodomain G) :
    ResolvedForestExternalLegSaturated (phi4WTriplePrime_recoveredOuter z) := by
  intro γ hγ
  rcases phi4WTriplePrime_recoveredOuter_component_origin z hγ with ⟨hγA, _hL⟩ | ⟨δ, rfl⟩
  · exact ((mem_phi4WTriplePrimeIndex G z.1.1).mp z.1.2).2.2.2.2.2.1 γ hγA
  · by_cases h : phi4WTriplePrime_inv_isForestImage z δ
    · rw [phi4WTriplePrime_inv_regionComponentOf_eq_parent z h]
      exact phi4WTriplePrime_inv_recoveredParent_saturated _
    · rw [phi4WTriplePrime_inv_regionComponentOf_eq_right z h]
      exact phi4WTriplePrime_inv_recoveredRight_saturated z h

/-- **body-619 (Step 3, seventh axis) — the recovered outer forest is internal-edge complete.**  Origin
dispatch: LEFT → `z.1.2`'s W‴ membership; RIGHT → `recoveredRight_edgeComplete`; FOREST →
`recoveredParent_edgeComplete`, transported along `regionComponentOf_eq_parent/right`. -/
theorem phi4WTriplePrime_recoveredOuter_forestEdgeComplete
    (z : Phi4WTriplePrimeInverseCodomain G) :
    ResolvedForestInternalEdgeComplete phi4DivergenceMeasureFamily (phi4WTriplePrime_recoveredOuter z) := by
  intro γ hγ
  rcases phi4WTriplePrime_recoveredOuter_component_origin z hγ with ⟨hγA, _hL⟩ | ⟨δ, rfl⟩
  · exact ((mem_phi4WTriplePrimeIndex G z.1.1).mp z.1.2).2.2.2.2.2.2 γ hγA
  · by_cases h : phi4WTriplePrime_inv_isForestImage z δ
    · rw [phi4WTriplePrime_inv_regionComponentOf_eq_parent z h]
      exact phi4WTriplePrime_inv_recoveredParent_edgeComplete _
    · rw [phi4WTriplePrime_inv_regionComponentOf_eq_right z h]
      exact phi4WTriplePrime_inv_recoveredRight_edgeComplete z h

/-! ## Step 4 — TARGET 1: live W‴ membership -/

/-- **body-619 (Step 4, TARGET 1) — the recovered outer forest is a LIVE W‴ carrier member.**  Via the
seven-conjunct `mem_phi4WTriplePrimeIndex` criterion: the four ambient gates (`ResolvedAmbientSupported G`,
`IsConnectedDivergentFor … G`, `G.EdgeIdsUnique`, `G.LegIdsUnique`) project from `z.1.2` (they read only
`G`); the three forest gates are Step 2 (`IsProperForest`) and Step 3 (saturation, edge-completeness). -/
theorem phi4WTriplePrime_recoveredOuter_mem (z : Phi4WTriplePrimeInverseCodomain G) :
    phi4WTriplePrime_recoveredOuter z ∈ phi4WTriplePrimeIndex G := by
  have hz := (mem_phi4WTriplePrimeIndex G z.1.1).mp z.1.2
  exact (mem_phi4WTriplePrimeIndex G (phi4WTriplePrime_recoveredOuter z)).mpr
    ⟨hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1,
      phi4WTriplePrime_recoveredOuter_isProperForest z,
      phi4WTriplePrime_recoveredOuter_forestSaturated z,
      phi4WTriplePrime_recoveredOuter_forestEdgeComplete z⟩

/-! ## Step 5 — TARGET 2: source-independent inverse inhabitant -/

/-- **body-619 (Step 5, TARGET 2) — the source-independent inverse split-choice inhabitant.**  A live
`Phi4EdgeCompleteFilteredCoassocSplitChoice G`, a function of an arbitrary codomain `z` alone (never reading a
source occurrence): the recovered outer forest with its Step-4 W‴ membership, the recovered global choice with
its carrier membership, and the forest-filtering (avoids both pure primitives, body-617).  ZERO external
residual field. -/
noncomputable def phi4WTriplePrime_recoveredSplitChoice (z : Phi4WTriplePrimeInverseCodomain G) :
    Phi4EdgeCompleteFilteredCoassocSplitChoice G where
  outer := phi4WTriplePrime_recoveredOuter z
  outer_mem := phi4WTriplePrime_recoveredOuter_mem z
  choice := phi4WTriplePrime_recoveredChoice z
  choice_mem := phi4WTriplePrime_recoveredChoice_mem z
  choice_filtered :=
    (mem_phi4EdgeCompleteForestChoiceCarrier (phi4WTriplePrime_recoveredOuter z)).mpr
      ⟨phi4WTriplePrime_recoveredChoice_mem z,
        phi4WTriplePrime_recoveredChoice_ne_pureRight z,
        phi4WTriplePrime_recoveredChoice_ne_pureLeft z⟩

/-- **body-619 (Step 5, anchor) — the inhabitant's outer forest is the recovered outer forest.** -/
@[simp] theorem phi4WTriplePrime_recoveredSplitChoice_outer (z : Phi4WTriplePrimeInverseCodomain G) :
    (phi4WTriplePrime_recoveredSplitChoice z).outer = phi4WTriplePrime_recoveredOuter z := rfl

/-- **body-619 (Step 5, anchor) — the inhabitant's choice is the recovered global choice. -/
@[simp] theorem phi4WTriplePrime_recoveredSplitChoice_choice (z : Phi4WTriplePrimeInverseCodomain G) :
    (phi4WTriplePrime_recoveredSplitChoice z).choice = phi4WTriplePrime_recoveredChoice z := rfl

end GaugeGeometry.QFT.Combinatorial
