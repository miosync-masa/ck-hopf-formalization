import GaugeGeometry.QFT.HopfAlgebra.Phi4WTriplePrimeForestBlockEquiv

/-!
# QFT-R1-body-616 — the corrected quotient forest (componentwise τ-correction, inverse side)

Body-615 reached a RED-LINE STOP: the uncorrected forest-block forward is NOT a raw bijection because the
FOREST sector recovers `δ` only up to a per-occurrence correcting permutation `τ`
(`phi4WTriplePrime_inv_reconTau O.input`).  A single GLOBAL `τ` is unavailable (cross-occurrence injectivity
of the local stars is UNPROVEN — the source local star of each occurrence lives in that occurrence's OWN
recovered-parent ambient, so distinct occurrences' local stars are not comparable as raw `VertexId`s), and
orbit-quotienting the codomain is REJECTED (it would collapse ID-distinct occurrences / star fibers and change
multiplicities).  The CORRECT global object (old-CK body-454/489 route) is the **corrected quotient forest**:
the per-occurrence `τ`-corrected components bundled WITH multiplicity preserved.

This body carries out that construction on the INVERSE side, mirroring the forward decompletion machinery of
body-604 (`remnantComponent`) / body-606 (`quotientForest`).

## Steps

* **Step 1 (global compatibility audit)** — the finite request index of `(δ, touched outer component)`
  (`phi4WTriplePrime_inv_forestRequestIndex`), the source local star (per occurrence, in the recovered
  parent's boundary-completed ambient) and the destination quotient star (`starOf G z.1.1`).  VERDICT: the
  source local stars of DISTINCT occurrences inhabit DISTINCT recovered-parent ambients, so cross-occurrence
  injectivity of the sources is not available; NO single global `τ` is banked and NO hypothesis is added.  We
  take the COMPONENTWISE route: each occurrence is corrected by its OWN `reconTau O.input`.
* **Step 2 (per-occurrence corrected graph)** — `phi4WTriplePrime_inv_correctedForestGraph O`, the recovered
  inner forest recontracted with the parent's fresh canonical star and pushed through `reconTau O.input`.  The
  RAW equality `correctedForestGraph O = δ.1.boundaryCompletedResolvedGraph` is CONSUMED directly from body-613
  (`phi4WTriplePrime_inv_recontraction_raw`); the survivor fix and the local-star → target-star law are
  re-exposed from body-613's `reconTau_fix` / `reconTau_map`.  NO re-proof of recontraction geometry.
* **Step 3 (decompletion + reembed)** — `phi4WTriplePrime_inv_correctedForestComponent O`, the corrected graph
  returned as a subgraph of the common quotient ambient `Q := z.1.1.contractWithStars (starOf G z.1.1)`; its
  legs are the DECOMPLETED genuine `Q`-legs (`Q.externalLegs.filter`), never the synthetic boundary legs.  The
  three RAW field equalities (vertices / internalEdges / externalLegs) against `δ.1` are proved
  (`δ.boundaryEdgeCount = 0` is never assumed; the externalLegs match uses `δ.1`'s external-leg SATURATION on
  `Q`, so the completed graph's synthetic legs are dropped exactly).
* **Step 4 (component round-trip)** — `phi4WTriplePrime_inv_correctedForestComponent_roundtrip` is an ordinary
  `Eq` (`correctedForestComponent O = δ.1`): both subgraphs inhabit the SAME fixed quotient ambient `Q`, so no
  dependent transport is needed and NO `HEq` / `cast` is introduced.  This closes the GEOMETRIC part of
  body-614's FOREST obligation; the global `Sum.inr` TERM equation stays for body-617.
* **Step 5 (corrected FOREST collection)** — `phi4WTriplePrime_inv_correctedForest`, the `Finset.image` of the
  target `forestDomain` under the corrected-component map (with an explicit injectivity proof — NO dedup / NO
  orbit quotient), the membership `iff`, the exact cardinality preservation, and the `elements` `Eq`.
* **Step 6 (interface for body-617)** — the corrected components, the exact per-occurrence recovery, and the
  collection facts, packaged for the corrected forward map.

## HALT compliance
Axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only); ZERO forbidden divergence classes in any
declaration type; the componentwise route adds NO hypothesis and banks NO ungrounded global `τ`; no
`δ.boundaryEdgeCount = 0`; no strict cross-presentation star equality; every `Finset.image` carries an
injectivity proof (zero multiplicity loss); the round-trip is a genuine raw `Eq` with no fabricated `HEq` /
`cast`; no `forestBlockForwardCorrected` / filtered inverse / whole `Equiv` / summand agreement / `sum_bij` /
`alpha` / coassoc; no new `class` / permanent `instance`; no `sorry` / `admit` / `native_decide`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

open ResolvedFeynmanSubgraph

variable {G : ResolvedFeynmanGraph}

set_option maxHeartbeats 3200000

/-- The concrete φ⁴ divergence measure family, registered file-locally (providable instance, NO forbidden
class). -/
noncomputable local instance phi4Inst616 : (H : FeynmanGraph) → DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

/-! ## Step 1 — global compatibility audit (verdict: componentwise, NO global τ) -/

/-- **body-616 (Step 1) — the target forest domain.**  The star-TOUCHING components of `z.2.1` — exactly the
`δ` a FOREST occurrence recovers.  These are the quotient components carrying the recovered inner forest. -/
noncomputable def phi4WTriplePrime_inv_forestDomain (z : Phi4WTriplePrimeInverseCodomain G) :
    Finset {x // x ∈ z.2.1.elements} :=
  z.2.1.elements.attach.filter (fun δ => phi4WTriplePrime_inv_isForestImage z δ)

theorem phi4WTriplePrime_inv_mem_forestDomain (z : Phi4WTriplePrimeInverseCodomain G)
    {δ : {x // x ∈ z.2.1.elements}} :
    δ ∈ phi4WTriplePrime_inv_forestDomain z ↔ phi4WTriplePrime_inv_isForestImage z δ := by
  unfold phi4WTriplePrime_inv_forestDomain
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_attach _ _, h⟩⟩

/-- **body-616 (Step 1) — the finite request index of `(δ, touched outer component)`.**  For each star-touching
`δ`, the outer components whose canonical star lands in `δ` (multiplicity / ID preserved). -/
noncomputable def phi4WTriplePrime_inv_forestRequestIndex (z : Phi4WTriplePrimeInverseCodomain G) :
    Finset ((δ : {x // x ∈ z.2.1.elements}) × {γ // γ ∈ z.1.1.elements}) :=
  (phi4WTriplePrime_inv_forestDomain z).sigma (fun δ => phi4WTriplePrime_touchedOuterComponents z δ)

variable {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}

/-- **body-616 (Step 1) — the source LOCAL star** of a touched outer component `i`, computed in the recovered
parent's boundary-completed ambient.  For DISTINCT occurrences these ambients DIFFER, so the sources are not
comparable across occurrences — hence NO global `τ`. -/
noncomputable def phi4WTriplePrime_inv_sourceLocalStar
    (O : Phi4WTriplePrime_RecoveredForestOccurrence z δ)
    (i : {x // x ∈ (phi4WTriplePrime_touchedOuterForest z δ).elements}) : VertexId :=
  phi4WTriplePrimeCanonicalSupply.starOf
    (phi4WTriplePrime_inv_recoveredParent O.input).boundaryCompletedResolvedGraph
    (phi4WTriplePrime_inv_recoveredInnerForest O.input
      (phi4WTriplePrime_inv_innerForest_CD_proof O.input))
    (phi4WTriplePrime_inv_innerComponent O.input i.1 i.2)

/-- **body-616 (Step 1) — the destination QUOTIENT star** of a touched outer component `i`, computed in the
global ambient `G` on `z.1.1`.  This is well-defined globally (a single `starOf G z.1.1`). -/
noncomputable def phi4WTriplePrime_inv_destQuotientStar (z : Phi4WTriplePrimeInverseCodomain G)
    (δ : {x // x ∈ z.2.1.elements})
    (i : {x // x ∈ (phi4WTriplePrime_touchedOuterForest z δ).elements}) : VertexId :=
  phi4WTriplePrimeCanonicalSupply.starOf G z.1.1 i.1

/-! ## Step 2 — the per-occurrence corrected forest graph -/

/-- **body-616 (Step 2, HEADLINE) — the per-occurrence corrected forest graph.**  The recovered inner forest
recontracted with the recovered parent's fresh canonical star, then pushed through the correcting permutation
`reconTau O.input`. -/
noncomputable def phi4WTriplePrime_inv_correctedForestGraph
    (O : Phi4WTriplePrime_RecoveredForestOccurrence z δ) : ResolvedFeynmanGraph :=
  ((phi4WTriplePrime_inv_recoveredInnerForest O.input
        (phi4WTriplePrime_inv_innerForest_CD_proof O.input)).contractWithStars
      (phi4WTriplePrimeCanonicalSupply.starOf
        (phi4WTriplePrime_inv_recoveredParent O.input).boundaryCompletedResolvedGraph
        (phi4WTriplePrime_inv_recoveredInnerForest O.input
          (phi4WTriplePrime_inv_innerForest_CD_proof O.input)))).mapPerm
    (phi4WTriplePrime_inv_reconTau O.input)

/-- **body-616 (Step 2, CONSUME 613) — the corrected graph reconstructs `δ`'s boundary-completion (RAW).**
This is exactly body-613's `phi4WTriplePrime_inv_recontraction_raw` — NO re-proof of recontraction geometry. -/
theorem phi4WTriplePrime_inv_correctedForestGraph_eq
    (O : Phi4WTriplePrime_RecoveredForestOccurrence z δ) :
    phi4WTriplePrime_inv_correctedForestGraph O = δ.1.boundaryCompletedResolvedGraph :=
  phi4WTriplePrime_inv_recontraction_raw O.input

/-- **body-616 (Step 2, survivor fix) — `reconTau` fixes the recovered-parent survivors.**  Re-exposed from
body-613 `reconTau_fix`. -/
theorem phi4WTriplePrime_inv_correctedForest_survivor_fix
    (O : Phi4WTriplePrime_RecoveredForestOccurrence z δ) {v : VertexId}
    (hv : v ∈ (phi4WTriplePrime_inv_recoveredParent O.input).vertices
        \ (phi4WTriplePrime_inv_recoveredInnerForest O.input
            (phi4WTriplePrime_inv_innerForest_CD_proof O.input)).vertices) :
    phi4WTriplePrime_inv_reconTau O.input v = v :=
  phi4WTriplePrime_inv_reconTau_fix O.input hv

/-- **body-616 (Step 2, local star → target star) — `reconTau` sends each source local star onto its
destination quotient star.**  Re-exposed from body-613 `reconTau_map`; NO strict cross-presentation star
equality (the shift is absorbed by `τ`). -/
theorem phi4WTriplePrime_inv_correctedForest_localStar_to_target
    (O : Phi4WTriplePrime_RecoveredForestOccurrence z δ)
    (i : {x // x ∈ (phi4WTriplePrime_touchedOuterForest z δ).elements}) :
    phi4WTriplePrime_inv_reconTau O.input (phi4WTriplePrime_inv_sourceLocalStar O i)
      = phi4WTriplePrime_inv_destQuotientStar z δ i :=
  phi4WTriplePrime_inv_reconTau_map O.input i

/-- **body-616 (Step 2, vertices) — the corrected graph's vertices are `δ`'s.** -/
theorem phi4WTriplePrime_inv_correctedForestGraph_vertices
    (O : Phi4WTriplePrime_RecoveredForestOccurrence z δ) :
    (phi4WTriplePrime_inv_correctedForestGraph O).vertices = δ.1.vertices := by
  rw [phi4WTriplePrime_inv_correctedForestGraph_eq O,
    ResolvedFeynmanSubgraph.boundaryCompletedResolvedGraph_vertices]

/-- **body-616 (Step 2, internalEdges) — the corrected graph's internal edges are `δ`'s.** -/
theorem phi4WTriplePrime_inv_correctedForestGraph_internalEdges
    (O : Phi4WTriplePrime_RecoveredForestOccurrence z δ) :
    (phi4WTriplePrime_inv_correctedForestGraph O).internalEdges = δ.1.internalEdges := by
  rw [phi4WTriplePrime_inv_correctedForestGraph_eq O,
    ResolvedFeynmanSubgraph.boundaryCompletedResolvedGraph_internalEdges]

/-! ## Step 3 — decompletion + reembed into the common quotient ambient -/

/-- **body-616 (Step 3, HEADLINE) — the decompleted corrected forest component** in the common quotient ambient
`Q := z.1.1.contractWithStars (starOf G z.1.1)`.  Its vertices / internal edges are the corrected graph's; its
external legs are the DECOMPLETED genuine ambient legs (`Q.externalLegs.filter`), never the synthetic boundary
legs. -/
noncomputable def phi4WTriplePrime_inv_correctedForestComponent
    (O : Phi4WTriplePrime_RecoveredForestOccurrence z δ) :
    ResolvedFeynmanSubgraph (z.1.1.contractWithStars (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1)) where
  vertices := (phi4WTriplePrime_inv_correctedForestGraph O).vertices
  internalEdges := (phi4WTriplePrime_inv_correctedForestGraph O).internalEdges
  externalLegs :=
    (z.1.1.contractWithStars (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1)).externalLegs.filter
      (fun ℓ => ℓ.attachedTo ∈ (phi4WTriplePrime_inv_correctedForestGraph O).vertices)
  vertices_subset := by
    rw [phi4WTriplePrime_inv_correctedForestGraph_vertices O]; exact δ.1.vertices_subset
  internalEdges_le := by
    rw [phi4WTriplePrime_inv_correctedForestGraph_internalEdges O]; exact δ.1.internalEdges_le
  externalLegs_le := Multiset.filter_le _ _
  edges_supported := by
    intro e he
    rw [phi4WTriplePrime_inv_correctedForestGraph_internalEdges O] at he
    obtain ⟨hs, ht⟩ := δ.1.edges_supported e he
    rw [phi4WTriplePrime_inv_correctedForestGraph_vertices O]
    exact ⟨hs, ht⟩
  legs_supported := fun _ℓ hℓ => (Multiset.mem_filter.mp hℓ).2

@[simp] theorem phi4WTriplePrime_inv_correctedForestComponent_vertices
    (O : Phi4WTriplePrime_RecoveredForestOccurrence z δ) :
    (phi4WTriplePrime_inv_correctedForestComponent O).vertices
      = (phi4WTriplePrime_inv_correctedForestGraph O).vertices := rfl

@[simp] theorem phi4WTriplePrime_inv_correctedForestComponent_internalEdges
    (O : Phi4WTriplePrime_RecoveredForestOccurrence z δ) :
    (phi4WTriplePrime_inv_correctedForestComponent O).internalEdges
      = (phi4WTriplePrime_inv_correctedForestGraph O).internalEdges := rfl

@[simp] theorem phi4WTriplePrime_inv_correctedForestComponent_externalLegs
    (O : Phi4WTriplePrime_RecoveredForestOccurrence z δ) :
    (phi4WTriplePrime_inv_correctedForestComponent O).externalLegs
      = (z.1.1.contractWithStars (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1)).externalLegs.filter
          (fun ℓ => ℓ.attachedTo ∈ (phi4WTriplePrime_inv_correctedForestGraph O).vertices) := rfl

/-- **body-616 (Step 3, RAW field — vertices) — the corrected component's vertices are `δ`'s.** -/
theorem phi4WTriplePrime_inv_correctedForestComponent_vertices_eq
    (O : Phi4WTriplePrime_RecoveredForestOccurrence z δ) :
    (phi4WTriplePrime_inv_correctedForestComponent O).vertices = δ.1.vertices :=
  phi4WTriplePrime_inv_correctedForestGraph_vertices O

/-- **body-616 (Step 3, RAW field — internalEdges) — the corrected component's internal edges are `δ`'s.** -/
theorem phi4WTriplePrime_inv_correctedForestComponent_internalEdges_eq
    (O : Phi4WTriplePrime_RecoveredForestOccurrence z δ) :
    (phi4WTriplePrime_inv_correctedForestComponent O).internalEdges = δ.1.internalEdges :=
  phi4WTriplePrime_inv_correctedForestGraph_internalEdges O

/-- **body-616 (Step 3, RAW field — externalLegs) — the corrected component's DECOMPLETED external legs are
`δ`'s.**  The synthetic boundary legs of the completed graph are dropped by the `Q`-leg filter, and `δ`'s
external-leg saturation on `Q` identifies the surviving genuine legs with `δ.1.externalLegs`. -/
theorem phi4WTriplePrime_inv_correctedForestComponent_externalLegs_eq
    (O : Phi4WTriplePrime_RecoveredForestOccurrence z δ) :
    (phi4WTriplePrime_inv_correctedForestComponent O).externalLegs = δ.1.externalLegs := by
  rw [phi4WTriplePrime_inv_correctedForestComponent_externalLegs,
    phi4WTriplePrime_inv_correctedForestGraph_vertices O]
  exact (externalLegs_eq_filter_of_saturated δ.1 (phi4WTriplePrime_inv_delta_saturated O.input)).symm

/-! ## Step 4 — the component round-trip (ordinary `Eq`, same fixed ambient `Q`) -/

/-- **body-616 (Step 4, VICTORY) — the corrected forest component round-trip is a genuine raw `Eq`.**  The
decompleted corrected component EQUALS the target quotient component `δ.1`.  Both inhabit the SAME fixed
quotient ambient `Q := z.1.1.contractWithStars (starOf G z.1.1)`, so no dependent transport is required and no
`HEq` / `cast` is introduced: the equality rests on the three RAW field equalities of Step 3.  This closes the
GEOMETRIC part of body-614's FOREST obligation; the global `Sum.inr ⟨B, mem⟩` TERM equation is left for
body-617. -/
theorem phi4WTriplePrime_inv_correctedForestComponent_roundtrip
    (O : Phi4WTriplePrime_RecoveredForestOccurrence z δ) :
    phi4WTriplePrime_inv_correctedForestComponent O = δ.1 :=
  ResolvedFeynmanSubgraph.ext
    (phi4WTriplePrime_inv_correctedForestComponent_vertices_eq O)
    (phi4WTriplePrime_inv_correctedForestComponent_internalEdges_eq O)
    (phi4WTriplePrime_inv_correctedForestComponent_externalLegs_eq O)

/-! ## Step 5 — the corrected FOREST collection (multiplicity preserved) -/

/-- **body-616 (Step 5) — the corrected component of a star-touching `δ`**, keyed on the star-touching witness
via the recovered occurrence.  On a star-free `δ` it defaults to `δ.1` (never used inside the forest
collection). -/
noncomputable def phi4WTriplePrime_inv_correctedForestComponentDom
    (z : Phi4WTriplePrimeInverseCodomain G) (δ : {x // x ∈ z.2.1.elements}) :
    ResolvedFeynmanSubgraph (z.1.1.contractWithStars (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1)) :=
  if hst : phi4WTriplePrime_inv_isForestImage z δ then
    phi4WTriplePrime_inv_correctedForestComponent
      (phi4WTriplePrime_recoveredForestOccurrence z δ hst)
  else δ.1

/-- **body-616 (Step 5) — the corrected component is EXACTLY the target component `δ.1`** (via the Step-4
round-trip in the star-touching case; the star-free default is `δ.1` by construction). -/
theorem phi4WTriplePrime_inv_correctedForestComponentDom_eq
    (z : Phi4WTriplePrimeInverseCodomain G) (δ : {x // x ∈ z.2.1.elements}) :
    phi4WTriplePrime_inv_correctedForestComponentDom z δ = δ.1 := by
  unfold phi4WTriplePrime_inv_correctedForestComponentDom
  by_cases hst : phi4WTriplePrime_inv_isForestImage z δ
  · rw [dif_pos hst]
    exact phi4WTriplePrime_inv_correctedForestComponent_roundtrip
      (phi4WTriplePrime_recoveredForestOccurrence z δ hst)
  · rw [dif_neg hst]

/-- **body-616 (Step 5) — the corrected-component map is injective** (it agrees with `Subtype.val`), so the
forest collection loses NO multiplicity — the `Finset.image` never dedups distinct occurrences. -/
theorem phi4WTriplePrime_inv_correctedForestComponentDom_injective
    (z : Phi4WTriplePrimeInverseCodomain G) :
    Function.Injective (phi4WTriplePrime_inv_correctedForestComponentDom z) := by
  intro δ₁ δ₂ h
  rw [phi4WTriplePrime_inv_correctedForestComponentDom_eq z δ₁,
    phi4WTriplePrime_inv_correctedForestComponentDom_eq z δ₂] at h
  exact Subtype.ext h

/-- **body-616 (Step 5, HEADLINE) — the corrected quotient FOREST collection.**  The `Finset.image` of the
target `forestDomain` under the corrected-component map — one corrected component per star-touching `δ`, with
an injectivity proof (Dedup / orbit-quotient FORBIDDEN). -/
noncomputable def phi4WTriplePrime_inv_correctedForest (z : Phi4WTriplePrimeInverseCodomain G) :
    Finset (ResolvedFeynmanSubgraph (z.1.1.contractWithStars (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1))) :=
  (phi4WTriplePrime_inv_forestDomain z).image (phi4WTriplePrime_inv_correctedForestComponentDom z)

/-- **body-616 (Step 5, membership iff) — a graph is a corrected forest component iff it is the target
component `δ.1` of some star-touching `δ`.** -/
theorem phi4WTriplePrime_inv_mem_correctedForest_iff (z : Phi4WTriplePrimeInverseCodomain G)
    {γ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1))} :
    γ ∈ phi4WTriplePrime_inv_correctedForest z ↔
      ∃ δ : {x // x ∈ z.2.1.elements}, phi4WTriplePrime_inv_isForestImage z δ ∧ δ.1 = γ := by
  unfold phi4WTriplePrime_inv_correctedForest
  rw [Finset.mem_image]
  constructor
  · rintro ⟨δ, hδ, hγ⟩
    exact ⟨δ, (phi4WTriplePrime_inv_mem_forestDomain z).mp hδ,
      (phi4WTriplePrime_inv_correctedForestComponentDom_eq z δ).symm.trans hγ⟩
  · rintro ⟨δ, hst, hγ⟩
    exact ⟨δ, (phi4WTriplePrime_inv_mem_forestDomain z).mpr hst,
      (phi4WTriplePrime_inv_correctedForestComponentDom_eq z δ).trans hγ⟩

/-- **body-616 (Step 5, multiplicity) — the corrected forest has EXACTLY as many components as the target
forest domain.**  No component count is lost (image injective). -/
theorem phi4WTriplePrime_inv_correctedForest_card (z : Phi4WTriplePrimeInverseCodomain G) :
    (phi4WTriplePrime_inv_correctedForest z).card = (phi4WTriplePrime_inv_forestDomain z).card :=
  Finset.card_image_of_injective _ (phi4WTriplePrime_inv_correctedForestComponentDom_injective z)

/-- **body-616 (Step 5, elements Eq) — the corrected forest collection IS the target forest domain's
components.**  Each corrected component equals its target `δ.1`, so the whole collection is exactly the
star-touching part of `z.2.1` — a raw `Finset` `Eq`. -/
theorem phi4WTriplePrime_inv_correctedForest_eq_forestDomain_image
    (z : Phi4WTriplePrimeInverseCodomain G) :
    phi4WTriplePrime_inv_correctedForest z
      = (phi4WTriplePrime_inv_forestDomain z).image (fun δ => δ.1) := by
  unfold phi4WTriplePrime_inv_correctedForest
  exact Finset.image_congr
    (fun δ _ => phi4WTriplePrime_inv_correctedForestComponentDom_eq z δ)

/-! ## Step 6 — interface for body-617 -/

/-- **body-616 (Step 6, INTERFACE) — the corrected quotient forest deliverable for body-617.**  Bundles: the
per-occurrence corrected forest components (each an exact raw recovery of its target `δ.1`, componentwise
`reconTau`-corrected), the exact target-sector recovery (`_roundtrip`), the exact multiplicity preservation
(`_card`), and the collection `elements` `Eq`.  The survivor sector is untouched (this body only rewrites the
FOREST components), and NO single global `τ` is introduced. -/
theorem phi4WTriplePrime_inv_correctedForest_interface (z : Phi4WTriplePrimeInverseCodomain G) :
    (∀ (δ : {x // x ∈ z.2.1.elements}) (O : Phi4WTriplePrime_RecoveredForestOccurrence z δ),
        phi4WTriplePrime_inv_correctedForestComponent O = δ.1)
      ∧ (phi4WTriplePrime_inv_correctedForest z).card = (phi4WTriplePrime_inv_forestDomain z).card
      ∧ phi4WTriplePrime_inv_correctedForest z
          = (phi4WTriplePrime_inv_forestDomain z).image (fun δ => δ.1) :=
  ⟨fun _δ O => phi4WTriplePrime_inv_correctedForestComponent_roundtrip O,
    phi4WTriplePrime_inv_correctedForest_card z,
    phi4WTriplePrime_inv_correctedForest_eq_forestDomain_image z⟩

end GaugeGeometry.QFT.Combinatorial
