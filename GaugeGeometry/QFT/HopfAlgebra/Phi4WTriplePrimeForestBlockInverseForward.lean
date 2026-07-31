import GaugeGeometry.QFT.HopfAlgebra.Phi4WTriplePrimeForestBlockForwardInverse

/-!
# QFT-R1-body-622a — the forward-native FOREST parent round-trip (left-inverse FOREST core)

The left inverse `phi4WTriplePrime_recoveredSplitChoice (phi4WTriplePrime_forestBlockForward s) = s`
is the mirror of body-621's right inverse.  Its outer coordinate demands
`phi4WTriplePrime_recoveredOuter (forestBlockForward s) = s.outer`, whose FOREST components are recovered
from the remnants `δ = remnantComponent o` of the source occurrences `o`.  The load-bearing FOREST fact is
the **forward-native parent identification**: the inverse decontraction of `remnantComponent o` recovers
`o.γ.1` EXACTLY (a raw `ResolvedFeynmanSubgraph G` equality — same ambient, no relabeling).

## What closes cleanly (this body)

* **Step 1 (helper)** — `phi4WTriplePrime_internalEdges_eq_filter_of_edgeComplete`: a W‴ (edge-complete)
  component's internal edges ARE the ambient's induced filter.
* **Step 2 (vertex bridge, HEADLINE core)** — `phi4WTriplePrime_forwardForest_recoveredParent_verts_eq`:
  for `z := forestBlockForward s` and `δ := remnantComponent o`, the recovered-parent region equals
  `o.γ.1.vertices`.  The proof composes body-609's `inv_retarget_mem_delta_iff` (region ⇔ `A`-retarget in
  `δ`) with body-604's `phi_mem_Ltau_iff` (`A`-retarget in the remnant ⇔ in `o.γ`), which share the
  IDENTICAL retarget LHS (`z.1.1 = selectedOuter s` definitionally).  NO correcting permutation `τ` is
  touched — the parent region is genuine `G`-native data.
* **Step 3 (HEADLINE)** — `phi4WTriplePrime_forwardForest_recoveredParent_eq`: the recovered parent equals
  `o.γ.1` as a raw `ResolvedFeynmanSubgraph G` (`ext`: vertices from Step 2, internal edges from Step 1 +
  `o.γ.1` edge-completeness, external legs from `o.γ.1` saturation — all induced-filter identities).

## SCOPE GUARD FIRED — the global left inverse moves to body-622b

The global headline `recoveredSplitChoice (forestBlockForward s) = s` also demands, in its FOREST **choice**
coordinate, the value equation `recoveredChoice (forestBlockForward s) ⟨o.γ.1, _⟩ = Sum.inr o.B`.  By
body-620's `recoveredChoice_forest_value` this equals `Sum.inr ⟨recoveredInnerForest, mem⟩`, so it forces the
DEPENDENT identity `recoveredInnerForest ≅ o.B.1` across the ambients
`(recoveredParent).boundaryCompletedResolvedGraph` vs `o.γ.1.boundaryCompletedResolvedGraph`.  Step 3 makes
those two graphs PROPOSITIONALLY equal, but NOT definitionally — so the equation is a cross-ambient
graph-data transport (`heq ▸ recoveredInnerForest = o.B.1`).  That is EXACTLY body-614's deferred exact
`Sum.inr ⟨B, mem⟩` obligation, on which body-615 truthfully STOPPED (the `toResolvedClass` / mapPerm-orbit
verdict) and which body-617 discharged ONLY via `forestBlockForwardCorrected` — FORBIDDEN here.  The
sanctioned `heq_of_eq`-after-`subst` fiber discharge (body-621) does NOT apply: neither `recoveredParent` nor
`o.γ.1` is a substitutable owner variable, so no `subst` aligns the ambient judgmentally.  A truthful partial
delivery is correct — the FOREST inner-forest transport is isolated as the sole remaining arc, delivered in
**body-622b**, and NO hypothesis-carrying global headline is emitted here.

## HALT compliance
Axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only); ZERO forbidden divergence classes in any
declaration type.  NO cross-ambient homogeneous subgraph equality / public `HEq`; NO hand-written `cast` /
`Eq.ndrec` / graph-data `▸`; NO `forestBlockForwardCorrected` / global `τ` / orbit quotient / dedup; NO whole
`Equiv` / summand / `sum_bij` / alpha / coassoc.  No `sorry` / `admit` / `native_decide`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

open ResolvedFeynmanSubgraph

variable {G : ResolvedFeynmanGraph}

set_option maxHeartbeats 3200000

/-- The concrete φ⁴ divergence measure family, registered file-locally (providable instance, NO forbidden
class). -/
noncomputable local instance phi4Inst622 : (H : FeynmanGraph) → DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

/-! ## Step 1 — a W‴ (edge-complete) component's internal edges ARE the ambient induced filter -/

/-- **body-622a (Step 1) — internal edges of an internal-edge-complete component are the induced filter.**
The forward `≤` is `internalEdges_le` + `edges_supported`; the reverse `≤` is edge-completeness itself. -/
theorem phi4WTriplePrime_internalEdges_eq_filter_of_edgeComplete
    (γ : ResolvedFeynmanSubgraph G) (hEC : ResolvedInternalEdgeComplete γ) :
    γ.internalEdges
      = G.internalEdges.filter (fun e => e.source ∈ γ.vertices ∧ e.target ∈ γ.vertices) :=
  le_antisymm
    (Multiset.le_filter.mpr ⟨γ.internalEdges_le, fun e he => γ.edges_supported e he⟩)
    hEC

/-! ## Step 2 — the forward-native recovered-parent vertex bridge -/

/-- **body-622a (Step 2, vertex bridge) — the recovered-parent region of the remnant `δ = remnantComponent o`
is `o.γ.1`'s vertex set.**  For `z := forestBlockForward s`, `z.1.1` is definitionally `selectedOuter s`, so
body-609's region membership iff (`inv_retarget_mem_delta_iff`) and body-604's remnant membership iff
(`phi_mem_Ltau_iff`) share the same `A`-retarget LHS: a `G`-vertex lies in the recovered-parent region iff
its retarget lands in the remnant iff it lies in `o.γ`.  Both regions sit inside `G.vertices`, so the
membership iff on `G.vertices` upgrades to a `Finset` equality.  NO `τ`. -/
theorem phi4WTriplePrime_forwardForest_recoveredParent_verts_eq
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G)
    (o : Phi4WTriplePrime_ForestChoiceOccurrence s) :
    phi4WTriplePrime_inv_recoveredParent_verts (phi4WTriplePrime_forestBlockForward s)
        ⟨phi4WTriplePrime_remnantComponent o,
          phi4WTriplePrime_remnantComponent_mem_quotientForest o⟩
      = o.γ.1.vertices := by
  have hst : phi4WTriplePrime_inv_isForestImage (phi4WTriplePrime_forestBlockForward s)
      ⟨phi4WTriplePrime_remnantComponent o,
        phi4WTriplePrime_remnantComponent_mem_quotientForest o⟩ :=
    phi4WTriplePrime_remnant_star_touching o
  have I := phi4WTriplePrime_forestDecontractionInput_of_starTouching
    (phi4WTriplePrime_forestBlockForward s) hst
  apply Finset.ext
  intro v
  constructor
  · intro hv
    have hvG : v ∈ G.vertices :=
      phi4WTriplePrime_inv_recoveredParent_verts_subset _ _ hv
    exact (phi4WTriplePrime_phi_mem_Ltau_iff o hvG).mp
      ((phi4WTriplePrime_inv_retarget_mem_delta_iff I hvG).mpr hv)
  · intro hv
    have hvG : v ∈ G.vertices := o.γ.1.vertices_subset hv
    exact (phi4WTriplePrime_inv_retarget_mem_delta_iff I hvG).mp
      ((phi4WTriplePrime_phi_mem_Ltau_iff o hvG).mpr hv)

/-! ## Step 3 — the forward-native recovered-parent identification (raw `G`-subgraph equality) -/

/-- **body-622a (Step 3, HEADLINE) — the inverse decontraction of `remnantComponent o` recovers `o.γ.1`
EXACTLY.**  A raw `ResolvedFeynmanSubgraph G` equality (SAME ambient `G`, no relabeling): the vertices are
Step 2's bridge, and because both the recovered parent (induced) and `o.γ.1` (W‴ edge-complete + saturated)
present their internal edges / external legs as the SAME `G`-induced filter on the SAME vertex set, all three
carrier fields coincide.  This is the FOREST forward-native core of the left inverse — closed from 604/609
alone, with NO correcting permutation `τ` and NO cross-ambient transport. -/
theorem phi4WTriplePrime_forwardForest_recoveredParent_eq
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G)
    (o : Phi4WTriplePrime_ForestChoiceOccurrence s) :
    phi4WTriplePrime_inv_recoveredParent
        (phi4WTriplePrime_forestDecontractionInput_of_starTouching
          (phi4WTriplePrime_forestBlockForward s)
          (δ := ⟨phi4WTriplePrime_remnantComponent o,
            phi4WTriplePrime_remnantComponent_mem_quotientForest o⟩)
          (phi4WTriplePrime_remnant_star_touching o))
      = o.γ.1 := by
  have hV := phi4WTriplePrime_forwardForest_recoveredParent_verts_eq s o
  have hSat : ResolvedExternalLegSaturated G o.γ.1 := phi4WTriplePrime_gamma_saturated o
  have hEC : ResolvedInternalEdgeComplete o.γ.1 :=
    ((mem_phi4WTriplePrimeIndex G s.outer).mp s.outer_mem).2.2.2.2.2.2 o.γ.1 o.γ.2
  apply ResolvedFeynmanSubgraph.ext
  · rw [phi4WTriplePrime_inv_recoveredParent_vertices]
    exact hV
  · rw [phi4WTriplePrime_inv_recoveredParent_internalEdges, hV]
    exact (phi4WTriplePrime_internalEdges_eq_filter_of_edgeComplete o.γ.1 hEC).symm
  · rw [phi4WTriplePrime_inv_recoveredParent_externalLegs, hV]
    exact (externalLegs_eq_filter_of_saturated o.γ.1 hSat).symm

end GaugeGeometry.QFT.Combinatorial
