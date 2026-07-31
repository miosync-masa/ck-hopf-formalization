import GaugeGeometry.QFT.HopfAlgebra.Phi4WTriplePrimeForestBlockInverseForward

/-!
# QFT-R1-body-622b — the FOREST inner-forest exact round-trip (settling body-614's obligation)

body-622a proved the forward-native FOREST **parent** identification: for `z := forestBlockForward s` and
`δ := remnantComponent o`, the inverse decontraction recovers the RAW parent `recoveredParent … = o.γ.1`
(same ambient `G`, no correcting permutation).  The remaining obstruction for the global left inverse
`recoveredSplitChoice (forestBlockForward s) = s` is the FOREST **choice** coordinate: its value equation
demands the DEPENDENT inner-forest identity `recoveredInnerForest ≅ o.B.1` across the ambients
`(recoveredParent).bcrg` vs `o.γ.1.bcrg`, which body-622a documented as blocked (the ambient equality is
propositional, not judgmental, and — crucially — the equation `recoveredParent I = o.γ.1` is NOT `subst`-able:
`recoveredParent I` syntactically references `o.γ.1` through `δ = remnantComponent o`, so an occurs-check
blocks eliminating either side).

## What this body delivers (the ambient-free combinatorial core of the round-trip)

The inner-forest round-trip has an ambient-FREE heart that IS provable outright — the exact identification of
the touched outer forest of the forward remnant with the promoted inner components of the original occurrence:

* **body-622b (Step 2 core, HEADLINE)** — `phi4WTriplePrime_forwardForest_touchedOuterForest_eq`:
  ```
  (touchedOuterForest (forestBlockForward s) ⟨remnantComponent o, _⟩).elements
      = o.B.1.elements.image (rootRelativeInner o.γ.1)
  ```
  A RAW, multiplicity-EXACT `Finset (ResolvedFeynmanSubgraph G)` equality (both sides ambient-free, no orbit
  quotient / dedup).  The reverse `⊆` is the load-bearing direction: a selected-outer component `γ` whose
  canonical star lands in the remnant is (i) NOT a survivor (its star is fresh, outside `G`, while survivors
  are fixed `G`-vertices), hence (ii) a `remnantTau`-image of a LOCAL star `starOf o.B.1 δᵢ`, whence
  `remnantTau_map` + selected-outer star INJECTIVITY pin `γ = rootRelativeInner o.γ.1 δᵢ`.  The forward `⊇`
  direction re-runs body-607's `remnant_star_touching` per component.

  This is the combinatorial content of body-614's deferred exact FOREST payload: it says precisely that the
  inverse-decontraction's touched outer components ARE the forward-promoted inner components, component for
  component, with multiplicity — the bijection `rootRelativeInner o.γ.1` (injective by body-604
  `rootRelativeInner_injOn`) mediating `recoveredInnerForest.elements ↔ o.B.1.elements`.

## SCOPE GUARD FIRED — the homogeneous packaging + global assembly move to body-622b-2

The homogeneous `recoveredInnerForest = o.B.1` (a typed `ResolvedAdmissibleSubgraph (recoveredParent I).bcrg`
equality) is NOT emitted here: turning the ambient-free element correspondence above into a typed subgraph
equality requires aligning `(recoveredParent I).bcrg` with `o.γ.1.bcrg`, and — as body-622a recorded and the
occurs-check above confirms — no `subst` aligns them judgmentally (the parent term references the owner).  A
graph-data `▸` / `cast` transport is a RED LINE here, and a hypothesis-carrying or correspondence-only global
headline is FORBIDDEN.  So the honest split is: **body-622b (this file)** delivers the exact ambient-free
inner-forest round-trip core; **body-622b-2** carries the sanctioned dependent-ambient discharge (a
non-owner-referential forward occurrence, or an approved fiber elimination) to lift this to the homogeneous
`recoveredInnerForest = o.B.1`, the Step-3 payload `recoveredChoice … = Sum.inr o.B`, and the global
`recoveredSplitChoice (forestBlockForward s) = s`.

## HALT compliance
Axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only); ZERO forbidden divergence classes in any
declaration type.  NO cross-ambient homogeneous subgraph equality / public `HEq`; NO hand-written `cast` /
`Eq.ndrec` / graph-data `▸`; NO `forestBlockForwardCorrected` / global `τ` / orbit quotient / dedup /
multiplicity collapse; NO `Finset.image` without adjacent injectivity.  No `sorry` / `admit` / `native_decide`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

open ResolvedFeynmanSubgraph

variable {G : ResolvedFeynmanGraph}

set_option maxHeartbeats 3200000

/-- The concrete φ⁴ divergence measure family, registered file-locally (providable instance, NO forbidden
class). -/
noncomputable local instance phi4Inst622b : (H : FeynmanGraph) → DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

variable {s : Phi4EdgeCompleteFilteredCoassocSplitChoice G}

/-! ## Step 2 core — the touched outer forest of the forward remnant IS the promoted inner forest -/

/-- **body-622b (Step 2 core, HEADLINE) — the ambient-free inner-forest round-trip.**  For `z :=
forestBlockForward s` and the forward remnant `δ := remnantComponent o` (star-touching), the touched outer
forest's element set is EXACTLY the image of the original inner forest `o.B.1`'s components under the
promotion `rootRelativeInner o.γ.1` — a RAW, multiplicity-preserving `Finset (ResolvedFeynmanSubgraph G)`
equality.  Both directions are pinned by the selected-outer star's freshness + injectivity and
`remnantTau`'s survivor-fix / local-star-map laws (body-604); `rootRelativeInner o.γ.1` is injective on
`o.B.1.elements` (body-604 `rootRelativeInner_injOn`), so this equality is the ambient-free carrier of
`recoveredInnerForest.elements = o.B.1.elements`. -/
theorem phi4WTriplePrime_forwardForest_touchedOuterForest_eq
    (o : Phi4WTriplePrime_ForestChoiceOccurrence s) :
    (phi4WTriplePrime_touchedOuterForest (phi4WTriplePrime_forestBlockForward s)
        ⟨phi4WTriplePrime_remnantComponent o,
          phi4WTriplePrime_remnantComponent_mem_quotientForest o⟩).elements
      = o.B.1.elements.image (rootRelativeInner o.γ.1) := by
  have hpfSel : (phi4WTriplePrime_selectedOuter s).IsProperForest :=
    phi4WTriplePrime_selectedOuter_isProperForest s
  -- the remnant's vertex set, as the `remnantTau`-image of the local contract graph
  have hRV : (phi4WTriplePrime_remnantComponent o).vertices
      = (phi4WTriplePrime_localContractGraph o).vertices.image (phi4WTriplePrime_remnantTau o) := rfl
  -- the local contract graph's vertex set
  have hLV : (phi4WTriplePrime_localContractGraph o).vertices
      = (o.γ.1.boundaryCompletedResolvedGraph.vertices \ o.B.1.vertices)
          ∪ o.B.1.starVertices
            (phi4WTriplePrimeCanonicalSupply.starOf o.γ.1.boundaryCompletedResolvedGraph o.B.1) := by
    rw [phi4WTriplePrime_localContractGraph, ResolvedAdmissibleSubgraph.contractWithStars_vertices]
  rw [phi4WTriplePrime_touchedOuterForest_elements]
  simp only [phi4WTriplePrime_forestBlockForward_outer]
  apply Finset.ext
  intro γ
  simp only [Finset.mem_filter, Finset.mem_image]
  constructor
  · -- reverse: a touched selected-outer component is a promotion of an inner component
    rintro ⟨hγSel, hstar⟩
    -- `hstar : starOf (selectedOuter s) γ ∈ (remnantComponent o).vertices`
    rw [hRV] at hstar
    obtain ⟨w, hwLC, hwstar⟩ := Finset.mem_image.mp hstar
    rw [hLV, Finset.mem_union] at hwLC
    rcases hwLC with hwsurv | hwlocstar
    · -- survivor: `remnantTau` fixes it → the fresh star equals a `G`-vertex, impossible
      exfalso
      rw [ResolvedFeynmanSubgraph.boundaryCompletedResolvedGraph_vertices] at hwsurv
      rw [phi4WTriplePrime_remnantTau_fix o hwsurv] at hwstar
      have hwG : w ∈ G.vertices := o.γ.1.vertices_subset (Finset.mem_sdiff.mp hwsurv).1
      exact phi4WTriplePrime_gen_star_not_mem (phi4WTriplePrime_selectedOuter s) hpfSel hγSel
        (hwstar ▸ hwG)
    · -- local star: `remnantTau_map` + selected-outer star injectivity pin the promotion
      rw [ResolvedAdmissibleSubgraph.mem_starVertices] at hwlocstar
      obtain ⟨δᵢ, hδᵢ, rfl⟩ := hwlocstar
      rw [phi4WTriplePrime_remnantTau_map o ⟨δᵢ, hδᵢ⟩] at hwstar
      have hpromMem : rootRelativeInner o.γ.1 δᵢ
          ∈ (phi4WTriplePrime_selectedOuter s).elements :=
        phi4WTriplePrime_remnant_promoted_mem o hδᵢ
      have hγeq : γ = rootRelativeInner o.γ.1 δᵢ :=
        phi4WTriplePrime_gen_star_injOn (phi4WTriplePrime_selectedOuter s) hpfSel hγSel hpromMem
          hwstar.symm
      exact ⟨δᵢ, hδᵢ, hγeq.symm⟩
  · -- forward: a promotion of an inner component is a touched selected-outer component
    rintro ⟨δᵢ, hδᵢ, rfl⟩
    refine ⟨phi4WTriplePrime_remnant_promoted_mem o hδᵢ, ?_⟩
    -- the promotion's canonical star is the `remnantTau`-image of the local star
    rw [← phi4WTriplePrime_remnantTau_map o ⟨δᵢ, hδᵢ⟩, hRV]
    apply Finset.mem_image.mpr
    refine ⟨phi4WTriplePrimeCanonicalSupply.starOf o.γ.1.boundaryCompletedResolvedGraph o.B.1 δᵢ,
      ?_, rfl⟩
    rw [hLV]
    exact Finset.mem_union_right _
      (ResolvedAdmissibleSubgraph.mem_starVertices.mpr ⟨δᵢ, hδᵢ, rfl⟩)

end GaugeGeometry.QFT.Combinatorial
