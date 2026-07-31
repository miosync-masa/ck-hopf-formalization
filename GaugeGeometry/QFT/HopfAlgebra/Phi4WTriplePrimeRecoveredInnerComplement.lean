import GaugeGeometry.QFT.HopfAlgebra.Phi4WTriplePrimeRecoveredInnerCD

/-!
# QFT-R1-body-612 — recovered inner complement exact residual

Body-609 left the named PROOF FRONTIER `phi4WTriplePrime_inv_innerForest_complement_pos` (the recovered inner
forest's complement is positive).  This body DISCHARGES it — NOT via the body-606 inequality route, but by the
EXACT RESIDUAL IDENTITY: the recovered inner forest's complement in the parent's boundary-completed ambient is
RAW-equal to `parentExactEdges` (body-610), whose cardinality equals `δ`'s internal-edge count (positive, from
`B`'s componentwise positive-edge properness).  Then it UNCONDITIONALIZES `recoveredInnerForest_mem`: all three
conditional frontier hypotheses are now discharged by bodies 610/611/612, so the live W‴ inner forest membership
takes only `I`.

## Strategy
* Step 1 — the inner aggregate `internalEdges` equals the touched-outer-forest's (component transport, dedup via
  the innerComponent map injectivity on the touched-forest `attach`, proved from pairwise-disjointness +
  component vertex-nonemptiness — NO forget injectivity).
* Step 2 — the load-bearing RAW complement identity: `complementEdges = parentExactEdges`, via
  `boundaryCompletedResolvedGraph_internalEdges` + the body-610 parent internal-edge decomposition +
  Step 1 + `add_tsub_cancel_left`.
* Step 3 — cardinal transport: `complementEdges.card = δ.internalEdges.card` (body-610 `_delta_internalEdges_eq`
  + `Multiset.card_map`; no retarget injectivity needed).
* Step 4 — frontier discharge (`0 < δ.internalEdges.card` from `B.IsProperForest`) + UNCONDITIONAL live W‴
  inner forest membership (all three conditional hypotheses discharged with the 610/611/612 proofs).

## HALT compliance
Axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only); ZERO forbidden divergence classes in any
declaration type; a pure count/multiset residual identity — NO degree / `physicalExternalLegCount`; no topology
or CD re-proof (READ from 610/611); no fabricated map injectivity (owner-disjointness + nonemptiness); no `s` /
`componentEquiv`; `_recontraction_recovery` untouched; no new `class` / `structure` / permanent `instance`;
no `sorry` / `admit` / `native_decide`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

open ResolvedFeynmanSubgraph

variable {G : ResolvedFeynmanGraph}

set_option maxHeartbeats 3200000

/-- The concrete φ⁴ divergence measure family, registered file-locally (providable instance, NO forbidden
class). -/
noncomputable local instance phi4Inst612 : (H : FeynmanGraph) → DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

/-! ## Step 1 — inner aggregate internal-edge equality. -/

/-- **body-612 (Step 1) — the recovered inner forest's aggregate internal edges are the touched outer forest's.**
Each transported component carries its outer component's internal edges (`innerComponent_internalEdges`); the
`innerComponent` map is injective on the touched-forest `attach` (equal transported components share a vertex
set, and distinct touched components are pairwise vertex-disjoint + vertex-nonempty), so `Finset.sum_image`
de-dups to the touched forest's aggregate. -/
theorem phi4WTriplePrime_inv_recoveredInnerForest_internalEdges_eq
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) :
    (phi4WTriplePrime_inv_recoveredInnerForest I (phi4WTriplePrime_inv_innerForest_CD_proof I)).internalEdges
      = (phi4WTriplePrime_touchedOuterForest z δ).internalEdges := by
  classical
  have hNE : z.1.1.HasNonemptyComponents :=
    (((mem_phi4WTriplePrimeIndex G z.1.1).mp z.1.2).2.2.2.2.1).2.1
  have hinj : Set.InjOn
      (fun γ : {x // x ∈ (phi4WTriplePrime_touchedOuterForest z δ).elements} =>
        phi4WTriplePrime_inv_innerComponent I γ.1 γ.2)
      ↑(phi4WTriplePrime_touchedOuterForest z δ).elements.attach := by
    intro γ₁ _ γ₂ _ heq
    apply Subtype.ext
    by_contra hne
    have hv : γ₁.1.vertices = γ₂.1.vertices := by
      have hcv := congrArg ResolvedFeynmanSubgraph.vertices heq
      simpa only [phi4WTriplePrime_inv_innerComponent_vertices] using hcv
    have hγ₁A : γ₁.1 ∈ z.1.1.elements := phi4WTriplePrime_inv_touchedForest_subset_A γ₁.2
    have hγ₂A : γ₂.1 ∈ z.1.1.elements := phi4WTriplePrime_inv_touchedForest_subset_A γ₂.2
    have hdisj : _root_.Disjoint γ₁.1.vertices γ₂.1.vertices :=
      z.1.1.pairwiseDisjoint hγ₁A hγ₂A hne
    have hpos : 0 < γ₁.1.vertices.card := hNE γ₁.1 hγ₁A
    obtain ⟨v, hv1⟩ := Finset.card_pos.mp hpos
    have hv2 : v ∈ γ₂.1.vertices := hv ▸ hv1
    exact Finset.disjoint_left.mp hdisj hv1 hv2
  rw [ResolvedAdmissibleSubgraph.internalEdges,
    phi4WTriplePrime_inv_recoveredInnerForest_elements, Finset.sum_image hinj]
  simp only [phi4WTriplePrime_inv_innerComponent_internalEdges]
  rw [Finset.sum_attach, ResolvedAdmissibleSubgraph.internalEdges]

/-! ## Step 2 — the load-bearing RAW complement identity. -/

/-- **body-612 (Step 2) — the recovered inner forest's complement in the parent's boundary-completed ambient is
RAW-equal to `parentExactEdges`.**  The ambient's internal edges are the recovered parent's
(`boundaryCompletedResolvedGraph_internalEdges`), which decompose as touched-forest + Exact (body-610); the
inner aggregate is exactly the touched-forest half (Step 1), so the complement cancels to the Exact half. -/
theorem phi4WTriplePrime_inv_recoveredInnerForest_complementEdges_eq
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) :
    (phi4WTriplePrime_inv_recoveredInnerForest I (phi4WTriplePrime_inv_innerForest_CD_proof I)).complementEdges
      = phi4WTriplePrime_inv_parentExactEdges z δ := by
  rw [ResolvedAdmissibleSubgraph.complementEdges,
    ResolvedFeynmanSubgraph.boundaryCompletedResolvedGraph_internalEdges,
    phi4WTriplePrime_inv_recoveredParent_internalEdges_decomp I,
    phi4WTriplePrime_inv_recoveredInnerForest_internalEdges_eq I,
    add_tsub_cancel_left]

/-! ## Step 3 — cardinal transport. -/

/-- **body-612 (Step 3) — the recovered inner forest's complement cardinality equals `δ`'s internal-edge count.**
Step 2 identifies the complement with `parentExactEdges`; body-610's `_delta_internalEdges_eq` presents `δ`'s
internal edges as the Exact edges retargeted, so their cardinalities agree (`Multiset.card_map`, no retarget
injectivity needed). -/
theorem phi4WTriplePrime_inv_recoveredInnerForest_complementEdges_card
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) :
    (phi4WTriplePrime_inv_recoveredInnerForest I
        (phi4WTriplePrime_inv_innerForest_CD_proof I)).complementEdges.card
      = δ.1.internalEdges.card := by
  rw [phi4WTriplePrime_inv_recoveredInnerForest_complementEdges_eq I,
    phi4WTriplePrime_inv_delta_internalEdges_eq I, Multiset.card_map]

/-! ## Step 4 — frontier discharge + UNCONDITIONAL live W‴ inner forest membership. -/

/-- **body-612 (Step 4) — the body-609 `_innerForest_complement_pos` proof frontier is DISCHARGED.**  The
complement cardinality equals `δ`'s internal-edge count (Step 3), which is positive because `B` (`z.2.1`) is a
proper forest with componentwise positive internal edges, applied at `δ ∈ B.elements`. -/
theorem phi4WTriplePrime_inv_innerForest_complement_pos_proof
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) :
    phi4WTriplePrime_inv_innerForest_complement_pos I (phi4WTriplePrime_inv_innerForest_CD_proof I) := by
  have hBpf : z.2.1.IsProperForest :=
    ((mem_phi4WTriplePrimeIndex
      (z.1.1.contractWithStars (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1)) z.2.1).mp
        z.2.2).2.2.2.2.1
  have hδpos : 0 < δ.1.internalEdges.card := hBpf.2.2.2.1 δ.1 δ.2
  unfold phi4WTriplePrime_inv_innerForest_complement_pos
  rw [phi4WTriplePrime_inv_recoveredInnerForest_complementEdges_card I]
  exact hδpos

/-- **body-612 (VICTORY) — the recovered inner forest is a LIVE W‴ forest, UNCONDITIONALLY.**  All three
conditional hypotheses of the body-609 membership are discharged by the 610/611/612 proofs (topology, CD,
complement positivity), so the membership takes ONLY `I`. -/
theorem phi4WTriplePrime_inv_recoveredInnerForest_mem_proof
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) :
    phi4WTriplePrime_inv_recoveredInnerForest I (phi4WTriplePrime_inv_innerForest_CD_proof I)
      ∈ phi4WTriplePrimeIndex (phi4WTriplePrime_inv_recoveredParent I).boundaryCompletedResolvedGraph :=
  phi4WTriplePrime_inv_recoveredInnerForest_mem I (phi4WTriplePrime_inv_innerForest_CD_proof I)
    (phi4WTriplePrime_inv_recoveredParent_ForgetTopology_proof I)
    (phi4WTriplePrime_inv_innerForest_complement_pos_proof I)

end GaugeGeometry.QFT.Combinatorial
