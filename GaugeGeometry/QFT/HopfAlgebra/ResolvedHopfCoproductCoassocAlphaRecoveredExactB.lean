import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaRemnantCorrespondence
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocMultiStarForestTag

/-!
# R-6c-body-506 — recovered-choice exact-B from its own tag construction (PROVED)

Five-hundred-and-sixth genuine-body step — closing body-505's identified blocker WITHOUT a backward socket.  Body-495's
remnant correspondence consumes `OccInv` at the RECOVERED `z` (not the forward `q`), which the forward-only faithful
socket does not cover.  But no backward socket is needed: the recovered split's forest-choice `B` is not an unknown datum
— it is the value `recoverChoiceAlphaValue` INSERTED, namely `T.forestTag z γ`.  So the recovered occurrence's `B` reads
its own construction, and `forestTag_of_parent` returns that tag to the inner de-contracted index.

## The generic recovered exact-B

`recoveredOccurrence_B_heq_innerIdx_alpha` — for a recovered forest occurrence at `z`, with `hForest` / `hFT` wiring the
recovered forest region to `M.forestRecoveredMulti` and `T.forestTag` to `M.forestTag`:

```text
HEq (forestComponentOccurrence (T.recoveredPreimageAlphaValue z) γ).B (M.innerIdx z δ)
```

under `hp : occurrence.γ.1 = M.parent z δ`.  Route: the occurrence's `B` is `Sum.inr.inj` of its own
`recoverChoiceAlphaValue` forest branch (`= Sum.inr (T.forestTag z γ)`); `hFT` sends that to `M.forestTag`; `hp` aligns
the parent subtype; `forestTag_of_parent` (body-…, `= M.innerIdx`) closes.  This is the BACKWARD dual of body-505's forward
`forestTag_agrees` — same exact-B, different ownership: forward recovers `q`'s own `B` geometrically, backward recovers the
`forestTag` it wrote into the recovered choice.  Neither `ForwardOcc` nor `OccRaw` appears.

## Status

Step 1 (this generic theorem) is banked.  Step 2 (porting body-495 `remnant_mem_alpha`'s two `innerIdx_occurrence`
consumers onto it) and Step 3 (canonical specialization + assembly) are the body-507 continuation (per the plan's
safe-stop — the generic recovered exact-B is the self-contained mathematical core; the remnant-correspondence re-plumbing
is deferred rather than rushed).

Per the HALT/guards: the forward socket is NOT extended to arbitrary recovered `z`; no new backward occurrence socket is
built; `hidx` is NOT back-computed from `remnant_mem` / quotient HEq / coassoc; body-489 is NOT used to derive `hidx`; the
legacy body-495 stays a valid conditional (NON-destructive); `quot_eq` / `legComplete` are NOT entered; strict `StarProm`
/ `InnerStarRaw` stay ZERO; NO unconditional-coassoc claim.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO
`promote_collapse` / singleton / floor-297.
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
set_option maxHeartbeats 1600000

variable {D : ResolvedCoproductProperForestData}
  {Fmem : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedFilteredConcreteSummandValueSupply D}

namespace ResolvedRegionTagAlphaValueSupply

/-- **R-6c-body-506 ∎ — the recovered forest occurrence's `B` is its own inserted `forestTag`, hence the inner index.**
No forward socket, no legacy `OccRaw`: the recovered choice reads the `forestTag` it wrote, and `forestTag_of_parent`
returns it to `M.innerIdx z δ`. -/
theorem recoveredOccurrence_B_heq_innerIdx_alpha (T : ResolvedRegionTagAlphaValueSupply Fmem V)
    (M : ResolvedMultiStarDecontractionSupply D) (Fstar : ResolvedCanonicalStarFacts D)
    (Measure : ResolvedMeasureLeafSupply D)
    (hForest : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
      (T.Closure.Assembly.Region.forestRecovered z).elements
        = (M.forestRecoveredMulti Fstar z).elements)
    (hFT : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
      (γ' : {x : ResolvedFeynmanSubgraph G // x ∈ (T.Closure.unionOuterAlphaValue z).1.elements})
      (h : γ'.1 ∈ (T.Closure.Assembly.Region.forestRecovered z).elements)
      (h' : γ'.1 ∈ (M.forestRecoveredMulti Fstar z).elements),
      T.forestTag z γ' h = M.forestTag Fstar z ⟨γ'.1, h'⟩)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (γ : {x : {y : ResolvedFeynmanSubgraph G // y ∈ (T.Closure.unionOuterAlphaValue z).1.elements} //
      x ∈ ResolvedCoassocSplitChoice.forestComponents (T.recoveredPreimageAlphaValue z)})
    (δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) // x ∈ forestDomain z})
    (hp : (ResolvedCoassocSplitChoice.forestComponentOccurrence (T.recoveredPreimageAlphaValue z) γ).γ.1
      = M.parent z δ) :
    HEq (ResolvedCoassocSplitChoice.forestComponentOccurrence (T.recoveredPreimageAlphaValue z) γ).B
      (M.innerIdx z δ) := by
  set o := ResolvedCoassocSplitChoice.forestComponentOccurrence (T.recoveredPreimageAlphaValue z) γ with ho
  have hFrec : γ.1.1 ∈ (T.Closure.Assembly.Region.forestRecovered z).elements :=
    (T.mem_forestComponents_iff_alpha z γ.1).mp γ.2
  have hfr : γ.1.1 ∈ (M.forestRecoveredMulti Fstar z).elements := by rw [← hForest]; exact hFrec
  have hrc : T.recoverChoiceAlphaValue z γ.1 (Finset.mem_attach _ _)
      = Sum.inr (T.forestTag z γ.1 hFrec) := by
    rw [recoverChoiceAlphaValue, if_neg (T.forest_notMem_left z γ.1 hFrec),
      if_neg (T.forest_notMem_right z γ.1 hFrec), dif_pos hFrec]
  have hoB : o.B = T.forestTag z γ.1 hFrec := Sum.inr.inj (o.hchoice.symm.trans hrc)
  have hp' : γ.1.1 = M.parent z δ := hp
  have hmem' : M.parent z δ ∈ (M.forestRecoveredMulti Fstar z).elements := hp' ▸ hfr
  rw [hoB, hFT z γ.1 hFrec hfr]
  have hsubeq : (⟨γ.1.1, hfr⟩ : {y : ResolvedFeynmanSubgraph G // y ∈ (M.forestRecoveredMulti Fstar z).elements})
      = ⟨M.parent z δ, hmem'⟩ := Subtype.ext hp'
  refine HEq.trans ?_ (M.forestTag_of_parent Fstar Measure z δ hmem')
  exact hsubeq ▸ HEq.rfl

end ResolvedRegionTagAlphaValueSupply

end GaugeGeometry.QFT.Combinatorial
