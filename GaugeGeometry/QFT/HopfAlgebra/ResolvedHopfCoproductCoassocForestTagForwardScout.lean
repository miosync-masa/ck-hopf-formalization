import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestValueEqScout

/-!
# R-6c-body-198 — forest tag forward scout: `forestTag_forward_eq` reduced to a choice-value identity

Hundred-and-ninety-eighth genuine-body step, a scout of body-196's fresh leaf `forestTag_forward_eq` before proving
it.  The audit found its value step is `Sum.inr.inj`-trivial and its genuine content is a **choice-value identity**
(equivalently the parent-recovery of the forward round-trip); it fielded that as one clean leaf and proved the
reduction.

## The audit — the value step is trivial, the content is parent recovery

Concretely, `forestTag_fwd q γ h` is intended to be `(componentToForest-recovered occurrence).B`, where
`ForestPrimitiveIndex.toOccurrence` bundles the occurrence `(occ.γ, occ.B, hchoice : choiceAt occ.γ = inr occ.B)`
*for free* (`hchoice = Classical.choose_spec`).  Since `q.2 γ = choiceAt γ` (as `ForestBlockDomType D G =
ResolvedCoassocSplitChoice D G`), the leaf's hypothesis `q.2 γ = inr B` is literally `choiceAt γ = inr B`.  So the
whole leaf reduces to the **choice-value identity**

```text
forest_choiceAt_eq : q.2 γ = inr (forestTag_fwd q γ h)
```

("the forest tag reconstructed on the forward image is `q`'s own choice value at `γ`") — whose real content is the
parent recovery `occ.γ = γ` (the forward round-trip parent identity), reusing `toOccurrence`'s `hchoice` and the
`Sum.inr.inj (hc₁.symm.trans hc₂)` kernel (`ResolvedOccurrenceParentInjectivitySupply` / `OccurrenceInjectivityBody`).
The de-contraction facts `remnantGen` / `remnantClass_eq` (bodies 126) are **not** the tool here — they are
value/class-level and feed the *dual* `forward_quotient_heq`, not this index-level `Eq`.

## The reduction (PROVED)

`ResolvedForestTagForwardDecompositionSupply D S Region` fields the forward forest tag `forestTag_fwd` and the
choice-value identity `forest_choiceAt_eq`.  Then `.forestTag_forward_eq` is **proved** by `Sum.inr.inj`:

```text
q.2 γ = inr B  and  q.2 γ = inr (forestTag_fwd q γ h)   ⟹   forestTag_fwd q γ h = B
```

`.toForestValueEqDecompositionSupply` (given the body-188 tag pinning `recoverChoice_forest_pin`) produces body-196's
supply — so the backward-choice `HEq` reduces, through bodies 198/196/194/193/192, to the single choice-value
identity `forest_choiceAt_eq` (i.e. the parent recovery).

## Consequence

The backward-choice residual is now the single choice-value identity `forest_choiceAt_eq` — a homogeneous
`Bool ⊕ ForestIdx` equality whose only content is the forward round-trip parent recovery; everything else on the
leaf (`Sum.inr.inj`, the value extraction) is proved.  `forward_quotient_heq` (the dual, heavier) is untouched.

Per the HALT: `forest_choiceAt_eq`'s body (the parent recovery / sector round-trip) is not entered; the tag pinning
is reused from body-188; only the `Sum.inr.inj` reduction is proved.

Landed:

* `ResolvedForestTagForwardDecompositionSupply D S Region` — the forward forest tag + the choice-value identity;
* `.forestTag_forward_eq` — body-196's leaf (PROVED from the choice-value identity by `Sum.inr.inj`);
* `.toForestValueEqDecompositionSupply` — body-196's supply (given the body-188 tag pinning).

Scout / toolkit body (like body-196).  No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- **R-6c-body-198 — the forest tag forward decomposition supply.**  The forward image's forest tag and the
choice-value identity (`q.2 γ = inr forestTag_fwd`), whose only content is the forward round-trip parent recovery. -/
structure ResolvedForestTagForwardDecompositionSupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) (Region : ResolvedRegionChoiceRoundTripSupply D S) where
  /-- The forward image's reconstructed forest tag on a forest-region component. -/
  forestTag_fwd : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ q.1.1.elements}),
    γ.1 ∈ (Region.Union.forestRecovered (fwdMap S q)).elements →
    (D.supply (γ.1.toResolvedFeynmanGraph)).ForestIdx
  /-- The choice-value identity: the reconstructed forest tag is `q`'s own choice value at `γ` (its content is the
  forward round-trip parent recovery). -/
  forest_choiceAt_eq : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ q.1.1.elements})
    (hmem : γ.1 ∈ (Region.Union.forestRecovered (fwdMap S q)).elements),
    q.2 γ (Finset.mem_attach _ _) = Sum.inr (forestTag_fwd q γ hmem)

namespace ResolvedForestTagForwardDecompositionSupply

variable {S : ResolvedConcreteSummandBundleSupply D} {Region : ResolvedRegionChoiceRoundTripSupply D S}

/-- **R-6c-body-198 — body-196's `forestTag_forward_eq` from the choice-value identity** (by `Sum.inr.inj`). -/
theorem forestTag_forward_eq (F : ResolvedForestTagForwardDecompositionSupply D S Region)
    {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ q.1.1.elements})
    (hmem : γ.1 ∈ (Region.Union.forestRecovered (fwdMap S q)).elements)
    (B : (D.supply (γ.1.toResolvedFeynmanGraph)).ForestIdx)
    (hqB : q.2 γ (Finset.mem_attach _ _) = Sum.inr B) :
    F.forestTag_fwd q γ hmem = B :=
  Sum.inr.inj ((F.forest_choiceAt_eq q γ hmem).symm.trans hqB)

/-- **R-6c-body-198 — body-196's forest value-equality supply from the decomposition** (given the body-188 tag
pinning). -/
def toForestValueEqDecompositionSupply (F : ResolvedForestTagForwardDecompositionSupply D S Region)
    (recoverChoice_forest_pin : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G)
      (γ : {x : ResolvedFeynmanSubgraph G // x ∈ q.1.1.elements})
      (hu : γ.1 ∈ (Region.Union.unionOuter (fwdMap S q)).1.elements)
      (hmem : γ.1 ∈ (Region.Union.forestRecovered (fwdMap S q)).elements),
      Region.recoverChoice (fwdMap S q) ⟨γ.1, hu⟩ (Finset.mem_attach _ _)
        = Sum.inr (F.forestTag_fwd q γ hmem)) :
    ResolvedForestValueEqDecompositionSupply D S Region where
  forestTag_fwd := fun {G} q γ hmem => F.forestTag_fwd q γ hmem
  recoverChoice_forest_pin := fun {G} q γ hu hmem => recoverChoice_forest_pin q γ hu hmem
  forestTag_forward_eq := fun {G} q γ hmem B hqB => F.forestTag_forward_eq q γ hmem B hqB

end ResolvedForestTagForwardDecompositionSupply

end GaugeGeometry.QFT.Combinatorial
