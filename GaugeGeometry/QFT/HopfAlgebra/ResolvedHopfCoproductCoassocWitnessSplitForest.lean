import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocWitnessSplitConcrete

/-!
# R-6c-body-143 — witnessSplit forest branch: the de-contraction backward reconstruction

Hundred-and-forty-third genuine-body step, the heart of the boss.  The forest branch of body-141's `witnessSplit`
— the case `resolvedIsForestImage A B` (the quotient forest `B` has a component touching `A`'s star) — is the
genuine de-contraction reconstruction: the star-touching components of `B` are remnants of contracted forest
choices, and the recovered split choice `p` carries at least one `inr Bᵧ`.

## The forest reconstruction (shape fielded; tag PROVED)

`ResolvedForestPreimageData D S` fields the recovered outer forest `forestOuter z h` (a carrier forest: the
left-primitive pieces of `A`, the right-primitive pieces from `B`'s star-avoiding survivors via `componentToRight`,
and the forest-choice parents reassembled from `B`'s star-touching remnants via `componentToForest` /
`ForestPrimitiveIndex.toOccurrence`) and its choice `forestChoice z h` (`inr Bᵧ` on the reassembled parents,
`inl false` / `inl true` on the primitives), together with:

* `forest_has_inr` — an explicit component tagged `inr` (the witness that at least one forest choice is present,
  from the star-touching component `h` produces);
* `forest_forward` — the forward of the reconstruction is `z` (the remnant sector round-trip + survivor + left
  residual);
* `forest_backward` — the reconstruction of a forest forward image is the original split choice.

From `forest_has_inr`, `forest_isForestCarrying` is **proved**: `isForestCarryingChoice (forestOuter z h)
(forestChoice z h)` — the definition IS "some component is `inr`" — the forest `p`-tag fact that body-133's
`forest_inv_tag` needs (together with the `forestChoiceCarrier` membership).

## What is streamed into body-141

`.forestPreimage` / `.forest_forward` / `.forest_backward` are exactly body-141's `ResolvedWitnessSplitConcreteData`
forest fields.  Paired with body-142's mixed branch, they complete `ResolvedWitnessSplitConcreteData`, and hence
`witnessSplit`, `forward_witness` / `backward_witness`, and the four provider inverse laws (body-139).  So both
branches of the backward map are now in place; the forest branch is reduced to the de-contraction reconstruction
facts: the `componentToForest` remnant sector round-trip (`forest_forward` / `forest_backward`) and the
at-least-one-`inr` witness (`forest_has_inr`, PROVED to give the `p`-tag).

Per the HALT: no mixed case is touched; the outer reassembly is fielded (`forestOuter` / `forestChoice`), and the
forward/backward specs are reduced to the remnant sector round-trip + survivor + left residual;
`forest_isForestCarrying` is proved from the `inr` witness.

Landed:

* `ResolvedForestPreimageData D S` — the forest outer / choice + the three specs;
* `.forestPreimage` — the forest-branch split choice `⟨forestOuter, forestChoice⟩`;
* `.forest_isForestCarrying` — the forest `p`-tag (PROVED from `forest_has_inr`);
* `.forward` / `.backward` — body-141's forest forward / backward fields.

Toolkit body (like body-142, the mirror).  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-143 — the forest-branch preimage data.**  The de-contraction backward reconstruction for the
forest case (`B` touches the star): the recovered outer forest, its choice with at least one `inr`, and the forward
/ backward specs. -/
structure ResolvedForestPreimageData (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) where
  /-- The recovered outer forest `A'` (left residual ⊔ survivors ⊔ reassembled forest-choice parents). -/
  forestOuter : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    resolvedIsForestImage z.1 z.2 → {A' : ResolvedAdmissibleSubgraph G // A' ∈ D.carrier G}
  /-- The recovered choice `p` (`inr Bᵧ` on the reassembled parents, `inl _` on the primitives). -/
  forestChoice : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (h : resolvedIsForestImage z.1 z.2),
    ∀ γ ∈ (forestOuter z h).1.elements.attach,
      Bool ⊕ (D.supply (γ.1.toResolvedFeynmanGraph)).ForestIdx
  /-- At least one component tag is `inr` (a forest choice is present). -/
  forest_has_inr : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (h : resolvedIsForestImage z.1 z.2),
    ∃ γ, ∃ (hγ : γ ∈ (forestOuter z h).1.elements.attach), ∃ B, forestChoice z h γ hγ = Sum.inr B
  /-- The forward of the forest reconstruction is `z`. -/
  forest_forward : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (h : resolvedIsForestImage z.1 z.2),
    fwdMap S (⟨forestOuter z h, forestChoice z h⟩ : ResolvedCoassocSplitChoice D G) = z
  /-- The forest reconstruction of a forest forward image is the original split choice. -/
  forest_backward : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G)
    (h : resolvedIsForestImage (fwdMap S q).1 (fwdMap S q).2),
    (⟨forestOuter (fwdMap S q) h, forestChoice (fwdMap S q) h⟩ : ResolvedCoassocSplitChoice D G) = q

namespace ResolvedForestPreimageData

variable {S : ResolvedConcreteSummandBundleSupply D}

/-- **R-6c-body-143 — the forest-branch split choice.** -/
def forestPreimage (F : ResolvedForestPreimageData D S) {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType D G) (h : resolvedIsForestImage z.1 z.2) :
    ResolvedCoassocSplitChoice D G :=
  ⟨F.forestOuter z h, F.forestChoice z h⟩

/-- **R-6c-body-143 — the forest `p`-tag** (PROVED): the reconstructed choice is forest-carrying. -/
theorem forest_isForestCarrying (F : ResolvedForestPreimageData D S) {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType D G) (h : resolvedIsForestImage z.1 z.2) :
    isForestCarryingChoice (F.forestPreimage z h).1 (F.forestPreimage z h).2 :=
  F.forest_has_inr z h

/-- **R-6c-body-143 — body-141's forest forward field.** -/
theorem forward (F : ResolvedForestPreimageData D S) {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType D G) (h : resolvedIsForestImage z.1 z.2) :
    fwdMap S (F.forestPreimage z h) = z :=
  F.forest_forward z h

/-- **R-6c-body-143 — body-141's forest backward field.** -/
theorem backward (F : ResolvedForestPreimageData D S) {G : ResolvedFeynmanGraph}
    (q : ForestBlockDomType D G)
    (h : resolvedIsForestImage (fwdMap S q).1 (fwdMap S q).2) :
    F.forestPreimage (fwdMap S q) h = q :=
  F.forest_backward q h

end ResolvedForestPreimageData

end GaugeGeometry.QFT.Combinatorial
