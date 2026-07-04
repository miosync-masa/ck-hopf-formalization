import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocWitnessSplitConcrete

/-!
# R-6c-body-142 — witnessSplit mixed branch: the primitive-only backward reconstruction

Hundred-and-forty-second genuine-body step, the lighter half of the backward map.  The mixed branch of body-141's
`witnessSplit` — the case `¬ resolvedIsForestImage A B` (the quotient forest `B` avoids `A`'s star) — is the
primitive-only reconstruction: `B` consists solely of right-survivor pieces, so the recovered split choice `p` has
**no `inr`** and the reassembly is a pure left/right-primitive relabelling.

## The mixed reconstruction (shape fielded; tag PROVED)

`ResolvedMixedPreimageData D S` fields the recovered outer forest `mixedOuter z h` (a carrier forest: the
left-primitive pieces of `A` glued with the right-primitive pieces recovered from `B`'s survivors via the sector
`componentToRight`) and its choice `mixedChoice z h` (`inl true` on the left residual, `inl false` on the
survivors), together with:

* `mixed_no_forest` — every component tag is `inl` (no `inr`);
* `mixed_forward` — the forward of the reconstruction is `z` (the survivor sector round-trip + left residual);
* `mixed_backward` — the reconstruction of a mixed forward image is the original split choice.

From `mixed_no_forest`, `mixed_not_forestCarrying` is **proved**: `¬ isForestCarryingChoice (mixedOuter z h)
(mixedChoice z h)` (an `inl`-tag cannot be `inr`) — the mixed `p`-tag fact that body-133's `mixed_inv_tag` needs
(together with the `forestChoiceCarrier` membership).

## What is streamed into body-141

`.mixedPreimage` / `.mixed_forward` / `.mixed_backward` are exactly body-141's
`ResolvedWitnessSplitConcreteData` mixed fields, so a later body pairs this with the forest branch to complete
`witnessSplit`.  The mixed half is thereby reduced to the primitive-only reconstruction facts: the right-survivor
sector round-trip (`mixed_forward` / `mixed_backward`) and the all-`inl` tag (`mixed_no_forest`, PROVED to give the
`p`-tag).

Per the HALT: no forest / remnant case; the outer union is fielded (`mixedOuter` / `mixedChoice`), and the
forward/backward specs are reduced to the survivor sector round-trip + left residual; `mixed_not_forestCarrying` is
proved from the all-`inl` tag.

Landed:

* `ResolvedMixedPreimageData D S` — the mixed outer / choice + the three specs;
* `.mixedPreimage` — the mixed-branch split choice `⟨mixedOuter, mixedChoice⟩`;
* `.mixed_not_forestCarrying` — the mixed `p`-tag (PROVED from `mixed_no_forest`);
* `.mixed_forward` / `.mixed_backward` — body-141's mixed forward / backward fields.

Toolkit body (like body-141).  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-142 — the mixed-branch preimage data.**  The primitive-only backward reconstruction for the mixed
case (`B` avoids the star): the recovered outer forest, its all-`inl` choice, and the forward / backward specs. -/
structure ResolvedMixedPreimageData (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) where
  /-- The recovered outer forest `A'` (left residual of `A` ⊔ right survivors of `B`). -/
  mixedOuter : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    ¬ resolvedIsForestImage z.1 z.2 → {A' : ResolvedAdmissibleSubgraph G // A' ∈ D.carrier G}
  /-- The recovered choice `p` (`inl true` on the left residual, `inl false` on the survivors). -/
  mixedChoice : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (h : ¬ resolvedIsForestImage z.1 z.2),
    ∀ γ ∈ (mixedOuter z h).1.elements.attach,
      Bool ⊕ (D.supply (γ.1.toResolvedFeynmanGraph)).ForestIdx
  /-- Every component tag is `inl` — no forest choice. -/
  mixed_no_forest : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (h : ¬ resolvedIsForestImage z.1 z.2),
    ∀ γ (hγ : γ ∈ (mixedOuter z h).1.elements.attach), ∃ b, mixedChoice z h γ hγ = Sum.inl b
  /-- The forward of the mixed reconstruction is `z`. -/
  mixed_forward : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (h : ¬ resolvedIsForestImage z.1 z.2),
    fwdMap S (⟨mixedOuter z h, mixedChoice z h⟩ : ResolvedCoassocSplitChoice D G) = z
  /-- The mixed reconstruction of a mixed forward image is the original split choice. -/
  mixed_backward : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G)
    (h : ¬ resolvedIsForestImage (fwdMap S q).1 (fwdMap S q).2),
    (⟨mixedOuter (fwdMap S q) h, mixedChoice (fwdMap S q) h⟩ : ResolvedCoassocSplitChoice D G) = q

namespace ResolvedMixedPreimageData

variable {S : ResolvedConcreteSummandBundleSupply D}

/-- **R-6c-body-142 — the mixed-branch split choice.** -/
def mixedPreimage (M : ResolvedMixedPreimageData D S) {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType D G) (h : ¬ resolvedIsForestImage z.1 z.2) :
    ResolvedCoassocSplitChoice D G :=
  ⟨M.mixedOuter z h, M.mixedChoice z h⟩

/-- **R-6c-body-142 — the mixed `p`-tag** (PROVED): the reconstructed choice is not forest-carrying. -/
theorem mixed_not_forestCarrying (M : ResolvedMixedPreimageData D S) {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType D G) (h : ¬ resolvedIsForestImage z.1 z.2) :
    ¬ isForestCarryingChoice (M.mixedPreimage z h).1 (M.mixedPreimage z h).2 := by
  rintro ⟨γ, hγ, b, hb⟩
  obtain ⟨b', hb'⟩ := M.mixed_no_forest z h γ hγ
  exact Sum.inl_ne_inr (hb'.symm.trans hb)

/-- **R-6c-body-142 — body-141's mixed forward field.** -/
theorem forward (M : ResolvedMixedPreimageData D S) {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType D G) (h : ¬ resolvedIsForestImage z.1 z.2) :
    fwdMap S (M.mixedPreimage z h) = z :=
  M.mixed_forward z h

/-- **R-6c-body-142 — body-141's mixed backward field.** -/
theorem backward (M : ResolvedMixedPreimageData D S) {G : ResolvedFeynmanGraph}
    (q : ForestBlockDomType D G)
    (h : ¬ resolvedIsForestImage (fwdMap S q).1 (fwdMap S q).2) :
    M.mixedPreimage (fwdMap S q) h = q :=
  M.mixed_backward q h

end ResolvedMixedPreimageData

end GaugeGeometry.QFT.Combinatorial
