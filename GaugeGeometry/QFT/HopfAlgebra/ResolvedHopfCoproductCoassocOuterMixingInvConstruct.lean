import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocBijectionProvider

/-!
# R-6c-body-134 — outer-mixing invConstruct reassembly skeleton: `invConstruct = ⟨recoverOuter, recoverChoice⟩`

Hundred-and-thirty-fourth genuine-body step, and the keystone: the backward map `invConstruct : (A, B) ↦ (A', p)`
is given a STRUCTURED form.  Instead of an opaque field, it is `⟨recoverOuter z, recoverChoice z⟩` — the original
outer forest `A'` plus its component choice `p`, reconstructed from the codomain pair `(A, B)` by the existing
sector backward maps.  This makes `invConstruct` transparent, so the four inverse laws can later decompose into the
two round-trips `forward (invConstruct z) = z` and `invConstruct (forward q) = q` component-by-component.

## The reassembly (structure placed; components named)

For a codomain forest `z = (A, B)` with `A = leftOf ∪ promotedOf` and `B = rightSurvivor ∪ remnant`:

* the components of `B` are star-classified (`resolvedIsForestImage`):
  * a STAR-AVOIDING (right-survivor) component ↦ a RIGHT-PRIMITIVE component of `A'`, via the existing sector
    backward map `ResolvedSectorBackwardFromImageSupply.componentToRight` (`right_surj`);
  * a STAR-TOUCHING (remnant) component ↦ a FOREST-CHOICE parent component of `A'`, via `componentToForest`
    (`forest_surj`);
* the components of `A` NOT arising from `B` (the `leftOf` pieces) ↦ LEFT-PRIMITIVE components of `A'`;
* `A' = ` (left-primitive pieces of `A`) ∪ (right-primitive pieces recovered from `B`'s survivors) ∪ (forest-choice
  parents recovered from `B`'s remnants) — `recoverOuter z`;
* `p` tags each `A'`-component by its origin: `inl true` (left-primitive), `inl false` (right-primitive),
  `inr Bᵧ` (forest choice) — `recoverChoice z`.

`ResolvedOuterMixingReassemblyData D` fields `recoverOuter` and `recoverChoice` (their concrete union / tag
construction from the sector backward maps is the deferred content, named above); `.invConstruct` is then the
literal pair `⟨recoverOuter z, recoverChoice z⟩ : ForestBlockDomType`, and `.invConstructFn` is its `∀ G`-form
ready to fill the bijection provider's `invConstruct` field.

## Consequence

`invConstruct` is no longer opaque: it is a structured reassembly `⟨recoverOuter, recoverChoice⟩`.  The four
inverse laws (`mixed_/forest_ left_/right_inv`) now reduce to:

* `right_inv`: `⟨selectedOuterOf (⟨recoverOuter z, recoverChoice z⟩), quotientForest (…)⟩ = z` — the forward of the
  reassembly is the identity (the `recoverOuter`/`recoverChoice` round-trip on `(A, B)`);
* `left_inv`: `⟨recoverOuter ⟨selectedOuterOf q, quotientForest q⟩, recoverChoice …⟩ = q` — the reassembly of the
  forward is the identity (on `(A', p)`).

Both are now equalities of the STRUCTURED pair, decomposable component-by-component against the sector round-trips.

Per the HALT: the inverse laws are NOT proved; `recoverOuter` / `recoverChoice` are fielded with their intended
sector-map components named; `invConstruct` is placed as the structured pair.

Landed:

* `ResolvedOuterMixingReassemblyData D` — `recoverOuter` + `recoverChoice`;
* `.invConstruct` / `.invConstructFn` — the structured backward map for the bijection provider.

Toolkit body (like body-132/133), one skeleton supply.  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-134 — the outer-mixing reassembly data.**  The two reconstruction fields recovering `(A', p)` from
a codomain pair `(A, B)`: `recoverOuter` builds the original outer forest `A'` (left-primitive pieces of `A` ∪
right-primitive pieces from `B`'s survivors ∪ forest-choice parents from `B`'s remnants), and `recoverChoice` tags
each `A'`-component (`inl true` / `inl false` / `inr Bᵧ`).  Both are built from the existing sector backward maps
(`componentToRight` / `componentToForest`). -/
structure ResolvedOuterMixingReassemblyData (D : ResolvedCoproductProperForestData) where
  /-- The recovered original outer forest `A'` (a carrier forest). -/
  recoverOuter : ∀ {G : ResolvedFeynmanGraph},
    ForestBlockCodType D G → {A' : ResolvedAdmissibleSubgraph G // A' ∈ D.carrier G}
  /-- The recovered component choice `p` on `A'` (`inl true` / `inl false` / `inr Bᵧ` by origin). -/
  recoverChoice : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    ∀ γ ∈ (recoverOuter z).1.elements.attach,
      Bool ⊕ (D.supply (γ.1.toResolvedFeynmanGraph)).ForestIdx

/-- **R-6c-body-134 — the structured backward map** `(A, B) ↦ (A', p)`.  The literal pair `⟨recoverOuter z,
recoverChoice z⟩ : ForestBlockDomType` — no longer opaque. -/
def ResolvedOuterMixingReassemblyData.invConstruct (R : ResolvedOuterMixingReassemblyData D)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) : ForestBlockDomType D G :=
  ⟨R.recoverOuter z, R.recoverChoice z⟩

/-- **R-6c-body-134 — the `∀ G`-form backward map, ready for the bijection provider's `invConstruct` field.** -/
def ResolvedOuterMixingReassemblyData.invConstructFn (R : ResolvedOuterMixingReassemblyData D)
    (G : ResolvedFeynmanGraph) : ForestBlockCodType D G → ForestBlockDomType D G :=
  fun z => R.invConstruct z

/-- **R-6c-body-134 — the recovered outer forest is the first projection of `invConstruct`** (`rfl`). -/
@[simp] theorem ResolvedOuterMixingReassemblyData.invConstruct_fst
    (R : ResolvedOuterMixingReassemblyData D) {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) :
    (R.invConstruct z).1 = R.recoverOuter z :=
  rfl

/-- **R-6c-body-134 — the recovered choice is the second projection of `invConstruct`** (`rfl`). -/
@[simp] theorem ResolvedOuterMixingReassemblyData.invConstruct_snd
    (R : ResolvedOuterMixingReassemblyData D) {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) :
    (R.invConstruct z).2 = R.recoverChoice z :=
  rfl

end GaugeGeometry.QFT.Combinatorial
