import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRegionValueClosure

/-!
# R-6c-body-282 — value-root `unionOuterValue` / `recoverChoiceValue` + the raw preimage root (PROVED)

Two-hundred-and-eighty-second genuine-body step — the S-free raw preimage root.  Body-281's S phantom is corrected
(its canonical root is now S-free; the legacy bundle is received on the `toParametricCarrierClosure` converter only).
This body builds the two value-root region layers over body-281's coherent `Assembly` maps and body-269's raw carrier
membership, and assembles the common `recoveredPreimageValue` — the reconstruction `⟨unionOuterValue z,
recoverChoiceValue z⟩`, S-free, mirroring body-145/152 with `Union.unionOuter` / `recoverChoice` re-keyed to the value
maps.  No round-trip, no forward reconstruction.

## `unionOuterValue` (body-145/153, value)

`ResolvedRegionValueClosureSupply.unionOuterValue z = ⟨recoveredRawUnion (Left.leftResidual z) (Region.rightRecovered z)
(Region.forestRecovered z) …, recovered_raw_mem z⟩` — the carrier-tagged raw recovered outer, its membership supplied
ONLY by body-281's raw closure (`recovered_raw_mem`), never re-derived.  (The `∪`-elements shape is deferred to the
membership body 283, where the `Classical.decEq` union instance is handled explicitly.)

## `recoverChoiceValue` + the three tags (body-152, value)

`ResolvedRegionTagValueSupply F V` carries body-281's closure, a `forestTag` map, and the three region exclusivities
(over the `Assembly` maps).  `recoverChoiceValue` is the same region-priority `dite`
(`leftResidual → inl true`, `rightRecovered → inl false`, `forestRecovered → inr (forestTag …)`); `left_tag` /
`right_tag` / `forest_tag` are PROVED by `if_pos` / `if_neg` (exclusivities) / `dif_pos`.

## The common raw preimage

`recoveredPreimageValue z := ⟨unionOuterValue z, recoverChoiceValue z⟩ : ForestBlockDomType D G` — the branch-agnostic
reconstruction shared by the mixed and forest preimages (body-142/143 split off it downstream).

Per the HALT: only the raw preimage root is built; NO round-trip (mixed/forest forward/backward), NO mixed/forest
classifier dependence, NO forward reconstruction (`forward_outer`/`forward_quotient` are body-284 leaves); the outer
carrier membership comes only from body-281's raw closure.  No `S` / `Forward` / legacy in any declaration type; the
old Union/Tag supplies are not used.  No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData}

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ResolvedRegionValueClosureSupply

variable {F : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}

/-- **R-6c-body-282 — the value-root outer union** (carrier-tagged raw recovered outer).  Membership supplied by
body-281's `recovered_raw_mem` only. -/
noncomputable def unionOuterValue (C : ResolvedRegionValueClosureSupply F V)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) :
    {A' : ResolvedAdmissibleSubgraph G // A' ∈ D.carrier G} :=
  ⟨recoveredRawUnion (C.Assembly.Left.leftResidual z) (C.Assembly.Region.rightRecovered z)
      (C.Assembly.Region.forestRecovered z)
      (C.left_right_disjoint z) (C.left_forest_disjoint z) (C.right_forest_disjoint z),
    C.recovered_raw_mem z⟩

end ResolvedRegionValueClosureSupply

/-- **R-6c-body-282 — the value-root region tag-definition supply.**  Body-281's coherent closure plus the forest-index
map and the three region exclusivities (over the `Assembly` maps) — the data defining `recoverChoiceValue`. -/
structure ResolvedRegionTagValueSupply (F : ResolvedSelectedOuterFilteredMemSupply D)
    (V : ResolvedConcreteSummandValueSupply D) where
  /-- The coherent region closure (body-281): shared `Assembly` maps + raw carrier membership. -/
  Closure : ResolvedRegionValueClosureSupply F V
  /-- The quotient sub-forest `Bᵧ` of each forest-recovered component. -/
  forestTag : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ (Closure.unionOuterValue z).1.elements}),
    γ.1 ∈ (Closure.Assembly.Region.forestRecovered z).elements →
      (D.supply (γ.1.toResolvedFeynmanGraph)).ForestIdx
  /-- A right-recovered component is not left-residual. -/
  right_notMem_left : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ (Closure.unionOuterValue z).1.elements}),
    γ.1 ∈ (Closure.Assembly.Region.rightRecovered z).elements →
      γ.1 ∉ (Closure.Assembly.Left.leftResidual z).elements
  /-- A forest-recovered component is not left-residual. -/
  forest_notMem_left : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ (Closure.unionOuterValue z).1.elements}),
    γ.1 ∈ (Closure.Assembly.Region.forestRecovered z).elements →
      γ.1 ∉ (Closure.Assembly.Left.leftResidual z).elements
  /-- A forest-recovered component is not right-recovered. -/
  forest_notMem_right : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ (Closure.unionOuterValue z).1.elements}),
    γ.1 ∈ (Closure.Assembly.Region.forestRecovered z).elements →
      γ.1 ∉ (Closure.Assembly.Region.rightRecovered z).elements

namespace ResolvedRegionTagValueSupply

variable {F : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}

/-- **R-6c-body-282 — the value-root region-priority tag function.** -/
noncomputable def recoverChoiceValue (T : ResolvedRegionTagValueSupply F V)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ (T.Closure.unionOuterValue z).1.elements})
    (hγ : γ ∈ (T.Closure.unionOuterValue z).1.elements.attach) :
    Bool ⊕ (D.supply (γ.1.toResolvedFeynmanGraph)).ForestIdx :=
  if γ.1 ∈ (T.Closure.Assembly.Left.leftResidual z).elements then Sum.inl true
  else if γ.1 ∈ (T.Closure.Assembly.Region.rightRecovered z).elements then Sum.inl false
  else if h : γ.1 ∈ (T.Closure.Assembly.Region.forestRecovered z).elements then
    Sum.inr (T.forestTag z γ h)
  else Sum.inl true

/-- **R-6c-body-282 — the left tag** (`inl true`). -/
theorem left_tag (T : ResolvedRegionTagValueSupply F V) {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ (T.Closure.unionOuterValue z).1.elements})
    (hm : γ.1 ∈ (T.Closure.Assembly.Left.leftResidual z).elements) :
    T.recoverChoiceValue z γ (Finset.mem_attach _ _) = Sum.inl true := by
  rw [recoverChoiceValue, if_pos hm]

/-- **R-6c-body-282 — the right tag** (`inl false`). -/
theorem right_tag (T : ResolvedRegionTagValueSupply F V) {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ (T.Closure.unionOuterValue z).1.elements})
    (hm : γ.1 ∈ (T.Closure.Assembly.Region.rightRecovered z).elements) :
    T.recoverChoiceValue z γ (Finset.mem_attach _ _) = Sum.inl false := by
  rw [recoverChoiceValue, if_neg (T.right_notMem_left z γ hm), if_pos hm]

/-- **R-6c-body-282 — the forest tag** (`inr Bᵧ`). -/
theorem forest_tag (T : ResolvedRegionTagValueSupply F V) {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ (T.Closure.unionOuterValue z).1.elements})
    (hm : γ.1 ∈ (T.Closure.Assembly.Region.forestRecovered z).elements) :
    ∃ B, T.recoverChoiceValue z γ (Finset.mem_attach _ _) = Sum.inr B := by
  rw [recoverChoiceValue, if_neg (T.forest_notMem_left z γ hm),
    if_neg (T.forest_notMem_right z γ hm), dif_pos hm]
  exact ⟨_, rfl⟩

/-- **R-6c-body-282 — the common raw preimage** (branch-agnostic reconstruction `⟨unionOuterValue, recoverChoiceValue⟩`).
The mixed / forest preimages split off this downstream (body-142/143). -/
noncomputable def recoveredPreimageValue (T : ResolvedRegionTagValueSupply F V)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) : ForestBlockDomType D G :=
  ⟨T.Closure.unionOuterValue z, fun γ hγ => T.recoverChoiceValue z γ hγ⟩

end ResolvedRegionTagValueSupply

end GaugeGeometry.QFT.Combinatorial
