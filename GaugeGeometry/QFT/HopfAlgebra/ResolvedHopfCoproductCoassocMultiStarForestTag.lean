import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocMultiStarDecontraction

/-!
# R-6c-body-333 — the forest-source selector + `forestTag` construction (PROVED, transport isolated)

Three-hundred-and-thirty-third genuine-body step — the image-witness selector and the concrete `forestTag`, with the
dependent transport confined to ONE helper.  `forestTag` is now a CONSTRUCTION (not an arbitrary field): pick the unique
quotient component `δ` whose parent is the recovered forest component `γ` (D4 injectivity), and transport its `innerIdx`.

## Banked here

* `forestSource M F z γ` — the quotient component `δ ∈ forestDomain z` with `parent M z δ = γ.1`
  (`Classical.choose` of `Finset.mem_image` on `forestRecoveredMulti_elements`).
* `forestSource_spec` — `parent M z (forestSource … γ) = γ.1`.
* `forestSource_parent` — `forestSource … ⟨parent M z δ, hmem⟩ = δ` (uniqueness from D4 `localizedParent_ne`).
* `transportForestIdx` / `transportForestIdx_heq` — the ONE dependent transport (`h ▸ B`; `HEq (transport h B) B` by
  `cases h; rfl`).  All the dependent-type juggling lives here.
* `forestTag M F z γ := transportForestIdx (congrArg toResolvedFeynmanGraph (forestSource_spec …)) (innerIdx …)` —
  the constructed forest tag.
* `forestTag_heq_source` / `forestTag_of_parent` — `HEq (forestTag … γ) (innerIdx … (forestSource … γ))` and (composing
  with `forestSource_parent`) `HEq (forestTag … ⟨parent δ, hmem⟩) (innerIdx … δ)` — the specs that will align with the
  forward-image occurrence `B` (body-334).

Per the HALT: only the selector + `forestTag` + the HEq specs are proved; the `eq_of_heq` (homogeneous) version awaits
type-alignment at the forward image (body-334); the witness uniqueness uses D4 (NOT `Classical.choose` internals);
membership-proof differences ride on proof-irrelevance; no `occurrence`/`V.Remnant`/forward round-trip; `recovered_raw_mem`
untouched; no facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

variable {D : ResolvedCoproductProperForestData}

set_option linter.unusedSectionVars false

/-- **R-6c-body-333 — the ONE dependent transport of a `ForestIdx` along a graph equality.** -/
def transportForestIdx {H₁ H₂ : ResolvedFeynmanGraph} (h : H₁ = H₂)
    (B : (D.supply H₁).ForestIdx) : (D.supply H₂).ForestIdx := h ▸ B

/-- **R-6c-body-333 — the transport is heterogeneously the identity.** -/
theorem transportForestIdx_heq {H₁ H₂ : ResolvedFeynmanGraph} (h : H₁ = H₂)
    (B : (D.supply H₁).ForestIdx) : HEq (transportForestIdx h B) B := by
  cases h; rfl

namespace ResolvedMultiStarDecontractionSupply

variable (M : ResolvedMultiStarDecontractionSupply D) (F : ResolvedCanonicalStarFacts D)
  {G : ResolvedFeynmanGraph}

/-- **R-6c-body-333 — the recovered component is in the parent image.** -/
theorem forestSource_mem (z : ForestBlockCodType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ (M.forestRecoveredMulti F z).elements}) :
    γ.1 ∈ (forestDomain z).attach.image (fun δ => M.parent z δ) := by
  rw [← M.forestRecoveredMulti_elements F z]; exact γ.2

/-- **R-6c-body-333 — the forest-source selector.**  The quotient component whose parent is `γ`. -/
noncomputable def forestSource (z : ForestBlockCodType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ (M.forestRecoveredMulti F z).elements}) :
    {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) // x ∈ forestDomain z} :=
  (Finset.mem_image.mp (M.forestSource_mem F z γ)).choose

/-- **R-6c-body-333 — the source's parent is `γ`.** -/
theorem forestSource_spec (z : ForestBlockCodType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ (M.forestRecoveredMulti F z).elements}) :
    M.parent z (M.forestSource F z γ) = γ.1 :=
  (Finset.mem_image.mp (M.forestSource_mem F z γ)).choose_spec.2

/-- **R-6c-body-333 — the source of a parent is that quotient component** (D4 uniqueness). -/
theorem forestSource_parent (Measure : ResolvedMeasureLeafSupply D) (z : ForestBlockCodType D G)
    (δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) // x ∈ forestDomain z})
    (hmem : M.parent z δ ∈ (M.forestRecoveredMulti F z).elements) :
    M.forestSource F z ⟨M.parent z δ, hmem⟩ = δ := by
  apply Subtype.ext
  by_contra hne
  have hpeq : M.parent z (M.forestSource F z ⟨M.parent z δ, hmem⟩) = M.parent z δ :=
    M.forestSource_spec F z ⟨M.parent z δ, hmem⟩
  have hdisj : Disjoint (M.forestSource F z ⟨M.parent z δ, hmem⟩).1.vertices δ.1.vertices :=
    z.2.1.pairwiseDisjoint (Finset.mem_filter.mp (M.forestSource F z ⟨M.parent z δ, hmem⟩).2).1
      (Finset.mem_filter.mp δ.2).1 hne
  exact localizedParent_ne F Measure z (M.forestSource F z ⟨M.parent z δ, hmem⟩).1 δ.1
    (M.legLift z (M.forestSource F z ⟨M.parent z δ, hmem⟩)) (M.legLift z δ) (M.hE G) (M.hL G)
    (Finset.mem_filter.mp (M.forestSource F z ⟨M.parent z δ, hmem⟩).2).2 hdisj hpeq

/-- **R-6c-body-333 — the constructed forest tag.**  Transport the source's `innerIdx` along `parent (source) = γ`. -/
noncomputable def forestTag (z : ForestBlockCodType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ (M.forestRecoveredMulti F z).elements}) :
    (D.supply (γ.1.toResolvedFeynmanGraph)).ForestIdx :=
  transportForestIdx
    (congrArg ResolvedFeynmanSubgraph.toResolvedFeynmanGraph (M.forestSource_spec F z γ))
    (M.innerIdx z (M.forestSource F z γ))

/-- **R-6c-body-333 — `forestTag` is heterogeneously the source's `innerIdx`.** -/
theorem forestTag_heq_source (z : ForestBlockCodType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ (M.forestRecoveredMulti F z).elements}) :
    HEq (M.forestTag F z γ) (M.innerIdx z (M.forestSource F z γ)) :=
  transportForestIdx_heq _ _

/-- **R-6c-body-333 — `forestTag` at a parent is that component's `innerIdx`** (composing with D4 uniqueness). -/
theorem forestTag_of_parent (Measure : ResolvedMeasureLeafSupply D) (z : ForestBlockCodType D G)
    (δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) // x ∈ forestDomain z})
    (hmem : M.parent z δ ∈ (M.forestRecoveredMulti F z).elements) :
    HEq (M.forestTag F z ⟨M.parent z δ, hmem⟩) (M.innerIdx z δ) := by
  have h1 := M.forestTag_heq_source F z ⟨M.parent z δ, hmem⟩
  rw [M.forestSource_parent F Measure z δ hmem] at h1
  exact h1

end ResolvedMultiStarDecontractionSupply

end GaugeGeometry.QFT.Combinatorial
