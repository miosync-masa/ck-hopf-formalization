import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocMultiStarRegionTagValue

/-!
# R-6c-body-366 — Front-3 bank-1: the multi-star definitional wiring, as named theorems (PROVED)

Three-hundred-and-sixty-sixth genuine-body step — the first Front-3 socket.  The multi-star region-tag supply's
region / left / forest-tag maps are, by construction (body-341's `multiStarRegion` / `multiStarLeft` / the
`forestTag := M.forestTag` field), the multi-star geometry's own outputs.  This body fixes that wiring as named
`rfl` theorems so the `hForest` / `hFT` / `hRight` / `hLeft` gates never travel back to a caller argument:

* `multiStar_forestRecovered_wiring` — `(Region.forestRecovered z).elements = (forestRecoveredMulti z).elements`;
* `multiStar_rightRecovered_wiring` — `(Region.rightRecovered z).elements = (rightDomain z).attach.image (rightReembed z)`;
* `multiStar_leftResidual_wiring` — `(Left.leftResidual z).elements = leftResidualTouched z`;
* `multiStar_forestTag_wiring` — `M.forestTag Fstar z ⟨γ, h⟩ = M.forestTag Fstar z ⟨γ, h'⟩` (proof-irrelevant
  membership swap — the exact-`B` value only depends on `γ`).

Each is `rfl` (the region/left constructions are `ofElements` / `filterElements` of exactly the multi-star image /
filter, and `forestTag := M.forestTag`).  Stated over the sub-constructions `multiStarRegion M Fstar` / `multiStarLeft`,
which are DEFINITIONALLY the tag supply's `Closure.Assembly.Region` / `.Left`, so they discharge the corresponding `T`
gates by `exact` up to `rfl`.

Per the HALT: only the definitional wiring is banked; the six sound/complete bridges, `hround`, `hSurvivor`, and every
carrier-membership leaf are UNTOUCHED (bank-2+); no `simp` blow-up (the body-337/341 public `_elements` shapes are
used); no new model field; axiom baseline preserved.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO
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

variable {D : ResolvedCoproductProperForestData}

set_option linter.unusedSectionVars false

namespace ResolvedMultiStarDecontractionSupply

variable (M : ResolvedMultiStarDecontractionSupply D) (Fstar : ResolvedCanonicalStarFacts D)
  {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)

/-- **R-6c-body-366 — forest-recovered wiring** (`hForest`, `rfl`). -/
theorem multiStar_forestRecovered_wiring :
    ((multiStarRegion M Fstar).forestRecovered z).elements = (M.forestRecoveredMulti Fstar z).elements :=
  rfl

/-- **R-6c-body-366 — right-recovered wiring** (`hRight`, `rfl`). -/
theorem multiStar_rightRecovered_wiring :
    ((multiStarRegion M Fstar).rightRecovered z).elements
      = (rightDomain z).attach.image (rightReembed z) :=
  rfl

/-- **R-6c-body-366 — left-residual wiring** (`hLeft`, `rfl`). -/
theorem multiStar_leftResidual_wiring :
    (multiStarLeft.leftResidual z).elements = leftResidualTouched z :=
  rfl

/-- **R-6c-body-366 — forest-tag wiring** (`hFT`, proof-irrelevant membership swap). -/
theorem multiStar_forestTag_wiring (γ : ResolvedFeynmanSubgraph G)
    (h h' : γ ∈ (M.forestRecoveredMulti Fstar z).elements) :
    M.forestTag Fstar z ⟨γ, h⟩ = M.forestTag Fstar z ⟨γ, h'⟩ :=
  rfl

end ResolvedMultiStarDecontractionSupply

end GaugeGeometry.QFT.Combinatorial
