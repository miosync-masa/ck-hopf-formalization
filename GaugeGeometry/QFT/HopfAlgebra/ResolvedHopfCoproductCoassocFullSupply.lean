import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocImageSideTerm
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocFiniteCover

/-!
# R-6c-support-9 — finite-cover supply + full compatibility adapter → `coassoc_gen`

The last wiring sprint: with the heart `term_eq` already a first-class field (support-8), this closes
the **entire** remaining chain from the de-contraction supplies to `coassoc_gen`, keeping every genuine
mathematical obligation as a named field.

  `ResolvedCoassocImageSideTermSupply` (term_eq field)
    `+ finite carriers/cover/inj` → `ResolvedCoassocSplitPhiFiniteData`           [`toFiniteData`]
    `+ representative + 2 regroup agreements` → `ResolvedCoassocGlobalCoverData x` [part 2c `toGlobalCoverData`]
    `∀ x family` → `ResolvedCoproductH58Compatibility`                             [4e `ofGlobalCoverData`]
    → `coassoc_gen`.

After this file, `Δᵣ`-coassociativity on every generator (`coassoc_gen`) is produced from ONE bundled
`ResolvedCoassocFullCompatibilitySupply`, whose unfilled fields are *exactly* the genuine holes:
`term_eq` (the heart), the finite carriers + `cover_on` + `inj_on`, the two regroup agreements
(`image_agreement` / `branch_agreement`), per representative, and the `∀ x` representative lift — plus
the deferred de-contraction bodies (`promotedOf` / `quotientForestOf` / `leftSelected` /
`imageWeightOf` / `discriminatorOf`).  Nothing else stands between the supply and `coassoc_gen`.

Landed:

* `ResolvedCoassocImageSideTermSupply.toFiniteData` — adds the finite carriers/cover/inj (as explicit
  inputs) to the term supply's `toSplitPhiData`, yielding `ResolvedCoassocSplitPhiFiniteData`;
* `ResolvedCoassocGlobalCoverSupply D x` — a representative `ResolvedCoassocSplitPhiFiniteData` plus the
  two regroup agreements, with `.toGlobalCoverData : ResolvedCoassocGlobalCoverData D x`;
* `ResolvedCoassocFullCompatibilitySupply D` — the `∀ x` family, with `.toCompatibility :
  ResolvedCoproductH58Compatibility D` and `.coassoc_gen` (the capstone).

No facade, no flat splitPhi theorem, no `forgetHopf`, no proof of any hole; pure adapter wiring.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-support-9 — the finite splitPhi data from the term supply.**  Adds the finite carriers,
cover, and branch injectivities (as explicit inputs, all referencing the term supply's constructed
`toSplitPhiData`) to recover a `ResolvedCoassocSplitPhiFiniteData D G`.  So the de-contraction supplies
(selected-outer + quotient-forest + weight + discriminator + `term_eq`) plus the carrier finiteness
witnesses assemble the part-2c finite cover. -/
noncomputable def ResolvedCoassocImageSideTermSupply.toFiniteData
    (S : ResolvedCoassocImageSideTermSupply D G)
    (forestCarrier :
      Finset {s : ResolvedCoassocSplitChoice D G // S.toSplitPhiData.discriminator (S.toSplitPhiData.imageOf s)})
    (mixedCarrier :
      Finset {s : ResolvedCoassocSplitChoice D G // ¬ S.toSplitPhiData.discriminator (S.toSplitPhiData.imageOf s)})
    (imageCarrier : Finset (ResolvedCoassocQuotientImage D G))
    (forestImage_mem : ∀ q ∈ forestCarrier, S.toSplitPhiData.imageOf q.1 ∈ imageCarrier)
    (mixedImage_mem : ∀ q ∈ mixedCarrier, S.toSplitPhiData.imageOf q.1 ∈ imageCarrier)
    (cover_on : ∀ z ∈ imageCarrier,
      (∃ q ∈ forestCarrier, S.toSplitPhiData.imageOf q.1 = z) ∨
        (∃ q ∈ mixedCarrier, S.toSplitPhiData.imageOf q.1 = z))
    (forest_inj_on : ∀ q₁ ∈ forestCarrier, ∀ q₂ ∈ forestCarrier,
      S.toSplitPhiData.imageOf q₁.1 = S.toSplitPhiData.imageOf q₂.1 → q₁ = q₂)
    (mixed_inj_on : ∀ q₁ ∈ mixedCarrier, ∀ q₂ ∈ mixedCarrier,
      S.toSplitPhiData.imageOf q₁.1 = S.toSplitPhiData.imageOf q₂.1 → q₁ = q₂) :
    ResolvedCoassocSplitPhiFiniteData D G where
  toResolvedCoassocSplitPhiData := S.toSplitPhiData
  forestCarrier := forestCarrier
  mixedCarrier := mixedCarrier
  imageCarrier := imageCarrier
  forestImage_mem := forestImage_mem
  mixedImage_mem := mixedImage_mem
  cover_on := cover_on
  forest_inj_on := forest_inj_on
  mixed_inj_on := mixed_inj_on

/-- **R-6c-support-9 — the per-generator global cover supply.**  A representative finite splitPhi cover
together with the two regroup agreements connecting the cover sums to `regroupImageSum` /
`regroupBranchSum` at the generator `x`.  The representative graph and the agreements are fields; the
connection between `x` and the representative is carried entirely by the agreements. -/
structure ResolvedCoassocGlobalCoverSupply (D : ResolvedCoproductProperForestData)
    (x : ResolvedHopfGen) where
  /-- A representative resolved Feynman graph for the generator `x`. -/
  repGraph : ResolvedFeynmanGraph
  /-- The finite splitPhi cover over the representative. -/
  finite : ResolvedCoassocSplitPhiFiniteData D repGraph
  /-- The image side equals the cover's image-weight sum. -/
  image_agreement : D.regroupImageSum x = ∑ z ∈ finite.imageCarrier, finite.imageWeight z
  /-- The cover's (forest + mixed) split-term sum equals the branch side. -/
  branch_agreement :
    (∑ q ∈ finite.forestCarrier, D.resolvedSplitChoiceTerm q.1)
      + (∑ q ∈ finite.mixedCarrier, D.resolvedSplitChoiceTerm q.1)
      = D.regroupBranchSum x

/-- The global cover bundle from the per-generator supply (via the part-2c `toGlobalCoverData`). -/
noncomputable def ResolvedCoassocGlobalCoverSupply.toGlobalCoverData
    {x : ResolvedHopfGen} (S : ResolvedCoassocGlobalCoverSupply D x) :
    ResolvedCoassocGlobalCoverData D x :=
  S.finite.toGlobalCoverData x S.image_agreement S.branch_agreement

/-- **R-6c-support-9 — the full compatibility supply.**  The `∀ x` family of per-generator global cover
supplies — everything needed to produce the H5.8 compatibility and hence resolved coassociativity. -/
structure ResolvedCoassocFullCompatibilitySupply (D : ResolvedCoproductProperForestData) where
  /-- A per-generator global cover supply. -/
  cover : ∀ x : ResolvedHopfGen, ResolvedCoassocGlobalCoverSupply D x

/-- The H5.8 compatibility from the full supply (via the 4e `ofGlobalCoverData`). -/
noncomputable def ResolvedCoassocFullCompatibilitySupply.toCompatibility
    (S : ResolvedCoassocFullCompatibilitySupply D) : ResolvedCoproductH58Compatibility D :=
  ResolvedCoproductH58Compatibility.ofGlobalCoverData (fun x => (S.cover x).toGlobalCoverData)

/-- **R-6c-support-9 — the capstone.**  `Δᵣ`-coassociativity on every generator, from the full
compatibility supply.  This closes the entire wiring: a single bundled supply (whose unfilled fields
are exactly the genuine holes — `term_eq`, finite cover/inj, the two regroup agreements, the
representative lift, and the deferred de-contraction bodies) yields `coassoc_gen`. -/
theorem ResolvedCoassocFullCompatibilitySupply.coassoc_gen
    (S : ResolvedCoassocFullCompatibilitySupply D) (x : ResolvedHopfGen) :
    D.coassocLeft (MvPolynomial.X x) = D.coassocRight (MvPolynomial.X x) :=
  S.toCompatibility.coassoc_gen x

end GaugeGeometry.QFT.Combinatorial
