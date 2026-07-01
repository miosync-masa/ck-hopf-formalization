import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocTermEqToFullSupply
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocFullSupply

/-!
# R-6c-heart-6a-12a — FULL coassoc leaf supply (the final boundary, one record)

The structural coassociativity chain is closed end-to-end (6a-11d): `term_eq` → `ResolvedCoassocImageSideTermSupply`
→ `toSplitPhiData` → (support-9) finite cover → `coassoc_gen`.  This file collects the LAST top-level record:
the grand image-side supply (the `term_eq` heart, 6a-11d) PLUS the support-9 finite-cover leaf fields
(`forestCarrier` / `mixedCarrier` / `imageCarrier` + `cover_on` + `inj_on`).  So every remaining obligation of
resolved coassociativity is a named leaf field of ONE record `ResolvedCoassocGrandFullSupply`.

Derived:

* `.toImageSideTermSupply` / `.toSplitPhiData` — inherited from the image-term half (6a-11d);
* `.toFiniteData : ResolvedCoassocSplitPhiFiniteData D G` — the support-9 finite splitPhi cover;
* `.toGlobalCoverSupply x (image_agreement) (branch_agreement) : ResolvedCoassocGlobalCoverSupply D x` —
  the per-generator building block of `ResolvedCoassocFullCompatibilitySupply` (repGraph := G);
* `.toGlobalCoverData x … : ResolvedCoassocGlobalCoverData D x`.

The `∀ x` lift into `ResolvedCoassocFullCompatibilitySupply D` needs a representative family (a per-generator
`repGraph`/agreements), so per the HALT it is NOT taken here — this per-`G` record is the stopping point.

Per the HALT: no finite cover/inj proofs, no regroup agreement proofs, no leaf discharge — only the wiring
of the grand image-side supply + finite fields into the existing support-9 machinery.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-6a-12a — the full coassoc leaf supply.**  The `term_eq` grand image-side supply (6a-11d)
plus the support-9 finite-cover leaf fields.  Every remaining obligation of resolved coassociativity is a
leaf field here (either inside `ImageTerm`'s grand records, or one of the finite/cover/inj fields). -/
structure ResolvedCoassocGrandFullSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph) where
  /-- The `term_eq` grand image-side supply (6a-11d): `Inner` + `selected`/`quotient`/`discriminatorOf` +
  `Product`/`Right` grand records. -/
  ImageTerm : ResolvedCoassocGrandImageSideSupply D G
  /-- The finite forest-classified split-choice carrier. -/
  forestCarrier :
    Finset {s : ResolvedCoassocSplitChoice D G //
      ImageTerm.toImageSideTermSupply.toSplitPhiData.discriminator
        (ImageTerm.toImageSideTermSupply.toSplitPhiData.imageOf s)}
  /-- The finite mixed-classified split-choice carrier. -/
  mixedCarrier :
    Finset {s : ResolvedCoassocSplitChoice D G //
      ¬ ImageTerm.toImageSideTermSupply.toSplitPhiData.discriminator
        (ImageTerm.toImageSideTermSupply.toSplitPhiData.imageOf s)}
  /-- The finite image carrier. -/
  imageCarrier : Finset (ResolvedCoassocQuotientImage D G)
  /-- Forest images land in the image carrier. -/
  forestImage_mem : ∀ q ∈ forestCarrier,
    ImageTerm.toImageSideTermSupply.toSplitPhiData.imageOf q.1 ∈ imageCarrier
  /-- Mixed images land in the image carrier. -/
  mixedImage_mem : ∀ q ∈ mixedCarrier,
    ImageTerm.toImageSideTermSupply.toSplitPhiData.imageOf q.1 ∈ imageCarrier
  /-- Cover: every image carrier element is a forest or mixed branch image. -/
  cover_on : ∀ z ∈ imageCarrier,
    (∃ q ∈ forestCarrier, ImageTerm.toImageSideTermSupply.toSplitPhiData.imageOf q.1 = z) ∨
      (∃ q ∈ mixedCarrier, ImageTerm.toImageSideTermSupply.toSplitPhiData.imageOf q.1 = z)
  /-- Forest-branch injectivity on the carrier. -/
  forest_inj_on : ∀ q₁ ∈ forestCarrier, ∀ q₂ ∈ forestCarrier,
    ImageTerm.toImageSideTermSupply.toSplitPhiData.imageOf q₁.1
      = ImageTerm.toImageSideTermSupply.toSplitPhiData.imageOf q₂.1 → q₁ = q₂
  /-- Mixed-branch injectivity on the carrier. -/
  mixed_inj_on : ∀ q₁ ∈ mixedCarrier, ∀ q₂ ∈ mixedCarrier,
    ImageTerm.toImageSideTermSupply.toSplitPhiData.imageOf q₁.1
      = ImageTerm.toImageSideTermSupply.toSplitPhiData.imageOf q₂.1 → q₁ = q₂

/-- **R-6c-heart-6a-12a — the support-8 image-side term supply (inherited from the image-term half). -/
noncomputable def ResolvedCoassocGrandFullSupply.toImageSideTermSupply
    (F : ResolvedCoassocGrandFullSupply D G) : ResolvedCoassocImageSideTermSupply D G :=
  F.ImageTerm.toImageSideTermSupply

/-- **R-6c-heart-6a-12a — the resolved `forestComponentSplitPhi` data (inherited). -/
noncomputable def ResolvedCoassocGrandFullSupply.toSplitPhiData
    (F : ResolvedCoassocGrandFullSupply D G) : ResolvedCoassocSplitPhiData D G :=
  F.ImageTerm.toSplitPhiData

/-- **R-6c-heart-6a-12a — the support-9 finite splitPhi cover from the full leaf record. -/
noncomputable def ResolvedCoassocGrandFullSupply.toFiniteData
    (F : ResolvedCoassocGrandFullSupply D G) : ResolvedCoassocSplitPhiFiniteData D G :=
  F.ImageTerm.toImageSideTermSupply.toFiniteData
    F.forestCarrier F.mixedCarrier F.imageCarrier
    F.forestImage_mem F.mixedImage_mem F.cover_on F.forest_inj_on F.mixed_inj_on

/-- **R-6c-heart-6a-12a — the per-generator global cover supply (repGraph := G).**  Adds the two regroup
agreements at a generator `x`; this is the direct building block of `ResolvedCoassocFullCompatibilitySupply`
(its `cover` field is a `∀ x` family of exactly these). -/
noncomputable def ResolvedCoassocGrandFullSupply.toGlobalCoverSupply
    (F : ResolvedCoassocGrandFullSupply D G) (x : ResolvedHopfGen)
    (image_agreement : D.regroupImageSum x = ∑ z ∈ F.toFiniteData.imageCarrier, F.toFiniteData.imageWeight z)
    (branch_agreement :
      (∑ q ∈ F.toFiniteData.forestCarrier, D.resolvedSplitChoiceTerm q.1)
        + (∑ q ∈ F.toFiniteData.mixedCarrier, D.resolvedSplitChoiceTerm q.1)
        = D.regroupBranchSum x) :
    ResolvedCoassocGlobalCoverSupply D x where
  repGraph := G
  finite := F.toFiniteData
  image_agreement := image_agreement
  branch_agreement := branch_agreement

/-- **R-6c-heart-6a-12a — the global cover bundle at a generator `x` (via the per-generator supply). -/
noncomputable def ResolvedCoassocGrandFullSupply.toGlobalCoverData
    (F : ResolvedCoassocGrandFullSupply D G) (x : ResolvedHopfGen)
    (image_agreement : D.regroupImageSum x = ∑ z ∈ F.toFiniteData.imageCarrier, F.toFiniteData.imageWeight z)
    (branch_agreement :
      (∑ q ∈ F.toFiniteData.forestCarrier, D.resolvedSplitChoiceTerm q.1)
        + (∑ q ∈ F.toFiniteData.mixedCarrier, D.resolvedSplitChoiceTerm q.1)
        = D.regroupBranchSum x) :
    ResolvedCoassocGlobalCoverData D x :=
  (F.toGlobalCoverSupply x image_agreement branch_agreement).toGlobalCoverData

end GaugeGeometry.QFT.Combinatorial
