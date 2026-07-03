import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocBranchFiberAgreementBody
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocImageFiberAgreementBody
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocOutputFiberAgreementCapstone

/-!
# R-6c-body-63 — the OUTPUT cover capstone: primitive leaves updated to the two cover fields

Sixty-third genuine-body step, a CAPSTONE updating body-60's minimal OUTPUT-reindex boundary from the two
fiber AGREEMENTS to the two pure COVER fields — after bodies 61/62 reduced each agreement (via the pre-existing
`coassocLeftTail_eq_splitChoiceTermSum` / `coassocRightTail_forestSummand` tail theorems) to a single cover.

## The boundary, updated

`ResolvedOutputCoverFamilySupply D` carries the support-9 representative lift (`repGraph` / `repCD` / `rep_eq`
/ `grand`) plus, per generator, exactly ONE image cover and ONE branch cover:

* `imageCover x : ResolvedImageFiberCoverSupply (grand x)` — the RIGHT de-contraction cover (body-62);
* `branchCover x : ResolvedBranchFiberCoverSupply (grand x)` — the LEFT pure sum cover (body-61).

Everything else in the OUTPUT chain is PROVED: the two tail theorems (bodies 61/62), the canonical fibers +
`maps_to` (bodies 58/59), the fibration engine (body-55), the partition bridge (body-53), the σ-cover skeleton
(body-54), and the reindex → `coassoc_gen` wiring (bodies 38/57/60).  So the OUTPUT reindex's primitive leaves
are now EXACTLY the two cover fields `image_cover` + `branch_cover`.

## The chain

`toOutputAgreementFamilySupply` lifts each cover to its agreement (bodies 61/62's
`toBranchFiberAgreementSupply` / `toImageFiberAgreementSupply`), landing body-60's
`ResolvedOutputAgreementFamilySupply`; `coassoc_gen` is then body-60's capstone.

Per the HALT, neither cover proof is entered, and no representative-family / finiteness construction is touched
— a thin adapter / re-export only.

Landed:

* `ResolvedOutputCoverFamilySupply D` — the OUTPUT-reindex supply at cover granularity (rep family + 2 covers);
* `.toOutputAgreementFamilySupply` — to body-60's agreement family via the two tail theorems;
* `.coassoc_gen` — `Δᵣ`-coassociativity on every generator.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData}

set_option linter.unusedSectionVars false

/-- **R-6c-body-63 — the OUTPUT-reindex supply at cover granularity.**  A representative family plus, per
generator, exactly one image (RIGHT de-contraction) and one branch (LEFT pure sum) cover — the two primitive
OUTPUT leaves left after bodies 61/62 discharged the fiber agreements' tail content. -/
structure ResolvedOutputCoverFamilySupply (D : ResolvedCoproductProperForestData) where
  /-- A representative resolved graph for each generator. -/
  repGraph : ResolvedHopfGen → ResolvedFeynmanGraph
  /-- The representative is connected-divergent. -/
  repCD : ∀ x : ResolvedHopfGen, (repGraph x).forget.toClass.IsConnectedDivergent
  /-- The representative's class IS the generator. -/
  rep_eq : ∀ x : ResolvedHopfGen, x = (repGraph x).toResolvedHopfGen (repCD x)
  /-- The per-`G` grand full supply at each representative. -/
  grand : ∀ x : ResolvedHopfGen, ResolvedCoassocGrandFullSupply D (repGraph x)
  /-- The image-side RIGHT de-contraction cover at each representative. -/
  imageCover : ∀ x : ResolvedHopfGen, ResolvedImageFiberCoverSupply (grand x)
  /-- The branch-side LEFT pure sum cover at each representative. -/
  branchCover : ∀ x : ResolvedHopfGen, ResolvedBranchFiberCoverSupply (grand x)

/-- **R-6c-body-63 — to body-60's agreement family, via the two tail theorems.**  Each cover lifts to its
agreement through bodies 61/62. -/
def ResolvedOutputCoverFamilySupply.toOutputAgreementFamilySupply
    (S : ResolvedOutputCoverFamilySupply D) : ResolvedOutputAgreementFamilySupply D where
  repGraph := S.repGraph
  repCD := S.repCD
  rep_eq := S.rep_eq
  grand := S.grand
  imageAgree := fun x => (S.imageCover x).toImageFiberAgreementSupply
  branchAgree := fun x => (S.branchCover x).toBranchFiberAgreementSupply

/-- **R-6c-body-63 — the OUTPUT cover capstone.**  From the representative family and the two per-`x` covers,
`Δᵣ`-coassociativity on every generator.  The OUTPUT reindex is now fully proved except `image_cover` +
`branch_cover`. -/
theorem ResolvedOutputCoverFamilySupply.coassoc_gen
    (S : ResolvedOutputCoverFamilySupply D) (x : ResolvedHopfGen) :
    D.coassocLeft (MvPolynomial.X x) = D.coassocRight (MvPolynomial.X x) :=
  S.toOutputAgreementFamilySupply.coassoc_gen x

end GaugeGeometry.QFT.Combinatorial
