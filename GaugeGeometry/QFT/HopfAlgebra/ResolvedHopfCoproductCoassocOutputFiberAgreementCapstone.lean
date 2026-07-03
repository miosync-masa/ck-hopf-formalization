import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocBranchFiberBody
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocOutputReindexMap

/-!
# R-6c-body-60 — the OUTPUT-fiber agreement capstone: reindex boundary at its minimal form

Sixtieth genuine-body step, a CAPSTONE consolidating bodies 56–59.  With the image / branch fiber
CONSTRUCTIONS discharged (bodies 58/59: fiber = `selectedOuter ∘ imageOf` / base-outer `s.1`, `maps_to` =
`Finset.mem_attach`), the OUTPUT σ-cover double sum needs only the two per-`A` expansion AGREEMENTS.  This step
bundles a representative family with exactly those two agreements and re-exports to `coassoc_gen` — fixing the
OUTPUT reindex boundary at its smallest form.

## The boundary, minimized

`ResolvedOutputAgreementFamilySupply D` carries the support-9 representative lift (`repGraph` / `repCD` /
`rep_eq` / `grand`, the INPUT-side leaves) plus, per generator, ONE image agreement and ONE branch agreement:

* `imageAgree x : ResolvedImageFiberAgreementSupply (grand x)` — the RIGHT-expansion coverage (body-58);
* `branchAgree x : ResolvedBranchFiberAgreementSupply (grand x)` — the LEFT-expansion coverage (body-59).

Everything else in the OUTPUT chain — the two canonical fiber maps, both `maps_to`, the fibration engine
(body-55), the partition bridge (body-53), the σ-cover skeleton (body-54), and the reindex → `coassoc_gen`
wiring (bodies 38/57) — is PROVED.  So the OUTPUT reindex's primitive leaves are now EXACTLY the two per-`A`
expansion agreements `image_fiber_agree` + `branch_fiber_agree`.

## The chain

`toRegroupReindexSupply` feeds the two agreement families through `toImageFiberSupply` / `toBranchFiberSupply`
(bodies 58/59) into body-57's `resolved_regroupReindex_of_fibers`; `coassoc_gen` is then body-57's capstone.

Per the HALT, neither agreement proof is entered, and no representative-family / finite-cover construction is
touched — a thin adapter / re-export only.

Landed:

* `ResolvedOutputAgreementFamilySupply D` — the minimal OUTPUT-reindex supply (rep family + 2 agreements);
* `.toRegroupReindexSupply` — to body-38's supply via the canonical fibers;
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

/-- **R-6c-body-60 — the minimal OUTPUT-reindex supply.**  A representative family plus, per generator, exactly
one image (RIGHT-expansion) and one branch (LEFT-expansion) agreement — the two primitive OUTPUT leaves left
after bodies 56–59 discharged the fiber constructions. -/
structure ResolvedOutputAgreementFamilySupply (D : ResolvedCoproductProperForestData) where
  /-- A representative resolved graph for each generator. -/
  repGraph : ResolvedHopfGen → ResolvedFeynmanGraph
  /-- The representative is connected-divergent. -/
  repCD : ∀ x : ResolvedHopfGen, (repGraph x).forget.toClass.IsConnectedDivergent
  /-- The representative's class IS the generator. -/
  rep_eq : ∀ x : ResolvedHopfGen, x = (repGraph x).toResolvedHopfGen (repCD x)
  /-- The per-`G` grand full supply at each representative. -/
  grand : ∀ x : ResolvedHopfGen, ResolvedCoassocGrandFullSupply D (repGraph x)
  /-- The image-side RIGHT-expansion agreement at each representative. -/
  imageAgree : ∀ x : ResolvedHopfGen, ResolvedImageFiberAgreementSupply (grand x)
  /-- The branch-side LEFT-expansion agreement at each representative. -/
  branchAgree : ∀ x : ResolvedHopfGen, ResolvedBranchFiberAgreementSupply (grand x)

/-- **R-6c-body-60 — to body-38's regroup reindex supply, via the canonical fibers.**  The two agreement
families feed `toImageFiberSupply` / `toBranchFiberSupply` (bodies 58/59) into body-57's assembler. -/
noncomputable def ResolvedOutputAgreementFamilySupply.toRegroupReindexSupply
    (S : ResolvedOutputAgreementFamilySupply D) : ResolvedRegroupReindexSupply D :=
  resolved_regroupReindex_of_fibers S.repGraph S.repCD S.rep_eq S.grand
    (fun x => (S.imageAgree x).toImageFiberSupply)
    (fun x => (S.branchAgree x).toBranchFiberSupply)

/-- **R-6c-body-60 — the OUTPUT-fiber agreement capstone.**  From the representative family and the two per-`x`
expansion agreements, `Δᵣ`-coassociativity on every generator.  The OUTPUT reindex is now fully proved except
`image_fiber_agree` + `branch_fiber_agree`. -/
theorem ResolvedOutputAgreementFamilySupply.coassoc_gen
    (S : ResolvedOutputAgreementFamilySupply D) (x : ResolvedHopfGen) :
    D.coassocLeft (MvPolynomial.X x) = D.coassocRight (MvPolynomial.X x) :=
  resolved_output_reindex_of_fibers S.repGraph S.repCD S.rep_eq S.grand
    (fun x => (S.imageAgree x).toImageFiberSupply)
    (fun x => (S.branchAgree x).toBranchFiberSupply) x

end GaugeGeometry.QFT.Combinatorial
