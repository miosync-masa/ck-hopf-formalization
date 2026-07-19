import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightTermAlpha
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocContractTwiceQuotEq

/-!
# R-6c-body-406 — the correcting-permutation right-term provider (PROVED issuance window)

Four-hundred-and-sixth genuine-body step — the formal ISSUANCE WINDOW that turns a correcting permutation into a
`rightTerm_mapPerm` certificate.  Body-405 replaced the inconsistent strict `star_mapPerm` with the consistent
`rightTerm_mapPerm`; this body proves that a class-level correcting-permutation datum discharges it.

Type audit: the existing `ResolvedRightPermExtensionSupply.starPerm` is per-split-choice (one-stage vs two-stage
contraction), whereas `rightTerm_mapPerm` is the `∀ G σ A` same-forest RELABELING — same technique, DIFFERENT instance.
The reused engines are `ResolvedContractTwiceClassData` (its `starPerm` = `τ` with `new = old.mapPerm τ`) and
`resolved_rightTerm_eq_of_class_eq`.

* `ResolvedRightTermCorrectingPermSupply D` — the minimal class-level socket: for each `(G, σ, A)` a
  `ResolvedContractTwiceClassData (newContract) (oldContract)` (`τ` relabels the relabeled contraction to the original);
* `rightTerm_mapPerm_of_correctingPerm` — the right-term equality from `classData.classEq` (via
  `resolved_rightTerm_eq_of_class_eq`); the `classEq` direction is `new = old`, so the `old = new` field needs a `.symm`;
* `ResolvedRightTermCorrectingPermSupply.toRightTermAlphaSupply` — the body-404 alpha law issued from the correcting
  permutation.

Per the HALT: NO strict star equality is revived; the coassoc-side `starPerm` instance is NOT reused at the wrong type;
the correcting permutation's EXISTENCE is NOT yet claimed (body-407 builds `τ` from fresh/injective stars); this does NOT
plug into `W.rightTerm_mapPerm` yet.  This body fixes only: "given `τ` + the three field equalities, the alpha law is
issuable".  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
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

/-- **R-6c-body-406 — the correcting-permutation class-level socket.**  A per-`(G, σ, A)` star-geometry datum whose
`starPerm` `τ` relabels the relabeled contraction back to the original: `new = old.mapPerm τ`. -/
structure ResolvedRightTermCorrectingPermSupply (D : ResolvedCoproductProperForestData) where
  /-- The two-stage class datum: `τ` sends the relabeled forest's contraction to the original forest's contraction. -/
  classData : ∀ (G : ResolvedFeynmanGraph) (σ : Equiv.Perm VertexId)
    (A : ResolvedAdmissibleSubgraph G) (_hA : A ∈ D.carrier G)
    (_hAσ : A.mapPerm σ ∈ D.carrier (G.mapPerm σ)),
    ResolvedContractTwiceClassData
      ((A.mapPerm σ).contractWithStars (D.starOf (G.mapPerm σ) (A.mapPerm σ)))
      (A.contractWithStars (D.starOf G A))

/-- **R-6c-body-406 — the right-term equality from a correcting permutation** (`classEq.symm` + class-level rightTerm). -/
theorem rightTerm_mapPerm_of_correctingPerm (Corr : ResolvedRightTermCorrectingPermSupply D)
    (G : ResolvedFeynmanGraph) (σ : Equiv.Perm VertexId) (A : ResolvedAdmissibleSubgraph G)
    (hA : A ∈ D.carrier G) (hAσ : A.mapPerm σ ∈ D.carrier (G.mapPerm σ)) :
    resolvedForestRightTerm A (D.starOf G A) (D.hCD G A hA)
      = resolvedForestRightTerm (A.mapPerm σ) (D.starOf (G.mapPerm σ) (A.mapPerm σ))
          (D.hCD (G.mapPerm σ) (A.mapPerm σ) hAσ) :=
  resolved_rightTerm_eq_of_class_eq ⟨A, hA⟩ ⟨A.mapPerm σ, hAσ⟩
    (Corr.classData G σ A hA hAσ).classEq.symm

/-- **R-6c-body-406 — the body-404 alpha law issued from the correcting permutation.** -/
def ResolvedRightTermCorrectingPermSupply.toRightTermAlphaSupply
    (Corr : ResolvedRightTermCorrectingPermSupply D) : ResolvedRightTermAlphaSupply D where
  rightTerm_mapPerm := fun G σ A hA hAσ => rightTerm_mapPerm_of_correctingPerm Corr G σ A hA hAσ

end GaugeGeometry.QFT.Combinatorial
