import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRegroupAgreementsBody

/-!
# R-6c-body-38 — regroup agreements reduced to the pure cover reindex

Thirty-eighth genuine-body step, discharging the *linearity descent* half of body-37's representative-coordinate
agreements, leaving only the pure **finite-cover reindex** equalities.

Body-37 established `image_agreement_at_rep` / `branch_agreement_at_rep` at a representative
`repGraph x .toResolvedHopfGen (repCD x)`.  The proved linearity theorems

* `regroupImageSum_eq_outerSum (G) (hCD)` — `regroupImageSum (G.toResolvedHopfGen hCD) = ∑ A ∈
  (D.supply G).forestCarrier, (1 ⊗ (leftTerm A ⊗ rightTerm A) + coassocRightTail …)`;
* `regroupBranchSum_eq_outerSum (G) (hCD)` — the branch analog;

rewrite the regroup side to a sum over the **outer forest carrier**.  So each representative-coordinate
agreement reduces (by one `rw`) to a pure equality between the outer-forest-carrier sum and the GrandFull
finite-cover sum (`imageCarrier`/`imageWeight`, `forestCarrier`+`mixedCarrier`/`splitTerm`) — the resolved
**H5.8 cover reindex**, with no `regroupImageSum`/`forestSum`/tail left.

That reindex is the genuine finishing content (the same double-sum shape already discharged at flat/full-grain
level in R-4-full `h58_resolved_carrier_double_sum_reindex`); per the HALT it is NOT proved here, only isolated
as the two named `*_cover_reindex` fields.

Landed:

* `ResolvedRegroupReindexSupply D` — `repGraph`/`repCD`/`rep_eq`/`grand` + the two pure cover reindex fields;
* `.toRegroupAgreementSupply` — body-37's supply (the `*_agreement_at_rep` fields via one `rw` each);
* `.coassoc_gen` — the capstone.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData}

/-- **R-6c-body-38 — the regroup reindex supply.**  The representative data plus the two pure finite-cover
reindex equalities (outer-forest-carrier sum = GrandFull cover sum), which the proved `…_eq_outerSum` descents
turn into the representative-coordinate agreements. -/
structure ResolvedRegroupReindexSupply (D : ResolvedCoproductProperForestData) where
  /-- A representative resolved graph for each generator. -/
  repGraph : ResolvedHopfGen → ResolvedFeynmanGraph
  /-- The representative is connected-divergent. -/
  repCD : ∀ x : ResolvedHopfGen, (repGraph x).forget.toClass.IsConnectedDivergent
  /-- The representative's class IS the generator. -/
  rep_eq : ∀ x : ResolvedHopfGen, x = (repGraph x).toResolvedHopfGen (repCD x)
  /-- The per-`G` grand full supply at each representative. -/
  grand : ∀ x : ResolvedHopfGen, ResolvedCoassocGrandFullSupply D (repGraph x)
  /-- **Image cover reindex**: the outer-forest image sum = the cover's image-weight sum. -/
  image_cover_reindex : ∀ x : ResolvedHopfGen,
    (∑ A ∈ (D.supply (repGraph x)).forestCarrier,
        ((1 : ResolvedHopfH) ⊗ₜ[ℚ]
            ((D.supply (repGraph x)).leftTerm A ⊗ₜ[ℚ] (D.supply (repGraph x)).rightTerm A)
          + D.coassocRightTail
              ((D.supply (repGraph x)).leftTerm A ⊗ₜ[ℚ] (D.supply (repGraph x)).rightTerm A)))
      = ∑ z ∈ (grand x).toFiniteData.imageCarrier, (grand x).toFiniteData.imageWeight z
  /-- **Branch cover reindex**: the cover's (forest + mixed) term sum = the outer-forest branch sum. -/
  branch_cover_reindex : ∀ x : ResolvedHopfGen,
    (∑ q ∈ (grand x).toFiniteData.forestCarrier, D.resolvedSplitChoiceTerm q.1)
      + (∑ q ∈ (grand x).toFiniteData.mixedCarrier, D.resolvedSplitChoiceTerm q.1)
      = ∑ A ∈ (D.supply (repGraph x)).forestCarrier,
          ((Algebra.TensorProduct.assoc ℚ ℚ ℚ ResolvedHopfH ResolvedHopfH ResolvedHopfH).toAlgHom
              (((D.supply (repGraph x)).leftTerm A ⊗ₜ[ℚ] (D.supply (repGraph x)).rightTerm A)
                ⊗ₜ[ℚ] (1 : ResolvedHopfH))
            + D.coassocLeftTail
                ((D.supply (repGraph x)).leftTerm A ⊗ₜ[ℚ] (D.supply (repGraph x)).rightTerm A))

/-- **R-6c-body-38 — body-37's regroup-agreement supply from the pure cover reindex.**  Each
representative-coordinate agreement is one `rw` by the proved `…_eq_outerSum` linearity descent, then the
cover reindex. -/
noncomputable def ResolvedRegroupReindexSupply.toRegroupAgreementSupply
    (F : ResolvedRegroupReindexSupply D) :
    ResolvedRegroupAgreementSupply D where
  repGraph := F.repGraph
  repCD := F.repCD
  rep_eq := F.rep_eq
  grand := F.grand
  image_agreement_at_rep := fun x => by
    rw [D.regroupImageSum_eq_outerSum (F.repGraph x) (F.repCD x)]; exact F.image_cover_reindex x
  branch_agreement_at_rep := fun x => by
    rw [D.regroupBranchSum_eq_outerSum (F.repGraph x) (F.repCD x)]; exact F.branch_cover_reindex x

/-- **R-6c-body-38 — the capstone from the regroup reindex supply. -/
theorem ResolvedRegroupReindexSupply.coassoc_gen
    (F : ResolvedRegroupReindexSupply D) (x : ResolvedHopfGen) :
    D.coassocLeft (MvPolynomial.X x) = D.coassocRight (MvPolynomial.X x) :=
  F.toRegroupAgreementSupply.coassoc_gen x

end GaugeGeometry.QFT.Combinatorial
