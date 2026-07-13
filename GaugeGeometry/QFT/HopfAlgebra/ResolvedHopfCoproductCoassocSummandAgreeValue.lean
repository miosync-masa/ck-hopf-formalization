import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocConcreteSummandValue
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocConcreteSummandBundle

/-!
# R-6c-body-254 — value-side summand agreement: the term equality with a `Forward`-free statement (PROVED)

Two-hundred-and-fifty-fourth genuine-body step — the term-agreement path over the value root.  The summand agreement
`D.resolvedSplitChoiceTerm q = leftTerm(outer) ⊗ (leftTerm(quot) ⊗ rightTerm(quot))` is restated with its `outer` and
`quot` taken from `fwdMapFilteredValue` (body-252, value root, no `Forward`) — so the **statement** never mentions the
retired total root.  `.ofLegacy` discharges it from the legacy `S.summand_agree` by `rfl`-defeq (every RHS factor is
defeq via `selectedOuter_eq` + proof irrelevance), the migration-check.

## Why the statement is `Forward`-free

`(D.supply G).leftTerm` reads only `.1` (the raw forest) — `leftTerm A = resolvedForestLeftTerm A.1`
(`ResolvedHopfCoproductSupply.lean:153`); the outer tag `(fwdMapFilteredValue F V q).1` comes from the **filtered**
`F.mem_of_mem_forestBlockDomFinset`, not `S.Forward`.  `rightTerm` reads the `.2` tag — but that tag lives on
`(fwdMapFilteredValue F V q).2 = V.quotientForestRaw q.1`, a contract-graph `ForestIdx` carried by the value root
(Forward-free).  So the whole term equality stands on `selectedOuterRawOf` + `F` + `V.quotientForestRaw` — no `Forward`.

## The value summand-agreement supply + `.ofLegacy`

```lean
structure ResolvedSummandAgreeValueSupply (F) (V) where
  summand_agree_value : ∀ q, D.resolvedSplitChoiceTerm q.1
      = leftTerm (fwdMapFilteredValue F V q).1 ⊗ (leftTerm (…).2 ⊗ rightTerm (…).2)
```

`.ofLegacy S : ResolvedSummandAgreeValueSupply F (ofLegacy S)` sets `summand_agree_value := fun q => S.summand_agree q.1`
— accepted by `rfl`-defeq: for `V = ofLegacy S`, `(fwdMapFilteredValue F (ofLegacy S) q).1 =
S.toSummandBundle.selected.selectedOuterOf q.1` (`selectedOuter_eq` + proof irrelevance on the tag) and
`(fwdMapFilteredValue …).2 = S.toSummandBundle.quotientForest q.1`, so the two term equalities are defeq.

## Audit — where the retired total root remains

After this body, `ResolvedConcreteSummandBundleSupply.Forward` (the total root) appears in a *declaration type* only in
migration-check comparison lemmas — `fwdMapFilteredValue_ofLegacy_eq` (body-252), the `FwdMapFiltered.lean` legacy
bridge, `ResolvedWitnessSplitFilteredCoverSupply.ofLegacy` (body-250), and this file's `.ofLegacy`.  The canonical
value declarations (round-trip cover/branch data body-253, the value bundle body-252, this term equality) are all
`Forward`-free in their statements.  The remaining *proof-level* dependence — a fully canonical discharge of
`summand_agree_value` (and a filtered `selected` image supply, since `ResolvedSummandFactorBundle.selected` is total)
via the Forward-free factor-eqs path (`resolved_splitChoice_summand_agree_of_factor_eqs`,
`ForestCarryingBlock.lean:68`) — is the follow-up; it discharges the supply field itself without `S`.

Per the HALT: the value summand-agreement supply (Forward-free statement) + the migration-check `.ofLegacy` are
defined/proved; the residual (canonical discharge via factor-eqs; the total `selected` field) is named.  No bundle field
is changed.  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-254 — the value-side summand agreement.**  The term equality with outer/quotient from
`fwdMapFilteredValue` (value root); the statement never mentions the retired total root. -/
structure ResolvedSummandAgreeValueSupply (F : ResolvedSelectedOuterFilteredMemSupply D)
    (V : ResolvedConcreteSummandValueSupply D) where
  /-- The resolved split-choice term factors as `leftTerm(outer) ⊗ (leftTerm(quot) ⊗ rightTerm(quot))`, all over the
  value root. -/
  summand_agree_value : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G),
    D.resolvedSplitChoiceTerm (q.1 : ResolvedCoassocSplitChoice D G)
      = (D.supply G).leftTerm (fwdMapFilteredValue F V q).1 ⊗ₜ[ℚ]
          ((D.supply ((fwdMapFilteredValue F V q).1.1.contractWithStars
              (D.starOf G (fwdMapFilteredValue F V q).1.1))).leftTerm (fwdMapFilteredValue F V q).2
            ⊗ₜ[ℚ] (D.supply ((fwdMapFilteredValue F V q).1.1.contractWithStars
              (D.starOf G (fwdMapFilteredValue F V q).1.1))).rightTerm (fwdMapFilteredValue F V q).2)

/-- **R-6c-body-254 — the value summand agreement from a legacy bundle** (migration-check, `rfl`-defeq).  For
`V = ofLegacy S` the term equality is defeq to `S.summand_agree`. -/
def ResolvedSummandAgreeValueSupply.ofLegacy (F : ResolvedSelectedOuterFilteredMemSupply D)
    (S : ResolvedConcreteSummandBundleSupply D) :
    ResolvedSummandAgreeValueSupply F (ResolvedConcreteSummandValueSupply.ofLegacy S) where
  summand_agree_value := fun {G} q => S.summand_agree q.1

end GaugeGeometry.QFT.Combinatorial
