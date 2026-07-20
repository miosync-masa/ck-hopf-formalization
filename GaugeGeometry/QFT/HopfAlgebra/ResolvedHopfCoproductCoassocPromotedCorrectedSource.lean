import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocStarRenameContract
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocPromotedStarCorrectingPerm

/-!
# R-6c-body-456 — the forward-owned corrected source graph (canonical representation) (PROVED)

Four-hundred-and-fifty-sixth genuine-body step — a single canonical representation of the forward corrected source graph,
from the forward comparator (body-455) ALONE.  The occurrence's promoted-star contraction equals its hardcoded-star
contraction (`= o.contractedSourceGraph`) relabeled by `ρ = promotedStarCorrectingPerm q o` — the two point laws only
(body-451 `resolvedStarRename_contractWithStars`), NO freshness / injectivity (those were spent building `ρ`).

* `promotedCorrectedOccurrenceSourceGraph q o` — `o.contractedSourceGraph.mapPerm ρ` (the data owner, no proofs);
* `promotedCorrectedSource_eq` — `o.B.1.contractWithStars (promotedOccurrenceStar q o) = promotedCorrected…` (body-451
  with the body-455 point laws and `o.γ.1`'s ambient support);
* `promotedCorrectedSource_vertices` / `_internalEdges` / `_externalLegs` — the three `congrArg` projections (reused by
  the forward corrected-remnant support in a later body).

Per the HALT/guards: this body fixes ONLY the canonical forward representation.  NOT done here: reembed into
`selectedOuterContractGraph`, the corrected `Concrete` provider, any comparison with the recovered `z, δ`, `VBuild`
migration.  Strict `promoted_star_agrees` / recovered inner correction are NOT used; no permutation equality is claimed;
`ρ` fixes only the parent ambient; body-445 stays a valid conditional.  NOT the unconditional theorem.  No facade, no flat
term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

variable {D : ResolvedCoproductProperForestData} (Fstar : ResolvedCanonicalStarFacts D)
  {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
  (o : ResolvedCoassocSplitChoice.ForestChoiceOccurrence q.1)

/-- **R-6c-body-456 — the forward-owned corrected source graph.**  The occurrence's contracted source graph relabeled by
the forward correcting permutation; the data owner for the forward corrected remnant. -/
noncomputable def promotedCorrectedOccurrenceSourceGraph : ResolvedFeynmanGraph :=
  o.contractedSourceGraph.mapPerm (promotedStarCorrectingPerm Fstar q o)

include Fstar

/-- **R-6c-body-456 ∎ — the forward corrected source equality.**  `o.B`'s promoted-star contraction equals its
hardcoded-star contraction (`o.contractedSourceGraph`) relabeled by `ρ`. -/
theorem promotedCorrectedSource_eq :
    o.B.1.contractWithStars (promotedOccurrenceStar q o)
      = promotedCorrectedOccurrenceSourceGraph Fstar q o :=
  resolvedStarRename_contractWithStars o.B.1 (hardcodedOccurrenceStar q o) (promotedOccurrenceStar q o)
    (promotedStarCorrectingPerm Fstar q o)
    (resolvedAmbientSupported_of_subgraphGraph o.γ.1).1
    (resolvedAmbientSupported_of_subgraphGraph o.γ.1).2
    (fun _ hv => promotedStarCorrectingPerm_on_parent_vertices Fstar q o hv)
    (fun _ hγ => promotedStarCorrectingPerm_on_occurrence_stars Fstar q o hγ)

/-- **R-6c-body-456 — the forward corrected source's vertices.** -/
theorem promotedCorrectedSource_vertices :
    (o.B.1.contractWithStars (promotedOccurrenceStar q o)).vertices
      = (promotedCorrectedOccurrenceSourceGraph Fstar q o).vertices :=
  congrArg ResolvedFeynmanGraph.vertices (promotedCorrectedSource_eq Fstar q o)

/-- **R-6c-body-456 — the forward corrected source's internal edges.** -/
theorem promotedCorrectedSource_internalEdges :
    (o.B.1.contractWithStars (promotedOccurrenceStar q o)).internalEdges
      = (promotedCorrectedOccurrenceSourceGraph Fstar q o).internalEdges :=
  congrArg ResolvedFeynmanGraph.internalEdges (promotedCorrectedSource_eq Fstar q o)

/-- **R-6c-body-456 — the forward corrected source's external legs.** -/
theorem promotedCorrectedSource_externalLegs :
    (o.B.1.contractWithStars (promotedOccurrenceStar q o)).externalLegs
      = (promotedCorrectedOccurrenceSourceGraph Fstar q o).externalLegs :=
  congrArg ResolvedFeynmanGraph.externalLegs (promotedCorrectedSource_eq Fstar q o)

end GaugeGeometry.QFT.Combinatorial
