import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCorrectedFamilyDisjoint

/-!
# R-6c-body-465 — the corrected remnant class equality + component nonemptiness + injectivity (PROVED)

Four-hundred-and-sixty-fifth genuine-body step — the alpha-native remnant class-and-injectivity leaves that feed the
generator equality (`remnantGen`) and the injectivity (`remnantInj`) of the eventual corrected abstract remnant supply.
These are the parts that need NO connected-divergence bridge (that bridge — subgraph-forget ↔ graph-class CD — is the
next body, alongside the `ResolvedRemnantComponentSupply` / `ResolvedRemnantDecontractionSupply` assembly).

* `correctedRemnantComponent_class_eq` — the corrected component's intrinsic-graph CLASS equals the uncorrected
  contracted source's class; the legacy `remnantGraph_eq` (a false graph equality `corrected = uncorrected`) is NOT used —
  only `ResolvedFeynmanGraph.toResolvedClass_mapPerm` (relabeling is an iso) after the reembed projection (`rfl`);
* `correctedRemnantComponent_vertices_nonempty` — a genuine vertex witness (a promoted-star vertex of a
  `CarrierProper`-nonempty component of `o.B`), NOT back-derived from CD;
* `correctedRemnantComponent_injective` — the corrected component map is injective: distinct occurrences give distinct
  components, else body-464's disjointness makes a nonempty component self-disjoint.

Per the HALT/guards: NO `corrected = uncorrected` graph equality is created; the legacy `remnantGraph_eq` socket is NOT
used; vertex-nonemptiness is a `CarrierProper` witness, NOT fabricated from CD; `remnantCD` and the full remnant supply,
`hcross`, `hRdisj`, `quotient_mem`, `quot_eq` are NOT touched; strict `StarProm` / `InnerStarRaw` NOT used; body-445 stays
a valid conditional.  NOT the unconditional theorem.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO
`promote_collapse` / singleton / floor-297.
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

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}
  (s : ResolvedCoassocSplitChoice D G) (Fstar : ResolvedCanonicalStarFacts D)

/-- **R-6c-body-465 — the corrected remnant's class equality.**  The corrected component's intrinsic graph is
class-equal to the uncorrected contracted source (relabeling is an iso). -/
theorem correctedRemnantComponent_class_eq (o : s.ForestChoiceOccurrence) :
    ((canonicalCorrectedRemnantReembedSupply s Fstar).correctedRemnantComponent o).toResolvedFeynmanGraph.toResolvedClass
      = o.contractedSourceGraph.toResolvedClass := by
  show (o.contractedSourceGraph.mapPerm (promotedStarCorrectingPerm Fstar s o)).toResolvedClass
    = o.contractedSourceGraph.toResolvedClass
  exact ResolvedFeynmanGraph.toResolvedClass_mapPerm _ _

variable (CarrierProper : ResolvedCarrierProperProvider D)

include CarrierProper in
/-- **R-6c-body-465 — the corrected remnant component is vertex-nonempty.**  A promoted-star vertex of a
`CarrierProper`-nonempty component of `o.B` (NO back-derivation from CD). -/
theorem correctedRemnantComponent_vertices_nonempty (o : s.ForestChoiceOccurrence) :
    ((canonicalCorrectedRemnantReembedSupply s Fstar).correctedRemnantComponent o).vertices.Nonempty := by
  rw [correctedRemnantComponent_vertices_eq_promoted s o Fstar,
    ResolvedAdmissibleSubgraph.contractWithStars_vertices]
  obtain ⟨b, hb⟩ := ResolvedAdmissibleSubgraph.isNonempty_of_isProperForest
    (CarrierProper.carrier_isProperForest o.γ.1.toResolvedFeynmanGraph o.B.1 o.B.2)
  exact ⟨promotedOccurrenceStar s o b, Finset.mem_union.mpr
    (Or.inr (ResolvedAdmissibleSubgraph.mem_starVertices.mpr ⟨b, hb, rfl⟩))⟩

include CarrierProper in
/-- **R-6c-body-465 ∎ — the corrected remnant component map is injective.**  Distinct occurrences give distinct
components — else body-464's disjointness makes a nonempty component self-disjoint. -/
theorem correctedRemnantComponent_injective :
    Function.Injective
      (fun o : s.ForestChoiceOccurrence =>
        (canonicalCorrectedRemnantReembedSupply s Fstar).correctedRemnantComponent o) := by
  intro o o' heq
  simp only [] at heq
  by_contra hne
  have hdisj := correctedRemnantComponent_disjoint s Fstar CarrierProper o o' hne
  obtain ⟨w, hw⟩ := correctedRemnantComponent_vertices_nonempty s Fstar CarrierProper o
  exact absurd (heq ▸ hw) (Finset.disjoint_left.mp hdisj hw)

end GaugeGeometry.QFT.Combinatorial
