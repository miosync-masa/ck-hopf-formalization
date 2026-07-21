import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCorrectedRemnantClass
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRemnantDecontraction
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRemnant

/-!
# R-6c-body-466 — the corrected CD bridge + abstract remnant supply (PROVED)

Four-hundred-and-sixty-sixth genuine-body step — the connected-divergence type-boundary lemma isolated as a public
generic bridge, the corrected remnant CD it yields, and the two abstract remnant supplies (de-contraction supply →
`remnantGen`; component supply from CD + body-464 disjointness).

* `reembedAsSubgraph_forget_isConnectedDivergent_of_graph` — the GENERIC bridge: a graph's forget-CD transports to the
  forget-CD of its `reembedAsSubgraph` (connected/1PI defeq off the shared intrinsic graph; divergence by
  `IsAmbientInvariantDivergence.degree_self_eq`).  A public ownership bridge — the `Coassoc.lean` private helper is NOT
  reused;
* `correctedRemnantComponent_cd` — `D.hCD → isConnectedDivergent_toClass → forget_mapPerm →
  mapPerm_isConnectedDivergent_iff → generic bridge` (the direct `D.hCD → mapPerm → reembed` ownership route, NOT via the
  body-465 class equality);
* `canonicalCorrectedRemnantDecontractionSupply` (+ `correctedRemnantComponent_gen`) — component + CD + class-equality,
  whence `.remnantGen`;
* `canonicalCorrectedRemnantComponentSupply` — component + CD + body-464 disjointness (specialized to the
  `forestComponentOccurrence` image);
* `correctedRemnantComponent_forestOccurrence_injective` — the V-shaped `remnantInj` leaf.

Per the HALT/guards: `hcross` / `hRdisj` / `quotient_mem` / `quot_eq` are NOT touched — family quotient ownership stays a
separate front; strict `StarProm` / `InnerStarRaw` NOT used; no `corrected = uncorrected` graph equality; body-445 stays a
valid conditional.  NOT the unconditional theorem.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO
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

/-- **R-6c-body-466 — the generic graph-CD → reembedded-subgraph-CD bridge.**  A public ownership bridge (the
`Coassoc.lean` private helper is not reused). -/
theorem reembedAsSubgraph_forget_isConnectedDivergent_of_graph
    {H K : ResolvedFeynmanGraph} (hV : H.vertices ⊆ K.vertices)
    (hE : H.internalEdges ≤ K.internalEdges) (hL : H.externalLegs ≤ K.externalLegs)
    (hes : ∀ e ∈ H.internalEdges, e.source ∈ H.vertices ∧ e.target ∈ H.vertices)
    (hls : ∀ ℓ ∈ H.externalLegs, ℓ.attachedTo ∈ H.vertices)
    (hH : H.forget.IsConnectedDivergent) :
    (H.reembedAsSubgraph K hV hE hL hes hls).forget.IsConnectedDivergent := by
  obtain ⟨hG, hself⟩ := hH
  refine ⟨hself.1, hself.2.1, ?_⟩
  have hdeg : DivergenceMeasure.degree ((H.reembedAsSubgraph K hV hE hL hes hls).forget)
      = DivergenceMeasure.degree (FeynmanSubgraph.self H.forget hG) := by
    rw [← IsAmbientInvariantDivergence.degree_self_eq
        ((H.reembedAsSubgraph K hV hE hL hes hls).forget),
      ← IsAmbientInvariantDivergence.degree_self_eq (FeynmanSubgraph.self H.forget hG)]
    rfl
  show 0 ≤ FeynmanSubgraph.divergenceDegree _
  unfold FeynmanSubgraph.divergenceDegree
  rw [hdeg]
  exact hself.2.2

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}
  (s : ResolvedCoassocSplitChoice D G) (Fstar : ResolvedCanonicalStarFacts D)

/-- **R-6c-body-466 — the corrected remnant component is connected-divergent.**  `D.hCD → mapPerm → reembed`. -/
theorem correctedRemnantComponent_cd (o : s.ForestChoiceOccurrence) :
    ((canonicalCorrectedRemnantReembedSupply s Fstar).correctedRemnantComponent o).forget.IsConnectedDivergent := by
  apply reembedAsSubgraph_forget_isConnectedDivergent_of_graph
  rw [ResolvedFeynmanGraph.forget_mapPerm, FeynmanGraph.mapPerm_isConnectedDivergent_iff]
  exact (FeynmanGraphClass.isConnectedDivergent_toClass o.contractedSourceGraph.forget).mp
    (D.hCD o.γ.1.toResolvedFeynmanGraph o.B.1 o.B.2)

/-- **R-6c-body-466 — the corrected remnant de-contraction supply** (component + CD + class equality). -/
noncomputable def canonicalCorrectedRemnantDecontractionSupply :
    ResolvedRemnantDecontractionSupply D G s where
  remnantComponent := fun o => (canonicalCorrectedRemnantReembedSupply s Fstar).correctedRemnantComponent o
  remnantCD := fun o => correctedRemnantComponent_cd s Fstar o
  remnantClass_eq := fun o => correctedRemnantComponent_class_eq s Fstar o

/-- **R-6c-body-466 — the corrected remnant generator equality** (from the de-contraction supply). -/
theorem correctedRemnantComponent_gen (o : s.ForestChoiceOccurrence) :
    resolvedComponentGenTerm
        ((canonicalCorrectedRemnantReembedSupply s Fstar).correctedRemnantComponent o)
      = o.rightTermOf :=
  (canonicalCorrectedRemnantDecontractionSupply s Fstar).remnantGen o

variable (CarrierProper : ResolvedCarrierProperProvider D)

include CarrierProper in
/-- **R-6c-body-466 ∎ — the abstract corrected remnant component supply** (component + CD + disjointness). -/
noncomputable def canonicalCorrectedRemnantComponentSupply :
    ResolvedRemnantComponentSupply D G where
  remnantComponent := fun s o => (canonicalCorrectedRemnantReembedSupply s Fstar).correctedRemnantComponent o
  remnantCD := fun s o => correctedRemnantComponent_cd s Fstar o
  remnantDisjoint := fun s => by
    intro δ hδ δ' hδ' hne
    obtain ⟨γ₁, _, rfl⟩ := Finset.mem_image.mp hδ
    obtain ⟨γ₂, _, rfl⟩ := Finset.mem_image.mp hδ'
    exact correctedRemnantComponent_disjoint s Fstar CarrierProper _ _
      (fun hoc => hne (congrArg
        (fun o => (canonicalCorrectedRemnantReembedSupply s Fstar).correctedRemnantComponent o) hoc))

include CarrierProper in
/-- **R-6c-body-466 — the V-shaped `remnantInj` leaf** (injectivity over the forest-component occurrences). -/
theorem correctedRemnantComponent_forestOccurrence_injective :
    Function.Injective (fun γ : {x : _ // x ∈ s.forestComponents} =>
      (canonicalCorrectedRemnantReembedSupply s Fstar).correctedRemnantComponent
        (s.forestComponentOccurrence γ)) := by
  intro γ₁ γ₂ heq
  simp only [] at heq
  have hocc : s.forestComponentOccurrence γ₁ = s.forestComponentOccurrence γ₂ :=
    correctedRemnantComponent_injective s Fstar CarrierProper heq
  exact Subtype.ext (congrArg (fun o => o.γ) hocc)

end GaugeGeometry.QFT.Combinatorial
