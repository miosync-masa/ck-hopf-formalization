import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCorrectedFamilyAudit
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCarrierProperProvider

/-!
# R-6c-body-464 — the corrected remnant family disjointness (PROVED)

Four-hundred-and-sixty-fourth genuine-body step — the one genuinely-new GEOMETRY field of the alpha-native corrected
family: the corrected remnant components are pairwise disjoint in the quotient graph.  Proved WITHOUT comparing distinct
`ρ`'s and WITHOUT claiming `mapPerm` preserves disjointness — each corrected component is rewritten to its common
promoted-star contraction (body-456), and the four vertex cases are separated inside the quotient ambient.

* `ForestChoiceOccurrence.eq_of_parent_eq` — parent uniqueness: `o.γ.1 = o'.γ.1 → o = o'` (`o.hchoice` pins `B`);
* `correctedRemnantComponent_vertices_eq_promoted` — the reembed projection composed with body-456;
* `correctedRemnantComponent_disjoint` — the four-case separation (survivor/survivor by parent disjointness;
  survivor/star and star/survivor by `Fstar.starOf_fresh` on the shared selected outer; star/star by
  `Fstar.starOf_injective` + a `CarrierProper` component-nonempty witness contradicting parent disjointness);
* `canonicalAlphaNativeCorrectedFamilySupply` — the canonical inhabitant of the body-462 prototype (`family` from the
  body-463 total provider, `remnantDisjoint` from the theorem).

Per the HALT/guards: distinct `ρ`'s are NOT compared; `mapPerm`-disjointness is NOT claimed; strict `StarProm` /
`InnerStarRaw` NOT used; the star/star nonemptiness EXPLICITLY consumes `CarrierProper`'s component-nonempty conjunct (no
CD back-derivation); `remnantCD` / `remnantGen` / `remnantInj`, cross, and quotient ownership are NOT touched; body-445
stays a valid conditional.  NOT the unconditional theorem.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO
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

/-- **R-6c-body-464 — parent uniqueness of a forest-choice occurrence.**  Two occurrences with the same input outer
component are equal (`o.hchoice` pins the chosen sub-forest). -/
theorem ForestChoiceOccurrence.eq_of_parent_eq {s : ResolvedCoassocSplitChoice D G}
    {o o' : s.ForestChoiceOccurrence} (h : o.γ.1 = o'.γ.1) : o = o' := by
  obtain ⟨γ, B, hc⟩ := o
  obtain ⟨γ', B', hc'⟩ := o'
  obtain rfl : γ = γ' := Subtype.ext h
  obtain rfl : B = B' := Sum.inr.inj (hc.symm.trans hc')
  rfl

variable (s : ResolvedCoassocSplitChoice D G) (o : s.ForestChoiceOccurrence)
  (Fstar : ResolvedCanonicalStarFacts D)

/-- **R-6c-body-464 — the corrected remnant component's vertices are the promoted-star contraction's.** -/
theorem correctedRemnantComponent_vertices_eq_promoted :
    ((canonicalCorrectedRemnantReembedSupply s Fstar).correctedRemnantComponent o).vertices
      = (o.B.1.contractWithStars (promotedOccurrenceStar s o)).vertices :=
  (promotedCorrectedSource_vertices Fstar s o).symm

variable (CarrierProper : ResolvedCarrierProperProvider D)

include CarrierProper in
/-- **R-6c-body-464 ∎ — the corrected remnant components are pairwise disjoint.** -/
theorem correctedRemnantComponent_disjoint (o o' : s.ForestChoiceOccurrence) (hne : o ≠ o') :
    ((canonicalCorrectedRemnantReembedSupply s Fstar).correctedRemnantComponent o).Disjoint
      ((canonicalCorrectedRemnantReembedSupply s Fstar).correctedRemnantComponent o') := by
  have hneγ : o.γ.1 ≠ o'.γ.1 := fun h => hne (ForestChoiceOccurrence.eq_of_parent_eq h)
  have hParentDisj : _root_.Disjoint o.γ.1.vertices o'.γ.1.vertices :=
    s.1.1.pairwiseDisjoint o.γ.2 o'.γ.2 hneγ
  rw [ResolvedFeynmanSubgraph.Disjoint,
    correctedRemnantComponent_vertices_eq_promoted s o Fstar,
    correctedRemnantComponent_vertices_eq_promoted s o' Fstar,
    ResolvedAdmissibleSubgraph.contractWithStars_vertices,
    ResolvedAdmissibleSubgraph.contractWithStars_vertices,
    ResolvedFeynmanSubgraph.toResolvedFeynmanGraph_vertices,
    ResolvedFeynmanSubgraph.toResolvedFeynmanGraph_vertices, Finset.disjoint_left]
  intro v hv hv'
  rw [Finset.mem_union] at hv hv'
  -- `v ∉ G.vertices` from a star membership.
  have star_notMemG : ∀ (p : s.ForestChoiceOccurrence),
      v ∈ p.B.1.starVertices (promotedOccurrenceStar s p) → v ∉ G.vertices := by
    intro p hvp
    rw [ResolvedAdmissibleSubgraph.mem_starVertices] at hvp
    obtain ⟨b, hb, rfl⟩ := hvp
    exact Fstar.starOf_fresh G ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s)
      (p.γ.1.promote b) (promote_mem_selectedOuterRawOf_raw s p hb)
  rcases hv with hvL | hvR
  · rcases hv' with hvL' | hvR'
    · -- survivor / survivor
      rw [Finset.mem_sdiff] at hvL hvL'
      exact Finset.disjoint_left.mp hParentDisj hvL.1 hvL'.1
    · -- survivor / star
      rw [Finset.mem_sdiff] at hvL
      exact star_notMemG o' hvR' (o.γ.1.vertices_subset hvL.1)
  · rcases hv' with hvL' | hvR'
    · -- star / survivor
      rw [Finset.mem_sdiff] at hvL'
      exact star_notMemG o hvR (o'.γ.1.vertices_subset hvL'.1)
    · -- star / star
      rw [ResolvedAdmissibleSubgraph.mem_starVertices] at hvR hvR'
      obtain ⟨b, hb, hbv⟩ := hvR
      obtain ⟨b', hb', hbv'⟩ := hvR'
      have hpromEq : o.γ.1.promote b = o'.γ.1.promote b' :=
        Fstar.starOf_injective G ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s)
          (promote_mem_selectedOuterRawOf_raw s o hb) (promote_mem_selectedOuterRawOf_raw s o' hb')
          (hbv.trans hbv'.symm)
      have hbverts : b.vertices = b'.vertices := by
        have := congrArg ResolvedFeynmanSubgraph.vertices hpromEq
        rwa [ResolvedFeynmanSubgraph.promote_vertices,
          ResolvedFeynmanSubgraph.promote_vertices] at this
      obtain ⟨w, hw⟩ : b.vertices.Nonempty := Finset.card_pos.mp
        ((CarrierProper.carrier_isProperForest o.γ.1.toResolvedFeynmanGraph o.B.1 o.B.2).2.1 b hb)
      exact Finset.disjoint_left.mp hParentDisj (b.vertices_subset hw)
        (b'.vertices_subset (hbverts ▸ hw))

/-- **R-6c-body-464 ∎ — the canonical inhabitant of the alpha-native corrected family prototype.** -/
noncomputable def canonicalAlphaNativeCorrectedFamilySupply
    (CarrierProper : ResolvedCarrierProperProvider D) (Fstar : ResolvedCanonicalStarFacts D) :
    ResolvedAlphaNativeCorrectedFamilySupply D G where
  family := fun s => canonicalCorrectedRemnantReembedFamily Fstar s
  remnantDisjoint := fun s o o' hne =>
    correctedRemnantComponent_disjoint s Fstar CarrierProper o o' hne

end GaugeGeometry.QFT.Combinatorial
