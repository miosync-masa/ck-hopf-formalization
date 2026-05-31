/-
  Main.lean
  Headline theorems.

  `geometric_main` is now pure geometry: Platonic integer set, uniqueness
  of the (60,30,8) floor inside the candidate space, and the
  adjoint-dimension characterization of `N = 3`. The algebraic
  unification identity and its evaluation on (60,30,8) vs (15,8,3) have
  moved to `Applications.UnificationRatio` and appear in a separate
  headline theorem below.
-/
import GaugeGeometry.Geometric.Platonic.IntegerSet
import GaugeGeometry.Geometric.Arithmetic.FloorValues
import GaugeGeometry.Geometric.GroupDimension.ColorEmergence
import GaugeGeometry.Applications.AlphaSPrediction
import GaugeGeometry.Applications.QuarkConsistency
import GaugeGeometry.Applications.UnificationRatio

namespace GaugeGeometry

theorem geometric_main :
    Geometric.Platonic.schlafliCoordinateSet = Geometric.Platonic.platonicIntegers ∧
      (∃! α : Geometric.Arithmetic.FloorCandidate,
        α ∈ Geometric.Arithmetic.candidateSpace ∧ α = Geometric.Arithmetic.floorTarget) ∧
      (3 ∈ Geometric.Platonic.platonicIntegers ∧
        Geometric.GroupDimension.adjointDim 3 = 8 ∧
        ∀ {N : ℕ}, 2 ≤ N → Geometric.GroupDimension.adjointDim N = 8 → N = 3) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Geometric.Platonic.platonic_integers_from_classification
  · exact Geometric.Arithmetic.unique_floor_structure
  · exact Geometric.GroupDimension.three_is_consistent

/--
  Physical separation between algebraic one-point unification and the
  empirical floor `(60, 30, 8)`:

  * `(60, 30, 8)` fails the idealized algebraic unification identity,
  * `(15, 8, 3)` satisfies it but is physically rejected.

  This lives outside `geometric_main` because it mixes algebraic
  (Applications) content with the geometric candidate space.
-/
theorem unification_physical_separation :
    ¬ Applications.unificationConsistency Applications.floorTargetZ ∧
      (∃ α ∈ Geometric.Arithmetic.candidateSpace,
        Applications.unificationConsistency (fun i => (α i : ℤ)) ∧
          α = Applications.nontrivialSolution) := by
  refine ⟨?_, ?_⟩
  · exact Applications.target_not_unification_consistent
  · exact Applications.nontrivial_unification_solution

/--
  Physical-consistency headline theorem.

  Two closures are bundled into one statement:

  * `ℚ`-side structural closure: for every nonzero rational baseline
    `k`, the canonical weak/color generation witness recovers the
    geometric integer `3` through the ratio of ratios, agreeing with
    `adjointDim 3 - 5`;
  * `ℝ`-side PDG-conditional closure: under the hypothesis that the
    PDG generation factor satisfies the real channel-factorization
    pattern for `N_c = 3` with nonzero second-generation entry, the
    real ratio of ratios equals `3`.

  No axiom beyond the already-registered `Axioms.pdgObservationData`
  is introduced. The PDG empirical-matching hypothesis is carried as
  an argument rather than asserted.
-/
theorem physical_consistency
    (hFact : Applications.ChannelFactorizationHoldsReal
               Applications.pdgGenerationFactor 3)
    (hNonzero : Applications.pdgGenerationFactor 1 ≠ 0) :
    (∀ k : ℚ, k ≠ 0 →
        (Applications.ratioOfRatios
            (Applications.generationFactorFromSectorWeights
              (Applications.canonicalWeakUniformColorScaled k (3 : ℚ))) : ℚ)
          = (Geometric.GroupDimension.adjointDim 3 - 5 : ℕ)) ∧
      Applications.ratioOfRatiosReal Applications.pdgGenerationFactor = 3 := by
  refine ⟨?_, ?_⟩
  · intro k hk
    exact Applications.geometric_physical_consistency_canonical k hk
  · exact Applications.pdg_channel_factorization_implies_three hFact hNonzero

#print axioms geometric_main
#print axioms unification_physical_separation
#print axioms physical_consistency

end GaugeGeometry
