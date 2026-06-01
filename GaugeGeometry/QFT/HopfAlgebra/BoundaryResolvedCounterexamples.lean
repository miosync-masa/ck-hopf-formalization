import GaugeGeometry.QFT.HopfAlgebra.BoundaryResolved

/-!
# Mechanism-level negative results for the flat boundary semantics

These are **formal, mechanism-level counterexamples**.  They do *not* prove the
negation of the flat facade classes directly (`ForestGraphInsertionUniquenessModel`,
`…PromotedExternalLegsLiftableModel`) — those are large proof-skeleton interfaces.
Instead they formalize the *exact retargeting collapse* that those facades would
have to rule out: the flat edge/leg retarget maps are genuinely non-injective,
even on singleton multisets.

In contrast, `BoundaryResolved.lean` proves the corresponding **boundary-resolved**
retarget maps are injective *before forgetting* (`BoundaryResolvedSemanticModel`),
and that forgetting boundary identities projects those resolved maps exactly onto
the flat retarget maps used here (`forget_retarget_edge` / `forget_retarget_leg`,
`map_forget_retarget_edges` / `_legs`).  So the resolved positive results are
formally wired to these flat failures — not cherry-picked analogues.

The witnessing vertex map collapses two distinct vertices to one
(`fun _ => 0`); the two source graphs differ only at that endpoint, so they are
distinct yet have identical images.  `VertexId = Nat`, so the witnesses are
concrete (no extra hypotheses needed).
-/

namespace GaugeGeometry.QFT.HopfAlgebra

open GaugeGeometry.QFT.Combinatorial

/-- **Edge retarget collapse.**  The flat edge-retarget map is not injective: two
edges differing only in a source endpoint that the vertex map identifies become
equal after retargeting. -/
theorem flatEdgeRetarget_not_injective :
    ∃ (f : VertexId → VertexId) (e₁ e₂ : FeynmanEdge),
      e₁ ≠ e₂ ∧ flatEdgeRetarget f e₁ = flatEdgeRetarget f e₂ :=
  ⟨fun _ => 0,
   (⟨0, 2, .hypercharge⟩ : FeynmanEdge),
   (⟨1, 2, .hypercharge⟩ : FeynmanEdge),
   by decide, by decide⟩

/-- **Leg retarget collapse.**  The flat leg-retarget map is not injective: two
legs differing only in an attachment vertex that the vertex map identifies become
equal after retargeting. -/
theorem flatLegRetarget_not_injective :
    ∃ (f : VertexId → VertexId) (ℓ₁ ℓ₂ : ExternalLeg),
      ℓ₁ ≠ ℓ₂ ∧ flatLegRetarget f ℓ₁ = flatLegRetarget f ℓ₂ :=
  ⟨fun _ => 0,
   (⟨0, .hypercharge⟩ : ExternalLeg),
   (⟨1, .hypercharge⟩ : ExternalLeg),
   by decide, by decide⟩

/-- **Edge retarget collapse, multiset level.**  Distinct singleton edge
multisets have equal images under `Multiset.map (flatEdgeRetarget f)`.  This is
the form that lines up with `BoundaryResolvedSemanticModel`'s submultiset
injectivity field. -/
theorem flatEdgeRetarget_multiset_collapse :
    ∃ (f : VertexId → VertexId) (M₁ M₂ : Multiset FeynmanEdge),
      M₁ ≠ M₂ ∧ M₁.map (flatEdgeRetarget f) = M₂.map (flatEdgeRetarget f) :=
  ⟨fun _ => 0,
   {(⟨0, 2, .hypercharge⟩ : FeynmanEdge)},
   {(⟨1, 2, .hypercharge⟩ : FeynmanEdge)},
   by decide, by decide⟩

/-- **Leg retarget collapse, multiset level.**  Distinct singleton leg multisets
have equal images under `Multiset.map (flatLegRetarget f)`. -/
theorem flatLegRetarget_multiset_collapse :
    ∃ (f : VertexId → VertexId) (M₁ M₂ : Multiset ExternalLeg),
      M₁ ≠ M₂ ∧ M₁.map (flatLegRetarget f) = M₂.map (flatLegRetarget f) :=
  ⟨fun _ => 0,
   {(⟨0, .hypercharge⟩ : ExternalLeg)},
   {(⟨1, .hypercharge⟩ : ExternalLeg)},
   by decide, by decide⟩

end GaugeGeometry.QFT.HopfAlgebra
