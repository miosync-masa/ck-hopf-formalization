import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocProdSum

/-!
# R-6c-3a-2 — the per-component coproduct decomposition (`hdecomp`)

The product-of-sums core (R-6c-3a-1) needs each component coproduct `gen(componentGen γ)` written as a
single finite sum `∑ b ∈ t γ, f γ b`.  This file supplies that decomposition at the **concrete
component graph** level (no quotient representative pain: a component generator's class is the
component-as-graph's class, `resolvedComponentGen γ = γ.toResolvedFeynmanGraph.toResolvedHopfGen …`).

For a resolved generator coming from a concrete graph `γG`, the generator coproduct is

  `gen (γG.toResolvedHopfGen hCD) = (X · ⊗ 1) + (1 ⊗ X ·) + ∑ B ∈ forestCarrier, leftTerm B ⊗ rightTerm B`,

so the local choice carrier is `Bool ⊕ (D.supply γG).ForestIdx` (the two primitive legs ⊔ the graph's
own proper forests), via `Finset.disjSum`.

Landed:

* `ResolvedCoproductProperForestData.localChoiceCarrier` / `localChoiceTerm` — the per-graph choice
  carrier and term;
* `ResolvedCoproductProperForestData.gen_eq_localChoiceSum` — the decomposition `gen
  (γG.toResolvedHopfGen hCD) = ∑ b ∈ localChoiceCarrier γG, localChoiceTerm γG hCD b`, ready to feed
  `hdecomp` of R-6c-3a-1.

No facade, no flat term, no `forgetHopf`; the all-primitive/nontrivial split and σ-cover are deferred.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable (D : ResolvedCoproductProperForestData)

/-- The local choice carrier for a concrete graph `γG`: the two primitive legs (`Bool`) disjointly
united with the graph's own proper-forest carrier. -/
noncomputable def ResolvedCoproductProperForestData.localChoiceCarrier (γG : ResolvedFeynmanGraph) :
    Finset (Bool ⊕ (D.supply γG).ForestIdx) :=
  (Finset.univ : Finset Bool).disjSum (D.supply γG).forestCarrier

/-- The local choice term: the two primitive legs `X · ⊗ 1` / `1 ⊗ X ·`, and per proper forest `B`
the forest summand `leftTerm B ⊗ rightTerm B`. -/
noncomputable def ResolvedCoproductProperForestData.localChoiceTerm (γG : ResolvedFeynmanGraph)
    (hCD : γG.forget.toClass.IsConnectedDivergent) :
    (Bool ⊕ (D.supply γG).ForestIdx) → ResolvedHopfH ⊗[ℚ] ResolvedHopfH :=
  Sum.elim
    (fun b => bif b then MvPolynomial.X (γG.toResolvedHopfGen hCD) ⊗ₜ[ℚ] (1 : ResolvedHopfH)
      else (1 : ResolvedHopfH) ⊗ₜ[ℚ] MvPolynomial.X (γG.toResolvedHopfGen hCD))
    (fun B => (D.supply γG).leftTerm B ⊗ₜ[ℚ] (D.supply γG).rightTerm B)

/-- **R-6c-3a-2 — the per-component (per-graph) coproduct decomposition.**  The generator coproduct of
a concrete graph is the finite sum of its two primitive legs plus its proper-forest summands — exactly
the `hdecomp` shape required by R-6c-3a-1. -/
theorem ResolvedCoproductProperForestData.gen_eq_localChoiceSum (γG : ResolvedFeynmanGraph)
    (hCD : γG.forget.toClass.IsConnectedDivergent) :
    D.toGenSupply.gen (γG.toResolvedHopfGen hCD)
      = ∑ b ∈ D.localChoiceCarrier γG, D.localChoiceTerm γG hCD b := by
  unfold ResolvedCoproductProperForestData.localChoiceCarrier
    ResolvedCoproductProperForestData.localChoiceTerm
  rw [Finset.sum_disjSum]
  simp only [Sum.elim_inl, Sum.elim_inr, Fintype.sum_bool, cond_true, cond_false]
  simp only [ResolvedCoproductGenSupply.gen, ResolvedFeynmanGraph.toResolvedHopfGen_val,
    ResolvedCoproductGenSupply.forestSum_mk, ResolvedCoproductProperForestData.toGenSupply,
    ResolvedCoproductForestSummandSupply.sum, resolvedCoproductGenPrimitive]

end GaugeGeometry.QFT.Combinatorial
