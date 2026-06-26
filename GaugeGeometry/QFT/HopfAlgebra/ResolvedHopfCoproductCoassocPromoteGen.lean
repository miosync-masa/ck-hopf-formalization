import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocLeftPartition

/-!
# R-6c-heart-5c-1d — the promote-gen equality (forest region engine)

The forest region of `leftFactorProduct` is `∏ γ ∈ forestComponents, leftTerm Bγ`; to identify it with
`resolvedForestLeftTerm (promotedOf s)` the key fact is that **promote preserves the component
generator**: since the resolved promote keeps the intrinsic graph (`(γ.promote δ).toResolvedFeynmanGraph
= δ.toResolvedFeynmanGraph`, both `⟨δ.vertices, δ.internalEdges, δ.externalLegs⟩`), the generators
agree.

Landed:

* `resolvedComponentGen_promote` — `resolvedComponentGen (γ.promote δ) = resolvedComponentGen δ` (`rfl`);
* `resolvedComponentGenTerm_of_cd` — `resolvedComponentGenTerm δ = X (componentGen δ)` when CD holds;
* `ResolvedFeynmanSubgraph.promote_injective` — promote is injective (keeps the data);
* `resolvedForestLeftTerm_promote` — `resolvedForestLeftTerm (promote γ B) = resolvedForestLeftTerm B`;
* `leftFactorOf_eq_promote_of_forestChoice` — a forest-choice component's left factor is
  `resolvedForestLeftTerm (promote γ B)`.

No facade, no flat term, no `forgetHopf`, no rep/perm.  The global forest region (`forestPart =
resolvedForestLeftTerm promotedOf` via the `promotedElements` biUnion) and `right_eq` remain.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-5c-1d — promote preserves the component generator.**  The promote keeps the intrinsic
graph (`(γ.promote δ).toResolvedFeynmanGraph = δ.toResolvedFeynmanGraph`), so the resolved generators —
the graph's resolved class (CD proof irrelevant) — agree. -/
theorem resolvedComponentGen_promote (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph γ.toResolvedFeynmanGraph)
    (hCD : (γ.promote δ).forget.IsConnectedDivergent) (hCD' : δ.forget.IsConnectedDivergent) :
    resolvedComponentGen (γ.promote δ) hCD = resolvedComponentGen δ hCD' := rfl

/-- The proof-free generator term reduces to `X (componentGen δ)` when `δ` is connected-divergent. -/
theorem resolvedComponentGenTerm_of_cd {δ : ResolvedFeynmanSubgraph G}
    (h : δ.forget.IsConnectedDivergent) :
    resolvedComponentGenTerm δ = MvPolynomial.X (resolvedComponentGen δ h) := by
  rw [resolvedComponentGenTerm, dif_pos h]

/-- **R-6c-heart-5c-1d — promote is injective.**  It keeps the subgraph data (vertices/edges/legs), so
distinct sources give distinct promotes. -/
theorem ResolvedFeynmanSubgraph.promote_injective (γ : ResolvedFeynmanSubgraph G) :
    Function.Injective γ.promote := by
  intro δ₁ δ₂ h
  have hv := congrArg ResolvedFeynmanSubgraph.vertices h
  have he := congrArg ResolvedFeynmanSubgraph.internalEdges h
  have hl := congrArg ResolvedFeynmanSubgraph.externalLegs h
  rw [ResolvedFeynmanSubgraph.promote_vertices, ResolvedFeynmanSubgraph.promote_vertices] at hv
  rw [ResolvedFeynmanSubgraph.promote_internalEdges, ResolvedFeynmanSubgraph.promote_internalEdges] at he
  rw [ResolvedFeynmanSubgraph.promote_externalLegs, ResolvedFeynmanSubgraph.promote_externalLegs] at hl
  cases δ₁; cases δ₂; cases hv; cases he; cases hl; rfl

/-- **R-6c-heart-5c-1d — the forest left term is promote-invariant.**  `resolvedForestLeftTerm (promote γ
B) = resolvedForestLeftTerm B` — the promoted forest has the same component generators. -/
theorem resolvedForestLeftTerm_promote (γ : ResolvedFeynmanSubgraph G)
    (B : ResolvedAdmissibleSubgraph γ.toResolvedFeynmanGraph) :
    resolvedForestLeftTerm (ResolvedAdmissibleSubgraph.promote γ B) = resolvedForestLeftTerm B := by
  letI : DecidableEq (ResolvedFeynmanSubgraph G) := Classical.decEq _
  rw [resolvedForestLeftTerm_eq_prod, resolvedForestLeftTerm_eq_prod,
    ResolvedAdmissibleSubgraph.promote_elements,
    Finset.prod_image (fun δ₁ _ δ₂ _ h => γ.promote_injective h)]
  apply Finset.prod_congr rfl
  intro δ hδ
  have h2 : δ.forget.IsConnectedDivergent := B.isConnectedDivergent δ hδ
  have h1 : (γ.promote δ).forget.IsConnectedDivergent := γ.promote_forget_isConnectedDivergent δ h2
  rw [resolvedComponentGenTerm_of_cd h1, resolvedComponentGenTerm_of_cd h2]
  rfl

/-- **R-6c-heart-5c-1d — a forest-choice component's left factor is the promoted forest term.**  For a
component whose choice is `Sum.inr B`, the local left factor `leftTerm B` equals `resolvedForestLeftTerm
(promote γ B)` (the promoted components of `G`). -/
theorem leftFactorOf_eq_promote_of_forestChoice
    {s : ResolvedCoassocSplitChoice D G} {γ : {x : ResolvedFeynmanSubgraph G // x ∈ s.1.1.elements}}
    {B : (D.supply γ.1.toResolvedFeynmanGraph).ForestIdx} (hc : s.choiceAt γ = Sum.inr B) :
    D.leftFactorOf s γ = resolvedForestLeftTerm (ResolvedAdmissibleSubgraph.promote γ.1 B.1) := by
  rw [resolvedForestLeftTerm_promote]
  unfold ResolvedCoproductProperForestData.leftFactorOf
    ResolvedCoproductProperForestData.localChoiceLeftFactor
  rw [hc]
  rfl

end GaugeGeometry.QFT.Combinatorial
