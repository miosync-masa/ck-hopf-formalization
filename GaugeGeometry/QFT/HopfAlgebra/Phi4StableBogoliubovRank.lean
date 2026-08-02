import GaugeGeometry.QFT.HopfAlgebra.Phi4RotaBaxterSubtraction

/-!
# body-661a (QFT-R2) — the stable generator RANK and the load-bearing strict descent

**661a extracts WHY CK recursion terminates from the stable W‴ carrier type: the generator
RANK (a class-well-defined internal-edge count) and the load-bearing fact that every W‴ forest
COMPONENT generator has strictly smaller rank than the ambient — the fifth axis
(edge-completeness) is the recursion-term CLOSURE, `IsProperForest`'s POSITIVE COMPLEMENT
(`0 < complementEdges.card`) is the WELL-FOUNDEDNESS.  The `WellFounded.fix` recursion + Bogoliubov
preparation / counterterm / renormalized unfolding is 661b.**

This is an honest SPLIT of body-661 (`661a = stable rank owner + W‴ component strict decrease`,
`661b = WellFounded.fix + preparation / counterterm / renormalized unfolding`).  NO Bogoliubov
recursion, NO preparation step, NO counterterm character `φ₋`, NO `WellFounded.fix`, NO antipode
here — ONLY the rank owner and the descent that makes the recursion well-founded.

## Contents
* `stablePhi4GeneratorRank : StableResolvedPhi4HopfGen → ℕ` — the internal-edge cardinality of the
  class, defined by `Quotient.liftOn` on the underlying `ResolvedFeynmanGraphClass`; it is therefore
  ALREADY representative- and `mapPerm`-well-defined BY CONSTRUCTION (the `liftOn` invariance obligation
  is discharged from `mapPerm`-invariance of the internal-edge cardinality).
* `stablePhi4GeneratorRank_toStableGen` — the load-bearing anchor
  `rank (X_G) = G.internalEdges.card`.
* `stableForestComponent_rank_lt` — the HEADLINE: a live W‴ carrier forest component's stable
  generator has strictly smaller rank than the ambient generator.

## Ownership separation (stated for the record)
The W‴ **fifth axis (edge-completeness / `ResolvedForestInternalEdgeComplete`) is NOT used for
termination** — it is the recursion-term CLOSURE.  What carries well-foundedness is
`IsProperForest`'s POSITIVE COMPLEMENT conjunct `0 < A.complementEdges.card`
(`complementEdges_card_pos_of_isProperForest`): the ambient graph has at least one internal edge
lying OUTSIDE the forest, so the aggregate forest internal-edge count is strictly below the
ambient's, which drops every component strictly below the ambient in rank.

## Roadmap
661a rank + descent (THIS FILE) → 661b `WellFounded.fix` recursion + Bogoliubov
preparation / counterterm / renormalized unfolding → 662 `aeval` `φ₋` / `φ₊` characters →
663 `φ₋ ⋆ φ = φ₊` → 664 Figure-1 dropped-term → renormalization weight + HALT.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped BigOperators

set_option linter.unusedVariables false

/-- File-scoped re-exposure of the φ⁴ divergence-measure family instance (NOT a permanent/global
instance — scoped to this file exactly as in `Phi4StableCounit` / `Phi4StableResolvedHopfCoproduct`),
so the W‴ carrier types in the forest-component statements elaborate. -/
local instance instPhi4DivergenceMeasureFamily661a : ∀ H : FeynmanGraph, DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

/-! ## Step 1 — the stable generator rank (class-well-defined internal-edge count) -/

/-- **body-661a (Step 1) — the stable generator RANK.**  The internal-edge cardinality of the
underlying id-preserving isomorphism class, taken by `Quotient.liftOn` on `x.val`.  It is
MANIFESTLY well-defined: the `liftOn` invariance obligation is discharged from the fact that
`mapPerm` maps internal edges bijectively (`ResolvedFeynmanEdge.map π` under `Multiset.map`), so the
cardinality is `mapPerm`-invariant — no representative choice enters.  This is the well-founded rank
for the CK recursion of 661b. -/
noncomputable def stablePhi4GeneratorRank (x : StableResolvedPhi4HopfGen) : ℕ :=
  Quotient.liftOn x.val (fun G => G.internalEdges.card) (by
    intro a b h
    obtain ⟨π, rfl⟩ := h
    show a.internalEdges.card = (a.internalEdges.map (ResolvedFeynmanEdge.map π)).card
    rw [Multiset.card_map])

/-- **body-661a (Step 1, LOAD-BEARING ANCHOR) — `rank (X_G) = G.internalEdges.card`.**  Reduces
definitionally: `(G.toStableResolvedPhi4HopfGen …).val = G.toResolvedClass = ⟦G⟧` and `liftOn ⟦G⟧`
computes to the internal-edge cardinality. -/
theorem stablePhi4GeneratorRank_toStableGen (G : ResolvedFeynmanGraph)
    (hCD : ∃ hWF : G.forget.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent G.forget (phi4DivergenceMeasureFamily G.forget)
        (FeynmanSubgraph.self G.forget hWF))
    (hSt : StableResolvedBoundaryIds G) :
    stablePhi4GeneratorRank (G.toStableResolvedPhi4HopfGen hCD hSt) = G.internalEdges.card := rfl

/-- **body-661a (Step 1, corollary) — the rank is `mapPerm`-invariant.**  Immediate from the
class-level definition (`⟦G.mapPerm σ⟧ = ⟦G⟧`).  Recorded for completeness; the definition is
already well-defined without it. -/
theorem stablePhi4GeneratorRank_toStableGen_mapPerm (G : ResolvedFeynmanGraph)
    (σ : Equiv.Perm VertexId)
    (hCD : ∃ hWF : G.forget.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent G.forget (phi4DivergenceMeasureFamily G.forget)
        (FeynmanSubgraph.self G.forget hWF))
    (hSt : StableResolvedBoundaryIds G)
    (hCDσ : ∃ hWF : (G.mapPerm σ).forget.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent (G.mapPerm σ).forget
        (phi4DivergenceMeasureFamily (G.mapPerm σ).forget)
        (FeynmanSubgraph.self (G.mapPerm σ).forget hWF))
    (hStσ : StableResolvedBoundaryIds (G.mapPerm σ)) :
    stablePhi4GeneratorRank ((G.mapPerm σ).toStableResolvedPhi4HopfGen hCDσ hStσ)
      = stablePhi4GeneratorRank (G.toStableResolvedPhi4HopfGen hCD hSt) := by
  rw [stablePhi4GeneratorRank_toStableGen, stablePhi4GeneratorRank_toStableGen,
    ResolvedFeynmanGraph.mapPerm, Multiset.card_map]

/-- **body-661a (Step 2, helper) — the aggregate forest internal edges are bounded by the ambient
graph's.**  Reconstructed inline (from ONLY the subgraph structure fields `pairwiseDisjoint` /
`edges_supported` / component-level `internalEdges_le`) so the statement stays free of the ambient
divergence-invariance typeclasses that the library aggregate `internalEdges_le` carries.
Vertex-disjoint components share no internal edge, so the componentwise `count` sum collapses to a
single component's, bounded by the ambient count. -/
theorem forestInternalEdges_le {G : ResolvedFeynmanGraph} (F : ResolvedAdmissibleSubgraph G) :
    F.internalEdges ≤ G.internalEdges := by
  classical
  rw [Multiset.le_iff_count]
  intro e
  show Multiset.count e (∑ γ ∈ F.elements, γ.internalEdges) ≤ Multiset.count e G.internalEdges
  rw [Multiset.count_sum']
  by_cases heF : ∃ γ ∈ F.elements, e ∈ γ.internalEdges
  · obtain ⟨γ, hγ, heγ⟩ := heF
    have hzero : ∀ δ ∈ F.elements, δ ≠ γ → Multiset.count e δ.internalEdges = 0 := by
      intro δ hδ hne
      by_cases heδ : e ∈ δ.internalEdges
      · have hdisj : _root_.Disjoint δ.vertices γ.vertices := F.pairwiseDisjoint hδ hγ hne
        obtain ⟨hsδ, _⟩ := δ.edges_supported e heδ
        obtain ⟨hsγ, _⟩ := γ.edges_supported e heγ
        exact absurd hsγ (Finset.disjoint_left.mp hdisj hsδ)
      · exact Multiset.count_eq_zero.mpr heδ
    calc (∑ x ∈ F.elements, Multiset.count e x.internalEdges)
        = Multiset.count e γ.internalEdges :=
          Finset.sum_eq_single γ (fun δ hδ hne => hzero δ hδ hne) (fun hγnot => absurd hγ hγnot)
      _ ≤ Multiset.count e G.internalEdges := Multiset.count_le_of_le e γ.internalEdges_le
  · have hz : (∑ x ∈ F.elements, Multiset.count e x.internalEdges) = 0 :=
      Finset.sum_eq_zero (fun δ hδ =>
        Multiset.count_eq_zero.mpr (fun hmem => heF ⟨δ, hδ, hmem⟩))
    rw [hz]; exact Nat.zero_le _

/-! ## Step 2 — the load-bearing strict decrease (HEADLINE) -/

/-- **body-661a (Step 2, HEADLINE) — every W‴ forest COMPONENT generator has strictly smaller rank
than the ambient generator.**

For a live W‴ carrier member forest `F` of an ambient stable generator (carrying `G`'s CD +
stable certificates) and a component `γ ∈ F.elements`, the component's stable generator
(inherited-verbatim local boundary completion, exactly the `stableLeftAggregate` component
generator of body-629) has strictly smaller rank than `G`'s stable generator.

**This is the well-foundedness of the CK recursion of 661b.**  The chain is
`rank (component) = γ.internalEdges.card ≤ F.internalEdges.card < G.internalEdges.card = rank (G)`:

1. `single_le_sum`: `γ.internalEdges ≤ F.internalEdges` (`γ ∈ F.elements`, `F.internalEdges` is the
   componentwise sum), hence `γ.internalEdges.card ≤ F.internalEdges.card` (`card_le_card`);
2. `add_tsub_cancel_of_le` on `F.internalEdges ≤ G.internalEdges` (`internalEdges_le`) gives
   `F.internalEdges + F.complementEdges = G.internalEdges`, so
   `F.internalEdges.card + F.complementEdges.card = G.internalEdges.card` (`card_add`);
3. `0 < F.complementEdges.card` (`complementEdges_card_pos_of_isProperForest`, the POSITIVE
   COMPLEMENT conjunct of `IsProperForest`) closes it by `omega`.

**Ownership separation:** the W‴ fifth axis (edge-completeness) is the recursion-term CLOSURE and is
NOT consumed here; `IsProperForest`'s POSITIVE COMPLEMENT is the WELL-FOUNDEDNESS. -/
theorem stableForestComponent_rank_lt (G : ResolvedFeynmanGraph)
    (hCD : ∃ hWF : G.forget.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent G.forget (phi4DivergenceMeasureFamily G.forget)
        (FeynmanSubgraph.self G.forget hWF))
    (hSt : StableResolvedBoundaryIds G)
    (F : ResolvedAdmissibleSubgraph G) (hF : F ∈ phi4WTriplePrimeIndex G)
    (γ : ResolvedFeynmanSubgraph G) (hγ : γ ∈ F.elements) :
    stablePhi4GeneratorRank ((stableLocalBoundaryCompletedGraph γ).toStableResolvedPhi4HopfGen
        (stableLocalBoundaryCompletedGraph_exists_self_isConnectedDivergent γ
          (F.isConnectedDivergent γ hγ))
        (stableResolvedBoundaryIds_stableLocalBoundaryCompletedGraph γ hSt))
      < stablePhi4GeneratorRank (G.toStableResolvedPhi4HopfGen hCD hSt) := by
  rw [stablePhi4GeneratorRank_toStableGen, stablePhi4GeneratorRank_toStableGen,
    stableLocalBoundaryCompletedGraph_internalEdges]
  -- goal : γ.internalEdges.card < G.internalEdges.card
  have hle1 : γ.internalEdges ≤ F.internalEdges :=
    Finset.single_le_sum (fun i _ => Multiset.zero_le _) hγ
  have hle2 : γ.internalEdges.card ≤ F.internalEdges.card := Multiset.card_le_card hle1
  have hsum : F.internalEdges + F.complementEdges = G.internalEdges :=
    add_tsub_cancel_of_le (forestInternalEdges_le F)
  have hcard : F.internalEdges.card + F.complementEdges.card = G.internalEdges.card := by
    rw [← Multiset.card_add, hsum]
  have hpos : 0 < F.complementEdges.card :=
    ResolvedAdmissibleSubgraph.complementEdges_card_pos_of_isProperForest
      (((mem_phi4WTriplePrimeIndex G F).mp hF).2.2.2.2.1)
  omega

end GaugeGeometry.QFT.Combinatorial
