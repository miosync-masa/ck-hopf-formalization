import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCanonicalMembershipAdapters
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocComponentNonempty

/-!
# R-6c-body-235 — `IsProperForest` conjunct scout: `HasNonemptyComponents` falls first (generically)

Two-hundred-and-thirty-fifth genuine-body step, a scout of which of the five `IsProperForest` conjuncts can be proved
first for the two constructed forests behind the membership certificates (body-232/233):

```text
(X) selectedOuterRawOf s = (leftOf s).union (promotedOf s) (cross s)          [Promote.lean:61]
(Y) region union = ((leftResidual z).union (rightRecovered z) …).union (forestRecovered z) …   [RecoveredOuterMembership.lean:75]
```

Verdict: **`HasNonemptyComponents` falls first**, and cleanest as a *generic* per-carrier lemma that serves both `X`
and `Y` (and every future construction) with no `mem_union` bookkeeping.  Imports 233 (the certificate route) and the
component-nonempty supply to keep the map honest.

## Correction to the naive premise

`IsConnectedDivergent` does **not** give nonemptiness or positive edges: `IsConnected` is vacuously true on empty
vertices and `IsDivergent` is `0 ≤ divergenceDegree` (`Combinatorial/SubGraph.lean:1321/670`).  Two files record this
verbatim — `ComponentNonempty.lean:9-18` ("`IsConnectedDivergent → vertices.Nonempty` is genuinely NOT provable from
the abstract `DivergenceMeasure`") and `ElementNonempty.lean:9`.  So per-component nonemptiness is a **supplied
measure-level fact**, already isolated as `ResolvedConnectedDivergentNonemptySupply.cd_nonempty`
(`ComponentNonempty.lean:45`: `∀ γ, γ.forget.IsConnectedDivergent → γ.vertices.Nonempty`), wired through
`ResolvedMeasureLeafSupply.componentNonempty` (`NonemptyLeavesIntegration.lean:67`, body-124).  `HasNonemptyComponents`
is discharged from `cd_nonempty` + the universal `isConnectedDivergent` structure field — **not** free from CD alone.

## Honest difficulty ranking (identical for X and Y — both are `union`s)

```text
1 (first)  HasNonemptyComponents            ∀ γ ∈ elements, γ.IsNonempty (= 0 < γ.vertexCount).
           Every element is CD (isConnectedDivergent field, ResolvedSubGraph.lean:136); cd_nonempty
           (ComponentNonempty.lean:45) converts that to vertex-nonemptiness. UNIVERSAL — no piece-specific fact,
           no mem_union work. Discharges X and Y and every construction at once.

2          HasPositiveInternalEdgesComponents  ∀ γ ∈ elements, 0 < γ.internalEdges.card. Same universal SHAPE, but
           there is NO "CD ⇒ 0 < internalEdges.card" supply (grep empty) — needs a NEW measure obligation field.

3          0 < internalEdges.card           internalEdges = elements.sum (ResolvedSubGraph.lean:151); via
           mem_internalEdges (ResolvedCoproductIndex.lean:38), 0 < card ⟸ a witness component (IsNonempty) with a
           positive-edge component (#2). Derivable, NOT independent — depends on #1 + #2.

4          IsNonempty  (elements.Nonempty)   Finset.union_nonempty needs ONE piece nonempty; but leftOf/promotedOf are
           abstract supply fields and leftResidual is a FILTER of z.1.1 (LeftResidualConstruction.lean:78) that can be
           EMPTY. PIECE-SPECIFIC, not yet proved.

5 (hardest) 0 < complementEdges.card        (G.internalEdges - A.internalEdges).card > 0 ⟺ strict A.internalEdges <
           G.internalEdges (properness). Only internalEdges_le (non-strict, ResolvedCoproductIndex.lean:165) exists;
           forget_complementEdges_card_pos (:202) takes IsProperForest as hypothesis (circular). Deepest properness.
```

Already free (per body-230): `IsPairwiseDisjoint` (union field via `cross`) and `selectedOuterRawOf_vertices_subset`
(a ⊆, not a conjunct).  All five `IsProperForest` conjuncts are otherwise open for both constructions.

## Assessment and plan

* **First target (body-236): `HasNonemptyComponents`, proved GENERICALLY.**  A per-carrier lemma
  `hasNonemptyComponents_of_cdNonempty (N : ResolvedConnectedDivergentNonemptySupply G) (A : ResolvedAdmissibleSubgraph G)
  : A.HasNonemptyComponents := fun γ hγ => …(IsNonempty from N.cd_nonempty γ (A.isConnectedDivergent γ hγ))…`, using
  `ResolvedFeynmanSubgraph.IsNonempty` / `vertexCount` (`ResolvedSubGraph.lean:85/82`) + `Finset.card_pos`.  Applies
  directly to `X` and `Y` (each is a `ResolvedAdmissibleSubgraph`), and to every future construction — no `union`
  lemma needed.  A per-piece `union_hasNonemptyComponents` (mem_union split) is a strictly weaker alternative.
* **Do not target `IsNonempty` or `complementEdges` first** — both need piece-specific facts that are unproved
  (`leftResidual` can be empty; strict properness of the union is the deepest obligation).
* **`HasPositiveInternalEdgesComponents` is next** but blocked on a missing "CD ⇒ positive-edge" measure supply — a
  small new leaf, sequenced after the generic nonempty-components lemma.

Per the HALT: no conjunct body is entered, no certificate field is proved; the exact first target, its generic form,
and the exact supplies/obstructions per conjunct are named.  This is a documentation / scout anchor (like body-230).
No declarations beyond this docstring.  No facade, no flat term, no `forgetHopf`.
-/
