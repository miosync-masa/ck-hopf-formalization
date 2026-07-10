import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocHasNonemptyComponents

/-!
# R-6c-body-237 — positive-internal-edges scout: `HasPositiveInternalEdgesComponents` needs a NEW measure leaf (cd_nonempty sibling)

Two-hundred-and-thirty-seventh genuine-body step, a scout of the second `IsProperForest` conjunct
`HasPositiveInternalEdgesComponents A = ∀ γ ∈ A.elements, 0 < γ.internalEdges.card`
(`ResolvedSubGraph.lean:631`) for the constructed forests behind the membership certificates.  Verdict: **it needs a
new measure-level supply**, an exact clone of `cd_nonempty` (body-1/236) — `IsConnectedDivergent` does not force a
positive internal-edge count.  Records the exact supply type, the generic lemma shape, and the corrected dependency of
conjunct #3.  Imports body-236 to keep the map honest.

## Why `IsConnectedDivergent` does not give it (definitive)

`IsConnectedDivergent γ = γ.IsConnected ∧ γ.IsOnePI ∧ γ.IsDivergent` (`SubGraph.lean:1358`), and none of the three
constrains the edge count:

```text
IsOnePI G = G.IsSupportConnected ∧ ∀ e ∈ G.internalEdges, ¬ G.IsBridge e    (SupportGraph.lean:210)
  — the bridge clause is a ∀ over internalEdges: VACUOUSLY TRUE when internalEdges = ∅.
    A graph with 0 internal edges (isolated vertex) is 1PI (support-connected, no edges ⇒ no bridges).
IsSupportConnected — vacuous on empty vertices.
IsDivergent = 0 ≤ divergenceDegree, divergenceDegree = DivergenceMeasure.degree γ (SubGraph.lean:1314)
  — an ARBITRARY Int of the abstract typeclass; no formula, no edge/loop content.
```

So `0 < γ.internalEdges.card` is genuinely NOT derivable — exactly the `cd_nonempty` situation
(`ComponentNonempty.lean:9-14`).  The only existing positive-edge machinery is a **hand-imposed filter conjunct**, not
a theorem: `properConnectedDivergentSubgraphs` filters on `0 < γ.internalEdges.card` (`Coproduct.lean:113`), with the
docstring calling it "the physical requirement (divergent 1PI subgraphs with no internal lines are excluded)"; its
projection `properConnectedDivergentSubgraphs_internalEdges_pos` (`:136`) only reads it back out.  No resolved-level
positive-edges sibling of `cd_nonempty` exists anywhere.

## The new supply and generic lemma (body-238 target)

`γ.internalEdges : Multiset ResolvedFeynmanEdge` (`ResolvedSubGraph.lean:27-35`), so `γ.internalEdges.card` is
`Multiset.card` — the field type typechecks.  The supply and lemma are a verbatim clone of body-236:

```lean
structure ResolvedConnectedDivergentPositiveInternalEdgesSupply (G : ResolvedFeynmanGraph) where
  cd_positiveInternalEdges : ∀ (γ : ResolvedFeynmanSubgraph G),
    γ.forget.IsConnectedDivergent → 0 < γ.internalEdges.card

theorem hasPositiveInternalEdgesComponents_of_cdPositive
    (P : ResolvedConnectedDivergentPositiveInternalEdgesSupply G) (A : ResolvedAdmissibleSubgraph G) :
    A.HasPositiveInternalEdgesComponents :=
  fun γ hγ => P.cd_positiveInternalEdges γ (A.isConnectedDivergent γ hγ)
```

The types line up exactly: `A.isConnectedDivergent γ hγ : γ.forget.IsConnectedDivergent` (`ResolvedSubGraph.lean:138`)
is precisely the field hypothesis — mirroring `toInputOuterElementNonemptySupply` (`ComponentNonempty.lean:53`).

## Corrected dependency for conjunct #3

`0 < A.internalEdges.card` (the AGGREGATE `Multiset`, `ResolvedSubGraph.lean:151`) needs a *witness component*: via
`mem_internalEdges` (`ResolvedCoproductIndex.lean:38`, `e ∈ A.internalEdges ↔ ∃ γ ∈ elements, e ∈ γ.internalEdges`),
`0 < A.internalEdges.card` follows from some `γ₀ ∈ A.elements` (= `A.IsNonempty`, conjunct #4) with
`0 < γ₀.internalEdges.card` (#2) via `Multiset.card_pos`.  So **#3 depends on #4 (`IsNonempty`) and #2**, NOT on #1
(`HasNonemptyComponents`, which gives vertex-nonemptiness, no edge and no existential witness).  Conjunct order is
therefore: #1 (done, 236) → #2 (new leaf, 238) → #4 (`IsNonempty`, piece-specific) → #3 (from #4 + #2) → #5
(`complementEdges`, hardest).

## Assessment and plan

* **body-238 target**: land `ResolvedConnectedDivergentPositiveInternalEdgesSupply` + the generic
  `hasPositiveInternalEdgesComponents_of_cdPositive` — a one-line clone of body-236, discharging conjunct #2 for `X`,
  `Y`, and every construction.  The `cd_positiveInternalEdges` field is the honest measure-level obligation (sibling of
  `cd_nonempty`), not provable from `IsOnePI`.
* **#3 sequenced after #4** — it needs the `IsNonempty` witness, so the piece-specific `IsNonempty` must land first.

Per the HALT: no lemma body is entered, no measure leaf is proved; the exact new supply type, the generic lemma shape,
and the corrected #3 dependency are named.  This is a documentation / scout anchor (like body-235).  No declarations
beyond this docstring.  No facade, no flat term, no `forgetHopf`.
-/
