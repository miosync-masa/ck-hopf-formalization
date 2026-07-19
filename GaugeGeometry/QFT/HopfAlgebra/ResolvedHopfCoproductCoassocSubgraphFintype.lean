import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocComponentFreshStar

/-!
# R-6c-body-415 — the finiteness floor: `Fintype (ResolvedFeynmanSubgraph G)` IS constructible (PROVED)

Four-hundred-and-fifteenth genuine-body step — the finiteness-floor audit, with a decisive verdict.  The project's
long-standing design note (`ResolvedCoproduct.lean:164`) and several scout files (`RawRecoveredOuterScout`,
`CarrierClosureMap`, `Phase1bEntryAudit`) asserted "there is no `Fintype (ResolvedFeynmanSubgraph G)` (no global resolved
enumeration)", ruling OUT the all-proper-filter (saturated) carrier.  That was a design *choice*, not an impossibility:
the value data of a resolved subgraph is entirely ambient-bounded

    vertices ⊆ G.vertices,   internalEdges ≤ G.internalEdges,   externalLegs ≤ G.externalLegs,

and the remaining fields are `Prop`s.  Enumerating vertex subsets (`Finset.powerset`) and edge/leg SUBMULTISETS
(`Multiset.powerset`) bounds the data in a genuine finite set, so the `Fintype` is constructible.  This body builds it,
overturning the "RULED OUT" verdict, and lands the ambient-parametric saturated proper-forest index.

* `resolvedFeynmanSubgraph_ext` — a resolved subgraph is determined by `(vertices, internalEdges, externalLegs)`;
* `resolvedFeynmanSubgraphFintype` — `Fintype (ResolvedFeynmanSubgraph G)` via `Fintype.ofInjective` into the
  powerset-bounded triple (the finiteness floor);
* `resolvedAdmissibleSubgraphFintype` — `Fintype (ResolvedAdmissibleSubgraph G)` (inject by `.elements`);
* `saturatedProperForestIndex` — the ∀`G` saturated index `Finset.univ.filter IsProperForest` (NOT per-payload);
  `mem_proper` is a filter projection.

These are `def`s (NOT global `instance`s), so downstream instance resolution is unchanged (ripple-safe) — future bodies
opt in via `letI`.

**Audit verdict for the ambient-parametric saturated carrier.**
1. Two `Fintype`s — CONSTRUCTIBLE, landed here (contra the design note).
2. `IsProperForest` `mapPerm`-iff (for `carrier_mapPerm`) — NOT yet proved (no lemma exists); next body.
3. ambient-CD emptying (for `hCD`) — separate from body-413's ambient-support emptying; next body.
4. saturated carrier route — now UNBLOCKED (the index is landed); the remaining `RawW` fields are `carrier_mapPerm`
   (needs 2) and `hCD` (needs 3), plus `starOf` (body-414's allocator).
5. no fallback needed.

Per the guards: `Finset.univ` is used only AFTER the `Fintype` is constructed (via `letI`); NO per-payload cover is
lifted to arbitrary `G`; NO `forget` injectivity is assumed.  No facade, no flat term, no `forgetHopf`, no rep/perm, and
NO `promote_collapse` / singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

set_option linter.unusedSectionVars false

/-- **R-6c-body-415 — a resolved subgraph is determined by its value data** `(vertices, internalEdges, externalLegs)`
(the remaining fields are `Prop`s). -/
theorem resolvedFeynmanSubgraph_ext {G : ResolvedFeynmanGraph} {γ δ : ResolvedFeynmanSubgraph G}
    (hv : γ.vertices = δ.vertices) (hi : γ.internalEdges = δ.internalEdges)
    (hl : γ.externalLegs = δ.externalLegs) : γ = δ := by
  cases γ; cases δ; cases hv; cases hi; cases hl; rfl

/-- **R-6c-body-415 ∎ — the finiteness floor.**  `ResolvedFeynmanSubgraph G` is finite: its value data is bounded by the
ambient graph (vertex subsets + edge/leg submultisets), so it injects into a powerset-bounded triple. -/
noncomputable def resolvedFeynmanSubgraphFintype (G : ResolvedFeynmanGraph) :
    Fintype (ResolvedFeynmanSubgraph G) :=
  Fintype.ofInjective
    (fun γ : ResolvedFeynmanSubgraph G =>
      ((⟨γ.vertices, Finset.mem_powerset.mpr γ.vertices_subset⟩ :
          {vs // vs ∈ G.vertices.powerset}),
       (⟨γ.internalEdges,
          Multiset.mem_toFinset.mpr (Multiset.mem_powerset.mpr γ.internalEdges_le)⟩ :
          {es // es ∈ G.internalEdges.powerset.toFinset}),
       (⟨γ.externalLegs,
          Multiset.mem_toFinset.mpr (Multiset.mem_powerset.mpr γ.externalLegs_le)⟩ :
          {ls // ls ∈ G.externalLegs.powerset.toFinset})))
    (by
      intro γ δ h
      exact resolvedFeynmanSubgraph_ext
        (congrArg (fun t => (Prod.fst t).val) h)
        (congrArg (fun t => (Prod.fst (Prod.snd t)).val) h)
        (congrArg (fun t => (Prod.snd (Prod.snd t)).val) h))

/-- **R-6c-body-415 — the admissible-subgraph `Fintype`**, from the subgraph floor (inject by `.elements`). -/
noncomputable def resolvedAdmissibleSubgraphFintype (G : ResolvedFeynmanGraph) :
    Fintype (ResolvedAdmissibleSubgraph G) := by
  letI := resolvedFeynmanSubgraphFintype G
  exact Fintype.ofInjective (fun A : ResolvedAdmissibleSubgraph G => A.elements)
    (by intro A B h; cases A; cases B; cases h; rfl)

/-- **R-6c-body-415 — the ambient-parametric saturated proper-forest index.**  For every `G`, the finite carrier of ALL
proper resolved forests (`Finset.univ.filter IsProperForest`), with `mem_proper` a filter projection.  Genuinely `∀ G`
(NOT a per-payload cover), and available only because the finiteness floor is now constructed. -/
noncomputable def saturatedProperForestIndex (G : ResolvedFeynmanGraph) :
    ResolvedProperForestFiniteIndex G := by
  letI := resolvedAdmissibleSubgraphFintype G
  letI : DecidablePred (fun A : ResolvedAdmissibleSubgraph G => A.IsProperForest) :=
    Classical.decPred _
  exact
    { carrier := Finset.univ.filter (fun A => A.IsProperForest)
      mem_proper := fun A hA => (Finset.mem_filter.mp hA).2 }

end GaugeGeometry.QFT.Combinatorial
