import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocQuotientElementsRecovery

/-!
# R-6c-body-205 — survivor elements scout: `survivor_elements_heq` is a genuine survivor transport (no collapse)

Two-hundred-and-fifth genuine-body step, a scout of body-204's survivor half `survivor_elements_heq` before proving
it.  Unlike the backward-choice forest leaf — which collapsed to `rfl` because body-171's `forestRecovered` bridge
was exactly its membership witness — the survivor leaf is a **genuine transport identity**: no fielded bridge names
`rightSurvivorForest recovered`, so it does not collapse.  The scout fixes the reduction and provides the reusable
single-Finset transport helper.

## Why it does not collapse (the finding)

The two sides are built by *opposite* machines over *different* graphs:

```text
LHS  (rightSurvivorForest recovered).elements = rightComponents(recovered).attach.image survivorComponent
       = { γ.reembed : γ a component of unionOuter z, recoverChoice z γ = inl false }   (over the recovered contract graph)
RHS  rightDomain z = z.2.1.elements.filter (Disjoint · (starOfZ z))                     (over z.1.1.contractWithStars)
```

The forest side had body-171's `forestRecovered_forward_membership` naming `forestRecovered (fwdMap q)` exactly;
the survivor side has **no** dual `rightSurvivor_forward_membership` — body-170's `rightRecovered_forward_membership`
is about the *G-level* `componentToRight` image on a *domain* `q`, a different object.  So the genuine content — the
correspondence `recoverChoice z`-marks-`inl false` ⟷ star-avoiding components of `B`, and `survivorReembed` of each =
the `B`-component — must be fielded fresh (the body-170/171 pattern, on the quotient side).

## The reusable transport helper (PROVED)

`heq_finset_of_transport` is the single-Finset analogue of body-204's `heq_of_membership_split`: an outer subgraph
equality plus a (transported) membership equivalence gives the `HEq` of two Finsets over the two contract graphs.
`cases` the outer equality (abstract bound variables), then `heq_of_eq (Finset.ext …)`.  Both the survivor
(body-206) and remnant (body-207) halves reduce through this helper to a membership bridge.

## Assessment (scout deliverable)

* **No collapse** — `survivor_elements_heq` is a genuine survivor transport identity, not `rfl`.
* **Fresh bridge needed** — a quotient-side `rightSurvivor_forward_membership : δ ∈ (rightSurvivorForest
  recovered).elements ↔ δ ∈ rightDomain z` (transported), the dual of bodies 170/171.  Field it; do not prove the
  `componentToRight` / `survivorComponent` inverse in the assembly.
* **Survivor is lighter than remnant** — `survivorComponent = survivorReembed` preserves vertices and the intrinsic
  graph (`survivorReembed_toResolvedFeynmanGraph = rfl`), so the reembed half is `rfl`-level; only the tag/round-trip
  correspondence is genuine.  The remnant side carries de-contraction geometry (bodies 126/183), strictly heavier.
* **No shared element provider yet** — both `survivor_elements_heq` and `remnant_elements_heq` are fields of the same
  body-204 supply, and the *term-level* `Inj`/`Gen` share body-148's provider, but the *element-level* recovered-side
  membership bridges are both unbuilt (the body-205/207 residual).

Per the HALT: no membership bridge is proved; the `survivorComponent` / `componentToRight` inverse is not entered;
only the reusable transport helper and the assessment are delivered.

Landed:

* `heq_finset_of_transport` — the single-Finset `HEq` transport (PROVED, reusable for survivor and remnant).

Scout / toolkit body (like body-192 / body-197).  No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- **R-6c-body-205 — the single-Finset `HEq` transport.**  An outer subgraph equality plus a transported membership
equivalence gives the `HEq` of two Finsets over the two contract-with-stars graphs.  `cases` the outer equality
(abstract bound variables), then `heq_of_eq (Finset.ext …)`.  The single-part analogue of body-204's
`heq_of_membership_split`; used by both the survivor (body-206) and remnant (body-207) halves. -/
theorem heq_finset_of_transport {G : ResolvedFeynmanGraph} {A₁ A₂ : ResolvedAdmissibleSubgraph G}
    (houter : A₁ = A₂)
    {s₁ : Finset (ResolvedFeynmanSubgraph (A₁.contractWithStars (D.starOf G A₁)))}
    {s₂ : Finset (ResolvedFeynmanSubgraph (A₂.contractWithStars (D.starOf G A₂)))}
    (hmem : ∀ x, x ∈ (houter ▸ s₁) ↔ x ∈ s₂) :
    HEq s₁ s₂ := by
  cases houter
  exact heq_of_eq (Finset.ext hmem)

end GaugeGeometry.QFT.Combinatorial
