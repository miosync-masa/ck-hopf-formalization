import GaugeGeometry.QFT.HopfAlgebra.ResolvedAdmissibleSubgraphOfElements

/-!
# R-6c-body-231 — `forget_union_elements`: the forgetful image of a union splits (infra lemma)

Two-hundred-and-thirty-first genuine-body step — a small, reusable infrastructure lemma that body-230's scout flagged
as the first prerequisite for the canonical membership-rewrite adapter (`cert_mem`).  The forgetful `.elements` of a
resolved-forest `union` splits as the union of the two forgetful images:

```
(A.union B hCross).forget.elements = A.forget.elements ∪ B.forget.elements
```

Every piece is `rfl`-level (`union_elements` — `ResolvedAdmissibleSubgraphOfElements.lean:69`; `forget_elements` —
`ResolvedSubGraph.lean:191`) glued by `Finset.image_union`.  This is the element law that
`selectedOuterRawOf s = (leftOf s).union (promotedOf s) …` (body-128) and the region union
`(leftResidual ∪ rightRecovered) ∪ forestRecovered` (body-159) both need to relate their `forget` to the flat index —
whether the certificate route (`A = ofForgetForest A.forget`) or the five `IsProperForest` conjuncts.

Per the HALT: this is generic infra only — no certificate schema, no membership rewrite, nothing
`selectedOuter` / `recoveredOuter`-specific.  No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
variable {G : ResolvedFeynmanGraph}

namespace ResolvedAdmissibleSubgraph

/-- **R-6c-body-231 — the forgetful image of a union splits.**  `(A.union B).forget` has elements the union of
`A.forget.elements` and `B.forget.elements` — `union_elements` + `forget_elements` glued by `Finset.image_union`. -/
theorem forget_union_elements (A B : ResolvedAdmissibleSubgraph G)
    (hCross : ∀ γ ∈ A.elements, ∀ δ ∈ B.elements, γ ≠ δ → γ.Disjoint δ) :
    (A.union B hCross).forget.elements = A.forget.elements ∪ B.forget.elements := by
  simp only [forget_elements, union_elements, Finset.image_union]

end ResolvedAdmissibleSubgraph

end GaugeGeometry.QFT.Combinatorial
