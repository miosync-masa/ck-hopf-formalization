import GaugeGeometry.QFT.HopfAlgebra.ResolvedAdmissibleSubgraphOfElements

/-!
# R-6c-body-240 — `IsNonempty` transfer infra: cover / membership-iff and union helpers (PROVED)

Two-hundred-and-fortieth genuine-body step — the reusable infrastructure that body-239's scout flagged for the
piece-specific `IsNonempty` conjunct.  The direct tool for `Y` (the recovered-outer region union) is a **membership
cover** transfer: if every element of a nonempty `A` also lies in `B`, then `B` is nonempty.  This lands `Y.IsNonempty`
straight from `recovered_region_membership`'s ⟸ direction plus `q.1.1.elements.Nonempty` (carrier-proper on the domain
outer), with no `union` bookkeeping.  Two `union`-side helpers are included for completeness.

## The lemmas

```lean
isNonempty_of_cover          (hA : A.IsNonempty) (hcover : ∀ γ, γ ∈ A.elements → γ ∈ B.elements) : B.IsNonempty
isNonempty_of_membership_iff (hA : A.IsNonempty) (hmem  : ∀ γ, γ ∈ A.elements ↔ γ ∈ B.elements) : B.IsNonempty
union_isNonempty_left  (hA : A.IsNonempty) : (A.union B hCross).IsNonempty
union_isNonempty_right (hB : B.IsNonempty) : (A.union B hCross).IsNonempty
```

`IsNonempty A = A.elements.Nonempty` (`ResolvedSubGraph.lean:627`), so `cover` is just destructuring the witness and
re-membering it; `membership_iff` is `cover` via `.mp`; the union helpers use `union_elements`
(`ResolvedAdmissibleSubgraphOfElements.lean:69`) + `Finset.mem_union_left/right`.

Per the HALT: generic infra only — no `Y` proof, no certificate field, nothing `selectedOuter` / `recoveredOuter`
specific.  No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
variable {G : ResolvedFeynmanGraph}

set_option linter.unusedSectionVars false

namespace ResolvedAdmissibleSubgraph

/-- **R-6c-body-240 — nonemptiness transfers along an element cover.**  If `A` is nonempty and every element of `A`
lies in `B`, then `B` is nonempty. -/
theorem isNonempty_of_cover {A B : ResolvedAdmissibleSubgraph G} (hA : A.IsNonempty)
    (hcover : ∀ γ, γ ∈ A.elements → γ ∈ B.elements) : B.IsNonempty := by
  obtain ⟨γ, hγ⟩ := hA
  exact ⟨γ, hcover γ hγ⟩

/-- **R-6c-body-240 — nonemptiness transfers along an element membership equivalence.** -/
theorem isNonempty_of_membership_iff {A B : ResolvedAdmissibleSubgraph G} (hA : A.IsNonempty)
    (hmem : ∀ γ, γ ∈ A.elements ↔ γ ∈ B.elements) : B.IsNonempty :=
  isNonempty_of_cover hA (fun γ h => (hmem γ).mp h)

/-- **R-6c-body-240 — a union is nonempty if its left summand is.** -/
theorem union_isNonempty_left {A B : ResolvedAdmissibleSubgraph G}
    (hCross : ∀ γ ∈ A.elements, ∀ δ ∈ B.elements, γ ≠ δ → γ.Disjoint δ) (hA : A.IsNonempty) :
    (A.union B hCross).IsNonempty := by
  obtain ⟨γ, hγ⟩ := hA
  exact ⟨γ, by rw [union_elements]; exact Finset.mem_union_left _ hγ⟩

/-- **R-6c-body-240 — a union is nonempty if its right summand is.** -/
theorem union_isNonempty_right {A B : ResolvedAdmissibleSubgraph G}
    (hCross : ∀ γ ∈ A.elements, ∀ δ ∈ B.elements, γ ≠ δ → γ.Disjoint δ) (hB : B.IsNonempty) :
    (A.union B hCross).IsNonempty := by
  obtain ⟨γ, hγ⟩ := hB
  exact ⟨γ, by rw [union_elements]; exact Finset.mem_union_right _ hγ⟩

end ResolvedAdmissibleSubgraph

end GaugeGeometry.QFT.Combinatorial
