import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSurvivorMemTagReduction
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightRecoveredSectorScout
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestSectorBridgeScout

/-!
# R-6c-body-218 — tag correspondence bundle scout: the three image correspondences do NOT bundle (attack separately)

Two-hundred-and-eighteenth genuine-body step, a scout of whether the three image correspondences (survivor / right /
forest) can share a common theorem or a useful provider bundle.  The audit's verdict: **no common theorem, and even
a three-field provider record adds no value** — keep them separate and attack the lightest (`right`) individually.

## The three correspondences, and why they do not share a theorem

```text
survivor  (211)  ∀ z x₁ x₂, HEq x₁ x₂ → (x₁ ∈ rightComponents(recovered).image survivorComponent
                    ↔ x₂ ∈ z.2.1.elements ∧ Disjoint x₂.vertices (starOfZ z))   -- quotient→quotient, codomain z
right     (213)  ∀ q γ, γ ∈ (rightDomain (fwdMap q)).image componentToRight ↔ rightPrimSelected q γ   -- quotient→G, domain q
forest    (215)  ∀ q γ, γ ∈ (forestDomain (fwdMap q)).image componentToForest ↔ forestChoiceSelected q γ  -- quotient→G, domain q
```

Three independent obstructions to a common theorem:

* **graph level** — survivor is *quotient → quotient* (a `HEq` between two `contractWithStars` graphs, via
  `survivorComponent`), while right / forest are *quotient → G* (`componentToRight` / `componentToForest` land in `G`);
* **index type** — survivor is `ForestBlockCodType`-indexed over the *recovered* choice `⟨unionOuter z, recoverChoice
  z⟩` (codomain `z`), while right / forest are `ForestBlockDomType`-indexed over `fwdMap q` (domain `q`) — different
  index *types*, not just names;
* **predicate kind** — survivor's RHS is a `starOf`-disjointness geometric filter (`= x₂ ∈ rightDomain z`), while
  right / forest's are `choiceAt` tag predicates (`inl false` / `inr B`).

No single tag classifier produces all three.

## Right + forest share a shape, but not a statement (without new abstraction)

Right and forest are structurally identical (same `{G}` / `q` / `γ`, both G-level image ↔ `choiceAt`-tag over `fwdMap
q`), differing only in the constants `rightDomain` / `componentToRight` / `rightPrimSelected` (`inl false`) vs
`forestDomain` / `componentToForest` / `forestChoiceSelected` (`inr B`).  But `componentToRight` / `componentToForest`
are **distinct `Classical.choose` maps** over the **complementary** star filters (`Disjoint` vs `¬ Disjoint`) with
**distinct surjectivity witnesses**; a shared parameterised statement would need a tag-indexed `regionDomain t` /
`componentTo t` family that does not exist today.  So as currently defined they stay two fields.

## No existing machinery discharges any of the three

`rightPrimSelected_iff_choice` (body-… `RightPrimitiveFactorComplete`) discharges only the *predicate half*; there is
no `forestChoiceSelected_iff` yet; body-150/151/152's tag facts classify `recoverChoice`'s tag, not the *image*
membership through the backward `Classical.choose` maps.  The load-bearing content of all three is the `Finset.image`
round-trip membership (`componentTo…_spec`), unpackaged.

## Verdict and plan

* **No common theorem** — genuinely separate (graph level, index type, predicate kind).
* **No useful provider bundle** — a three-field record is type-legal but buys no proof reuse (the fields never
  reference each other) and only aggregates unrelated residuals; the three already sit in clean supply structures with
  clean downstream consumers.  Bundling is premature.
* **Keep separate; attack the lightest first — `right_image_correspondence`** (body-213): the only one with a ready
  predicate-side lemma (`rightPrimSelected_iff_choice`), the simplest tag (`inl false`, no `∃ B`), G-level membership,
  no `HEq`.  Then `forest` (same shape, needs a fresh `forestChoiceSelected_iff` + the `∃ B`); `survivor` last (the
  `HEq` quotient transport + geometric filter, codomain-indexed).

Per the HALT: no correspondence is proved; the `componentTo…` round-trip / `Classical.choose` body is not entered;
the assessment is recorded.

This is a documentation / scout anchor (like body-210).  The imports keep the map honest against the source.  No
declarations beyond this docstring.  No facade, no flat term, no `forgetHopf`.
-/
