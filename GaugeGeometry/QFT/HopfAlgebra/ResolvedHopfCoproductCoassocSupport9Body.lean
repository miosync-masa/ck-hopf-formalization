import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocGrandFullSupply

/-!
# R-6c-body-36 — support-9 representative-family bundle → `coassoc_gen`

Thirty-sixth genuine-body step, illuminating the FINAL exit of the wiring: what stands between the per-`G`
`ResolvedCoassocGrandFullSupply` building block and the capstone `coassoc_gen`.

The support-9 funnel is:

```
ResolvedCoassocGrandFullSupply D G          (per-G: heart term_eq + finite carriers + cover_on + inj_on)
   ▼  .toGlobalCoverSupply x (image_agreement) (branch_agreement)
ResolvedCoassocGlobalCoverSupply D x        (repGraph := G + the two regroup agreements at x)
   ▼  (∀ x)
ResolvedCoassocFullCompatibilitySupply D    (cover : ∀ x, ResolvedCoassocGlobalCoverSupply D x)
   ▼  .coassoc_gen
D.coassocLeft (X x) = D.coassocRight (X x)
```

So `coassoc_gen` needs, PER GENERATOR `x`: (i) a representative graph `repGraph x`, (ii) a full per-`G`
building block `grand x : ResolvedCoassocGrandFullSupply D (repGraph x)` (the entire heart + finite cover at
that representative), and (iii) the two regroup agreements connecting the cover sums over `repGraph x` to
`D.regroupImageSum x` / `D.regroupBranchSum x`.  This is the `∀ x` **representative-lift boundary** — the last
top-level obligation.

This file bundles those three into one record and wires it (pure adapter) all the way to `coassoc_gen`.  The
per-`G` `GrandFullSupply` already bundles everything below repGraph (heart + finite carriers + `cover_on` +
`inj_on`); what remains genuinely open is exactly the representative choice + the two regroup agreements.

**Leaf inventory to `coassoc_gen`, fully fixed:**

| Field | Nature |
|---|---|
| `repGraph : ResolvedHopfGen → ResolvedFeynmanGraph` | representative choice per generator |
| `grand x : ResolvedCoassocGrandFullSupply D (repGraph x)` | the per-`G` heart + finite cover at the representative |
| `image_agreement x` | regroup agreement: image side = cover image-weight sum |
| `branch_agreement x` | regroup agreement: cover (forest+mixed) term sum = branch side |

Per the HALT, the two regroup agreements are NAMED, not proved — they connect the cover sums to
`regroupImageSum` / `regroupBranchSum`, i.e. the representative-regrouping identity (Quot.sound representative
territory); this file stops exactly at that boundary.  All wiring is `rfl`/adapter — no leaf discharge.

Landed:

* `ResolvedCoassocRepresentativeFamilySupply D` — the `∀ x` representative family + the two agreements;
* `.toFullCompatibilitySupply` — the support-9 `ResolvedCoassocFullCompatibilitySupply`;
* `.coassoc_gen` — the capstone from the representative family.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData}

/-- **R-6c-body-36 — the representative-family supply.**  For each generator `x`: a representative graph, the
per-`G` grand building block over it, and the two regroup agreements at `x`.  This is the `∀ x`
representative-lift boundary — the last top-level obligation before `coassoc_gen`. -/
structure ResolvedCoassocRepresentativeFamilySupply (D : ResolvedCoproductProperForestData) where
  /-- A representative resolved graph for each generator. -/
  repGraph : ResolvedHopfGen → ResolvedFeynmanGraph
  /-- The per-`G` grand full supply (heart + finite cover) at each representative. -/
  grand : ∀ x : ResolvedHopfGen, ResolvedCoassocGrandFullSupply D (repGraph x)
  /-- Regroup agreement: the image side equals the cover's image-weight sum. -/
  image_agreement : ∀ x : ResolvedHopfGen,
    D.regroupImageSum x =
      ∑ z ∈ (grand x).toFiniteData.imageCarrier, (grand x).toFiniteData.imageWeight z
  /-- Regroup agreement: the cover's (forest + mixed) split-term sum equals the branch side. -/
  branch_agreement : ∀ x : ResolvedHopfGen,
    (∑ q ∈ (grand x).toFiniteData.forestCarrier, D.resolvedSplitChoiceTerm q.1)
      + (∑ q ∈ (grand x).toFiniteData.mixedCarrier, D.resolvedSplitChoiceTerm q.1)
      = D.regroupBranchSum x

/-- **R-6c-body-36 — the support-9 full compatibility supply from the representative family.** -/
noncomputable def ResolvedCoassocRepresentativeFamilySupply.toFullCompatibilitySupply
    (F : ResolvedCoassocRepresentativeFamilySupply D) :
    ResolvedCoassocFullCompatibilitySupply D where
  cover := fun x =>
    (F.grand x).toGlobalCoverSupply x (F.image_agreement x) (F.branch_agreement x)

/-- **R-6c-body-36 — the capstone from the representative family.**  `Δᵣ`-coassociativity on every
generator, from a single representative-family record. -/
theorem ResolvedCoassocRepresentativeFamilySupply.coassoc_gen
    (F : ResolvedCoassocRepresentativeFamilySupply D) (x : ResolvedHopfGen) :
    D.coassocLeft (MvPolynomial.X x) = D.coassocRight (MvPolynomial.X x) :=
  F.toFullCompatibilitySupply.coassoc_gen x

end GaugeGeometry.QFT.Combinatorial
