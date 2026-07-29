import GaugeGeometry.QFT.HopfAlgebra.Phi4WDoublePrimeCoproduct
import GaugeGeometry.QFT.HopfAlgebra.Phi4ForestCoproductEntrance

/-!
# R-6c-QFT-R1-body-592 — resolved `rep*` + one-way flat-forget shadow audit

This body pins down exactly two honest facts about the resolved carrier and its forgetful
shadow, and — crucially — records the boundary where the deeper coalgebra-descent problem
begins, WITHOUT crossing it.

`rep*` here is **resolved graph-class representative selection** (`Quotient.out` on
`ResolvedFeynmanGraphClass`), NOT a `flat ↔ resolved` bridge.  We prove it is closed
(`phi4ResolvedRepCD` / `phi4ResolvedRep_gen`).

We then record that a `W″`-index resolved forest **forgets one-way** into the flat forest
coproduct index (`phi4WDoublePrime_forget_mem_phi4ForestCoproductIndex`), and refine that
landing into the *saturated* flat subindex (`phi4WDoublePrime_forget_mem_saturatedIndex`).

## What this body deliberately does NOT do

The full coproduct commutativity `TensorProduct.map forget forget ∘ Δ_resolved = Δ_flat ∘ forget`
is a DEEPER coalgebra-descent problem that this body MUST NOT claim, because:

1. **Index mismatch.**  The flat coproduct (`coproduct_phi4`) sums over proper forests with a
   *positive complement* — it does NOT impose external-leg saturation — whereas the resolved `W″`
   carrier sums over proper forests that ARE externally-leg-saturated.  The flat all-index is
   strictly larger than the saturated subindex.
2. **Fiber multiplicity.**  Id-distinct resolved occurrences can forget to the SAME flat forest
   (the `Finset.image ·.forget` collapses duplicates), so `forget` on forest indices is **not**
   injective and **not** bijective; no fiber-weighting / symmetry factor is assembled here.

Hence NOTHING about coproduct commutativity, coassociativity, counit, bialgebra, Measure/E, or a
reverse `flat → W″` lift is stated or proved.

## VERDICT

```
resolved rep*                     DERIVED (Step 1)
W'' forest -> flat forest         ONE-WAY (Step 3)
W'' forest -> flat saturated idx  DERIVED (Step 4)
flat all-index -> W''             NOT PROVED (flat coproduct counts non-saturated forests)
forget on forest indices          NOT INJECTIVE / NOT BIJECTIVE (ID-distinct resolved occurrences collapse; fiber multiplicity unhandled)
```

No `TensorProduct.map` / coalgebra morphism / `coproduct_phi4` / `coproduct_resolved_phi4` /
`forgetPhi4Hopf` / `rigidifyPhi4Hopf` appears in any lemma STATEMENT; no reverse lift / `Equiv` /
forget-injectivity; no Measure / E / coassoc; zero new `class` / `structure` / `instance`; zero
forbidden divergence classes.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

/-! ## Step 1 — resolved `rep*` (representative selection, NOT a bridge) -/

/-- **body-592 — resolved `rep*`.**  The `Quotient.out` representative of a resolved generator's
graph class.  This is representative *selection* on `ResolvedFeynmanGraphClass`; it is NOT a
`flat ↔ resolved` bridge. -/
noncomputable def phi4ResolvedRep (x : ResolvedPhi4HopfGen) : ResolvedFeynmanGraph :=
  Quotient.out x.val

/-- **body-592 — `rep*` lands back on the generator's class as a connected-divergent class.** -/
theorem phi4ResolvedRepCD (x : ResolvedPhi4HopfGen) :
    ResolvedFeynmanGraphClass.IsConnectedDivergentFor phi4DivergenceMeasureFamily
      phi4PermInvariantDivergenceMeasureFamily (phi4ResolvedRep x).toResolvedClass := by
  unfold phi4ResolvedRep
  rw [show (Quotient.out x.val).toResolvedClass = x.val from Quotient.out_eq x.val]
  exact x.property

/-- **body-592 — `rep*` regenerates the generator.**  A resolved generator equals the resolved
generator built from its own `rep*` representative — representative selection is closed. -/
theorem phi4ResolvedRep_gen (x : ResolvedPhi4HopfGen) :
    x = (phi4ResolvedRep x).toResolvedPhi4HopfGen
          ((ResolvedFeynmanGraphClass.isConnectedDivergentFor_toResolvedClass
            phi4DivergenceMeasureFamily phi4PermInvariantDivergenceMeasureFamily
            (phi4ResolvedRep x)).mp (phi4ResolvedRepCD x)) := by
  apply Subtype.ext
  rw [ResolvedFeynmanGraph.toResolvedPhi4HopfGen_val]
  unfold phi4ResolvedRep
  exact (Quotient.out_eq x.val).symm

/-! ## Step 2 — flat saturation shadow (measure-free predicates + forget lemmas) -/

/-- **body-592 — flat external-leg saturation** (the forgetful shadow of body-532's
`ResolvedExternalLegSaturated`). -/
def FlatExternalLegSaturated (G : FeynmanGraph) (γ : FeynmanSubgraph G) : Prop :=
  G.externalLegs.filter (fun ℓ => ℓ.attachedTo ∈ γ.vertices) ≤ γ.externalLegs

/-- **body-592 — flat forest external-leg saturation** (all components). -/
def FlatForestExternalLegSaturated {G : FeynmanGraph} [DivergenceMeasure G]
    (A : AdmissibleSubgraph G) : Prop :=
  ∀ γ ∈ A.elements, FlatExternalLegSaturated G γ

/-- **body-592 — component-level forget of saturation** (multiplicity-safe, `filter`/`map` commute,
NOT a membership-only shortcut). -/
theorem resolvedExternalLegSaturated_forget {H : ResolvedFeynmanGraph}
    (δ : ResolvedFeynmanSubgraph H) :
    ResolvedExternalLegSaturated H δ → FlatExternalLegSaturated H.forget δ.forget := by
  intro h
  -- `H.forget.externalLegs = H.externalLegs.map forget` (rfl), `δ.forget.vertices = δ.vertices`
  -- (rfl), `δ.forget.externalLegs = δ.externalLegs.map forget` (rfl):
  show (H.externalLegs.map ResolvedExternalLeg.forget).filter
        (fun ℓ => ℓ.attachedTo ∈ δ.vertices)
      ≤ δ.externalLegs.map ResolvedExternalLeg.forget
  rw [Multiset.filter_map]
  refine Multiset.map_le_map ?_
  -- `(p ∘ forget) ℓ` is defeq `p ℓ` since `(forget ℓ).attachedTo = ℓ.attachedTo` (rfl):
  refine le_trans (le_of_eq (Multiset.filter_congr (fun ℓ _ => Iff.rfl))) h

/-- **body-592 — forest-level forget of saturation** (φ⁴-specialized).  `A.forget.elements` is the
`Finset.image ·.forget` of `A.elements`; each flat component's saturation is supplied by SOME
resolved component forgetting to it (duplicates in the image are harmless). -/
theorem resolvedForestExternalLegSaturated_forget {G : ResolvedFeynmanGraph}
    (A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G)
    (h : @ResolvedForestExternalLegSaturated phi4DivergenceMeasureFamily G A) :
    @FlatForestExternalLegSaturated G.forget (phi4DivergenceMeasureFamily G.forget)
      (@ResolvedAdmissibleSubgraph.forget phi4DivergenceMeasureFamily G A) := by
  letI : (H : FeynmanGraph) → DivergenceMeasure H := phi4DivergenceMeasureFamily
  intro γ' hγ'
  rw [ResolvedAdmissibleSubgraph.forget_elements] at hγ'
  obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.mp hγ'
  exact resolvedExternalLegSaturated_forget δ (h δ hδ)

/-! ## Step 3 — `W″` forest ONE-WAY forget landing -/

/-- **body-592 — a `W″`-index resolved forest forgets INTO the flat forest coproduct index.**
ONE-WAY only: proper-forest structure gives the flat proper-disjoint membership (`fgMem`), and the
resolved complement positivity transports to the flat complement via `forget_complementEdges_eq_clean`
+ `Multiset.card_map`.  No reverse lift, no injectivity, no bijection. -/
theorem phi4WDoublePrime_forget_mem_phi4ForestCoproductIndex {G : ResolvedFeynmanGraph}
    (A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G)
    (hA : A ∈ @ResolvedProperForestFiniteIndex.carrier phi4DivergenceMeasureFamily G
      (phi4WDoublePrimeCanonicalSupply.index G)) :
    (@ResolvedAdmissibleSubgraph.forget phi4DivergenceMeasureFamily G A)
      ∈ G.forget.phi4ForestCoproductIndex := by
  letI : (H : FeynmanGraph) → DivergenceMeasure H := phi4DivergenceMeasureFamily
  -- `(index G).carrier` reduces to `resolvedLegSaturatedIndexFor phi4 phi4 G` (body-587/591 defeq):
  have hA' : A ∈ resolvedLegSaturatedIndexFor phi4DivergenceMeasureFamily
      phi4PermInvariantDivergenceMeasureFamily G := hA
  obtain ⟨_hsupp, _hcd, _he, _hl, hpf, _hsat⟩ :=
    (mem_resolvedLegSaturatedIndexFor phi4DivergenceMeasureFamily
      phi4PermInvariantDivergenceMeasureFamily G A).mp hA'
  rw [G.forget.mem_phi4ForestCoproductIndex]
  refine ⟨fgMem A hpf, ?_⟩
  have hcard : (@AdmissibleSubgraph.complementEdges G.forget (phi4DivergenceMeasureFamily G.forget)
        A.forget).card = A.complementEdges.card := by
    rw [forget_complementEdges_eq_clean A hpf.2.1, Multiset.card_map]
  rw [hcard]
  exact hpf.2.2.2.2

/-! ## Step 4 — saturated flat subindex + the landing into it -/

/-- **body-592 — the flat saturated forest coproduct subindex.**  The flat forest coproduct index,
further restricted to externally-leg-saturated forests — this is the flat shadow that `W″` actually
targets (strictly smaller than the full flat index). -/
noncomputable def FeynmanGraph.phi4SaturatedForestCoproductIndex (G : FeynmanGraph) :
    Finset (AdmissibleSubgraphFor phi4DivergenceMeasureFamily G) :=
  G.phi4ForestCoproductIndex.filter
    (fun A : AdmissibleSubgraphFor phi4DivergenceMeasureFamily G =>
      @FlatForestExternalLegSaturated G (phi4DivergenceMeasureFamily G) A)

@[simp] theorem FeynmanGraph.mem_phi4SaturatedForestCoproductIndex (G : FeynmanGraph)
    (A : AdmissibleSubgraphFor phi4DivergenceMeasureFamily G) :
    A ∈ G.phi4SaturatedForestCoproductIndex ↔
      A ∈ G.phi4ForestCoproductIndex ∧
        @FlatForestExternalLegSaturated G (phi4DivergenceMeasureFamily G) A := by
  unfold FeynmanGraph.phi4SaturatedForestCoproductIndex
  rw [Finset.mem_filter]

/-- **body-592 ∎ — a `W″`-index resolved forest forgets INTO the flat *saturated* subindex.**
INCLUSION ONLY; the reverse (`flat saturated → W″`, a coalgebra-descent step involving fiber
multiplicity) is NOT proved. -/
theorem phi4WDoublePrime_forget_mem_saturatedIndex {G : ResolvedFeynmanGraph}
    (A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G)
    (hA : A ∈ @ResolvedProperForestFiniteIndex.carrier phi4DivergenceMeasureFamily G
      (phi4WDoublePrimeCanonicalSupply.index G)) :
    (@ResolvedAdmissibleSubgraph.forget phi4DivergenceMeasureFamily G A)
      ∈ G.forget.phi4SaturatedForestCoproductIndex := by
  letI : (H : FeynmanGraph) → DivergenceMeasure H := phi4DivergenceMeasureFamily
  have hA' : A ∈ resolvedLegSaturatedIndexFor phi4DivergenceMeasureFamily
      phi4PermInvariantDivergenceMeasureFamily G := hA
  obtain ⟨_hsupp, _hcd, _he, _hl, _hpf, hsat⟩ :=
    (mem_resolvedLegSaturatedIndexFor phi4DivergenceMeasureFamily
      phi4PermInvariantDivergenceMeasureFamily G A).mp hA'
  rw [G.forget.mem_phi4SaturatedForestCoproductIndex]
  exact ⟨phi4WDoublePrime_forget_mem_phi4ForestCoproductIndex A hA,
    resolvedForestExternalLegSaturated_forget A hsat⟩

end GaugeGeometry.QFT.Combinatorial
