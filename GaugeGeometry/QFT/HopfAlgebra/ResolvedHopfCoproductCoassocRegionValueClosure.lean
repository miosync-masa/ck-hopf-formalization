import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecoveredRegionValueAssembly
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocParametricCarrierClosure

/-!
# R-6c-body-281 — region coherence: the value bridge assembly IS the parametric closure's region maps (PROVED)

Two-hundred-and-eighty-first genuine-body step — the first construction-boundary audit point (body-273): **region
identity coherence**.  The scout's verdict is (a) *definitionally-constructible*: body-269's `ResolvedParametricCarrier
ClosureSupply` region fields are plain `∀ {G}, ForestBlockCodType D G → ResolvedAdmissibleSubgraph G`
(`ParametricCarrierClosure.lean:96,98,100`), so body-280's shared `A.Left.leftResidual` / `A.Region.rightRecovered` /
`A.Region.forestRecovered` slot in **directly**.  `ResolvedRegionValueClosureSupply` carries the body-280 assembly + the
selected-outer closure + the three pairwise disjointnesses + `recovered_raw_mem` (the honest supplied model leaves), and
`toParametricCarrierClosure` builds a body-269 closure whose region maps ARE the assembly's — so `recovered_raw_mem`
(closure) and `recovered_region_membership_value` (body-280) speak about the *same* three maps, no equality bridge.
Round-trip-free (no `unionOuter`, no `recoverChoice`, no forward reconstruction).

## Final construction-boundary audit (scout conclusion)

The remaining path to a concrete `cover` for `coassoc_gen_of_parametric_model_value` (body-272), and what is REUSABLE
(S-free) vs the genuine remaining LEAVES:

```text
REUSABLE (S-free, already proved — do NOT re-prove):
  unionOuter               OuterUnionRegionsConcrete.lean:91-94   (reads only z)
  recoverChoice + 3 tags   RegionTagsConcrete.lean:95,85,96,110   (region-priority dite, S phantom)
  union_eq                 OuterUnionRegionsConcrete.lean          (elements decomposition)
  body-256 membership      tags → forestBlockDomFinset
  body-253 dite/Subtype    WitnessSplitFilteredValue.lean:110-160  + .toCover
  body-280 region membership  recovered_region_membership_value    (⇒ backward_outer outright)
  body-274 domain↔surv/remn                                         (value split)
  body-272 forwardMem      ForwardQuotientMemValue.lean:52-58       (already FREE)

FINAL LEAVES (genuinely unbuilt at the value root):
  1. forward_outer  (value):  selectedOuterRawOf ⟨unionOuter z, recoverChoice z⟩ = z.1
  2. forward_quotient (value): HEq (V.quotientForestRaw ⟨unionOuter z, recoverChoice z⟩) z.2
  (near-leaf) backward_choice (value): from body-280 + S-free forestTag cases
  backward_outer (value) is NOT a leaf — body-280 + Subtype.ext/ext_elements.
```

So the construction boundary reduces to **two genuine forward-reconstruction facts** (`forward_outer`,
`forward_quotient`) plus one reducible backward HEq — no more.

## Roadmap (endorsed split)

```text
281 region coherence  (this body — round-trip-free)
282 S-free unionOuter / recoverChoice on the value Region/Left  (raw preimage root)
283 tags + filtered membership → mixedPreimage_mem / forestPreimage_mem  (body-256)
284 four value branch specs: backward_outer/backward_choice (body-280) + forward_outer/forward_quotient (2 leaves)
285 ResolvedWitnessSplitFilteredValueConcreteData → .toCover → discharge body-272 cover
```

Per the HALT: only the region coherence record + its closure converter are defined; no `unionOuter` / `recoverChoice`
instantiation, no round-trip, no forward reconstruction is entered.  `recovered_raw_mem` and the three disjointnesses stay
supplied model leaves (body-269).  No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData}

set_option linter.unusedSectionVars false

/-- **R-6c-body-281 — the region coherence supply.**  The body-280 value bridge assembly (its shared `Region` / `Left`
region maps) plus the parametric closure's supplied model leaves: the filtered selected-outer closure, the three
pairwise disjointnesses of the assembly's maps, and the raw recovered-outer carrier membership.  Everything speaks about
`Assembly`'s three maps, so the closure and body-280's membership are coherent by construction. -/
structure ResolvedRegionValueClosureSupply (F : ResolvedSelectedOuterFilteredMemSupply D)
    (V : ResolvedConcreteSummandValueSupply D) (S : ResolvedConcreteSummandBundleSupply D) where
  /-- The shared value bridge assembly (body-280): one `Region`, one `Left`, six sound/complete leaves. -/
  Assembly : ResolvedRecoveredRegionValueBridgeAssemblySupply F V
  /-- The filtered selected-outer carrier closure (body-245). -/
  selected : ResolvedSelectedOuterFilteredMemSupply D
  /-- Left / right pairwise disjointness of the assembly's maps (model closure leaf). -/
  left_right_disjoint : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    ∀ γ ∈ (Assembly.Left.leftResidual z).elements, ∀ δ ∈ (Assembly.Region.rightRecovered z).elements,
      γ ≠ δ → γ.Disjoint δ
  /-- Left / forest pairwise disjointness of the assembly's maps (model closure leaf). -/
  left_forest_disjoint : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    ∀ γ ∈ (Assembly.Left.leftResidual z).elements, ∀ δ ∈ (Assembly.Region.forestRecovered z).elements,
      γ ≠ δ → γ.Disjoint δ
  /-- Right / forest pairwise disjointness of the assembly's maps (model closure leaf). -/
  right_forest_disjoint : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    ∀ γ ∈ (Assembly.Region.rightRecovered z).elements, ∀ δ ∈ (Assembly.Region.forestRecovered z).elements,
      γ ≠ δ → γ.Disjoint δ
  /-- The raw recovered outer (assembly's maps) lies in the carrier (model closure leaf). -/
  recovered_raw_mem : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    recoveredRawUnion (Assembly.Left.leftResidual z) (Assembly.Region.rightRecovered z)
        (Assembly.Region.forestRecovered z)
        (left_right_disjoint z) (left_forest_disjoint z) (right_forest_disjoint z) ∈ D.carrier G

namespace ResolvedRegionValueClosureSupply

variable {F : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}
  {S : ResolvedConcreteSummandBundleSupply D}

/-- **R-6c-body-281 — the parametric closure from the coherent region maps** (body-269).  Its region maps ARE the
assembly's `Left`/`Region` maps, so body-269's `recovered_raw_mem` and body-280's `recovered_region_membership_value`
are about the same maps by construction. -/
noncomputable def toParametricCarrierClosure (C : ResolvedRegionValueClosureSupply F V S) :
    ResolvedParametricCarrierClosureSupply D S where
  selected := C.selected
  leftResidual := C.Assembly.Left.leftResidual
  rightRecovered := C.Assembly.Region.rightRecovered
  forestRecovered := C.Assembly.Region.forestRecovered
  left_right_disjoint := C.left_right_disjoint
  left_forest_disjoint := C.left_forest_disjoint
  right_forest_disjoint := C.right_forest_disjoint
  recovered_raw_mem := C.recovered_raw_mem

end ResolvedRegionValueClosureSupply

end GaugeGeometry.QFT.Combinatorial
