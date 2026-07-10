# Connes–Kreimer Hopf Algebra — Dependency Graph

*The technical proof-dependency map of the CK Hopf algebra formalization, for
developers and reviewers.  Companion to `CK_HOPF_FORMALIZATION_MAP.md` (the
reader-facing distillation) and `HOPF_DECOMPOSITION.md` (the full sprint log).*

All Lean names below are verified against the source.  Constructive body:
no `sorry`/`admit`/project axiom.  The only conditional surface is the **two**
named boundary-semantics kernels in §4 (the former third kernel, the CK §3
right-antipode core identity, is eliminated — §4).

---

## 1. File / module layer

```
Combinatorial/FeynmanGraphs.lean         flat carrier: FeynmanEdge, ExternalLeg, FeynmanGraph
        │                                  FeynmanEdge.retarget (Finset, star)-based
        ▼
Combinatorial/SubGraph.lean              admissible subgraphs, contractWith, componentAt
        │                                  IsFreshStarAssignment, retargetVertex_of_mem_component
        ▼
HopfAlgebra/Coassoc.lean   (~36.7k LOC)  coproduct_strict_forest, forest cover,
        │                                  Track A/B, coassoc, CoassocStrictForestH58Ready
        ▼
HopfAlgebra/Bialgebra.lean               instCoalgebraHopfHStrictForest,
        │                                  instBialgebraHopfHStrictForest
        ▼
HopfAlgebra/Antipode.lean                antipode_forest, AntipodeForestRightCoreIdentity,
        │                                  AntipodeStrictForestRightReady (+ connector instance)
        ▼
HopfAlgebra/HopfAlgebra.lean             instHopfAlgebraStructHopfHStrictForest,
                                           instHopfAlgebraHopfHStrictForest  (conditional)

Combinatorial/ResolvedFeynmanGraphs.lean boundary-resolved carrier (Track R, standalone)
        │
        ├─────────────────────────────────┐
        ▼                                  ▼
HopfAlgebra/BoundaryResolved.lean        Combinatorial/ResolvedSubGraph.lean
        │   Tier 1 bridge: distilled        R-4-full Phase 1 lower spine (standalone)
        │   facade content on resolved        ResolvedFeynmanSubgraph
        │   carrier (imports Coassoc +         ResolvedAdmissibleSubgraph
        │   Resolved)                          contractWithStars / quotientRemainderSubgraph
        ▼                                      insertion uniqueness ✅ (bomb #1)
HopfAlgebra/BoundaryResolvedCounterexamples.lean   external-leg liftability ✅ (bomb #2)
        formal mechanism-level negative results:
        flat edge/leg retarget maps non-injective
```

`ResolvedFeynmanGraphs.lean` is intentionally standalone: it imports the flat
carrier (for `forget`) but is not wired into the Hopf coproduct/coassoc stack
(that would be `R-4-full`).  `BoundaryResolved.lean` is the thin bridge importing
both Coassoc and the resolved carrier; it states the distilled content of the two
flat-false facades and proves them on the resolved carrier (Tier 1 — no resolved
SubGraph layer).

`ResolvedSubGraph.lean` is the **R-4-full Phase 1 lower graph spine** (also
standalone — imports `ResolvedFeynmanGraphs` + flat `SubGraph`, no HopfAlgebra;
not yet wired into `Main`).  It builds the resolved subgraph / admissible-forest /
contraction / quotient-remainder carriers and proves the resolved counterparts of
**both** flat-false boundary interfaces:

```
ResolvedSubGraph spine ✅  (R-4-full Phase 1)
  ├ ResolvedFeynmanSubgraph                 (1a)
  ├ ResolvedAdmissibleSubgraph              (1b)
  ├ contractWithStars                       (1c)
  ├ quotientRemainderSubgraph               (1d)
  ├ insertion uniqueness ✅  parent_eq_of_remainder_eq               (1e, bomb #1)
  └ external-leg liftability ✅  externalLegs_lift_unique /
                                 parent_externalLegs_eq_of_remainder_eq  (1f, bomb #2)
```

`ResolvedCoproductIndex.lean` and `ResolvedCoproduct.lean` are the **R-4-full
Phase 2** layer (HopfAlgebra-level — they import `ResolvedSubGraph` + `Coproduct`;
standalone, not yet wired into `Main`).  They bridge the resolved proper forest to
the flat finite index and define the resolved coproduct summand/sum:

```
Resolved coproduct via forget ✅  (R-4-full Phase 2)
  ├ IsProperForest (predicate + projections)                         (2a)
  ├ forget_injOn_elements  (linchpin: forget injective on components) (2b)
  ├ forget_mem_properDisjointAdmissibleDivergentSubgraphs            (2b)
  ├ forget_mem_properDisjoint_filter_complement  → forestCoproductProperForestIndex (2c-i)
  ├ strictSummandViaForget  (= flat summand of A.forget)              (2c-ii)
  └ ResolvedProperForestFiniteIndex + strictCoproductSum             (2d)
```

Design conclusions (cost-lowering): **no** native resolved `Fintype`, **no**
ambient `EdgeIdsUnique` (multiset `map` preserves card), **no** `ResolvedHopfGen`
(algebra carrier stays flat `HopfH`; resolved is a semantic witness layer).

`ResolvedCoproduct.lean` (Phases 3–5) lifts this to the whole carrier, and
`ResolvedPayloadModel.lean` (Phase 6c) makes it unconditional on the payload:

```
ResolvedCoproduct  ✅  (Phases 3–5)
  ├ strictSummandCanonicalViaForget                                  (3a-b)
  ├ ResolvedProperForestFiniteCover + strictCoproductSumCanonical_eq_flat (3c)
  ├ resolvedCoproductX_eq_coproduct_strict_forest_X  (= flat Δ(X g)) (4a-b)
  ├ resolvedCoproduct_toLinearMap_eq_flat  (= flat coproduct as LinearMap) (4c)
  └ resolvedCoproduct_coassoc[_ofReflection]  (coassoc by transfer)  (5)

ResolvedPayloadModel  ✅  (R-4-full Phase 6c)
  flat graph / proper forest
     │  ofFlatGraph / ofForgetForest   (constant-id lift, edgeId/legId = ⟨0⟩)
     ▼
  ResolvedHopfPayloadFamily
     │  resolvedHopfPayloadFamily_exists   (axioms: propext, Classical.choice, Quot.sound)
     ▼
  non-vacuity / unicorn objection CLOSED ✅

ResolvedHopfCertificate  ✅  (R-4-full Phase 7)
  ResolvedPayloadModel      ─ payload existence ─┐
  ResolvedCoproduct         ─ resolved Δ = flat Δ ┤
  Coassoc/Antipode/Counit   ─ flat Hopf laws ─────┤  (all transferred by rw)
                                                  ▼
  ResolvedHopfStructureCertificate
  resolvedHopfStructureCertificate_holds   (coassoc + counit×2 + antipode×2)
  exists_resolvedHopfStructureCertificate  ✅  (inhabited + all Hopf laws)
```

So the resolved-payload coproduct equals the flat coproduct as a linear map,
satisfies the full Hopf-structure law bundle (`resolvedHopfStructureCertificate_holds`),
and is inhabited by a canonical constant-id lift
(`exists_resolvedHopfStructureCertificate`) — all depending only on
`propext`/`Classical.choice`/`Quot.sound`.  We deliberately do **not** register a
second `HopfAlgebra`/`Coalgebra`/`Bialgebra` typeclass instance on `HopfH` (it would
clash with the existing flat instance on the same carrier); the certificate carries
the full structural content without that clash.  **R-4-full is effectively closed.**

---

## 2. Instance dependency chain (the kernel funnel)

```
                    coproduct_strict_forest  (Δ, constructive)
                              │
        ┌─────────────────────┴─────────────────────┐
        │ coassoc (H5.8)                             │ counit / coalgebra laws
        │   via CoassocStrictForestH58Ready  🔒      │
        ▼                                            ▼
   instCoalgebraHopfHStrictForest  ◄─────────────────┘
        │
        ▼
   instBialgebraHopfHStrictForest
        │
        │  antipode_forest  +  AntipodeStrictForestRightReady
        │     (◄ AntipodeStrictForestRightReady_ofConvolution ✅
        │        convolution / local-nilpotency — NOT the §3 core identity)
        ▼
   instHopfAlgebraStructHopfHStrictForest
        │
        ▼
   instHopfAlgebraHopfHStrictForest      [CoassocStrictForestH58Ready]
                                          [AntipodeStrictForestRightReady]
```

Reading: the conditional `HopfAlgebra ℚ HopfH` instance
(`instHopfAlgebraHopfHStrictForest`) takes two instance arguments —
`[CoassocStrictForestH58Ready]` and `[AntipodeStrictForestRightReady]`.  **Both
are now synthesized** from the two boundary facades + the power-counting
environment: the coalgebra side via `CoassocStrictForestH58CoverData_ofReflection`
+ `CoassocStrictForestH58Ready_ofBoundaryFacades`, and the antipode side via
`AntipodeStrictForestRightReady_ofConvolution` (convolution / local nilpotency,
`AntipodeConvolution.lean`).  So `AntipodeForestRightCoreIdentity` is **no longer
on the path** — it is an eliminated kernel.  Final cross-file certificate:
`hopfAlgebraHopfH_ofBoundaryFacadesAndReflection_convolution`.

---

## 3. Coassociativity sub-DAG (Coassoc.lean)

`CoassocStrictForestH58Ready` (`Coassoc.lean:36708`) is the public facade whose
single field is the H5.8 strict-forest coassociativity equation.  Its discharge
factors through the forest cover identity and four hBP facade Models, three of
which are constructive:

```
coassoc_strict_forest_linear_of_generators          (149, 187, 209: algHom→linear→generators)
        │
        ▼
forest cover identity  (F2i-3q)
        │
   ┌────┼──────────────────────────────────────────────┐
   │    │                                                │
hBP #1 ✅  hBP #2 ✅  hBP #3 ✅              hBP #4 (semantic) ──┐
(constructive structural decomposition)                          │
        │                                                        ▼
        │                          forest_inj branch ✅:  full q.1 recovery
   Track A: hForestCompl ✅                            gated only on 🔒
   (_Q_v3_fully_canonical + 4 wrappers)               ForestGraphInsertionUniquenessModel
        │                                                        (Coassoc.lean:7027)
   Track B: mixed_inj ✅                                         │
   (forestComponentMixedBoundaryToQuotientForestSigma_inj)       │
        │                                                        │
   Track forest_cd: CoverData ✅ (canonical)                     │
   (SourceSubgraphExactPlus.IsConnectedDivergent theorem)        │
        │                                                        │
        └──► promoted external legs branch → 🔒 ◄───────────────┘
             ForestQuotientForestSigmaForestCover
               PromotedExternalLegsLiftableModel  (Coassoc.lean:21749)
```

- **Track A** (`hForestCompl`): forest-complement supply, fully discharged.
- **Track B** (`mixed_inj`): mixed-boundary coassoc injectivity, fully
  discharged over an 8-sprint free-index generic-lemma campaign.
- **Track B-forest** (`forest_inj`): forest-branch injectivity, fully discharged
  (full `q.1` Left/Right/Forest-parent recovery), gated only on
  `ForestGraphInsertionUniquenessModel`.
- **Track forest_cd**: `SourceSubgraphExactPlus.IsConnectedDivergent` (Connected
  via path-lift + 1PI bridge-free + Divergent via reverse power-counting
  reflection) discharges `CoassocStrictForestH58CoverData` canonically — coassoc
  carries no residual cover-data hypothesis (audit
  `coassoc_strict_forest_linearMap_ofReflection`).
- The two 🔒 kernels are the **boundary-semantics facades** — false on the flat
  carrier (§5 of the formalization map), repaired by Track R.  The underlying
  collapse is sealed as **formal mechanism-level counterexamples** in
  `BoundaryResolvedCounterexamples.lean` (`flatEdgeRetarget_not_injective`,
  `flatLegRetarget_not_injective`, and their singleton-multiset forms): the flat
  edge/leg retarget maps are provably non-injective.  These do not negate the
  facade classes directly (those are proof-skeleton interfaces) but formalize the
  exact retargeting collapse the facades would have to rule out.

---

## 4. The two named kernels

| Kernel | Location | Gates | Nature |
|---|---|---|---|
| `ForestQuotientForestSigmaForestCoverPromotedExternalLegsLiftableModel` | Coassoc.lean | coassoc (promoted-legs branch) | ✗ flat / ∎ resolved |
| `ForestGraphInsertionUniquenessModel` | Coassoc.lean | coassoc (forest_inj internalEdge branch) | ✗ flat / ∎ resolved |

Both are carrier artifacts (Track R turns them into theorems on
`ResolvedFeynmanGraph`).  There is **no** remaining genuine open proof obligation.

**Eliminated:** `AntipodeForestRightCoreIdentity` (the former CK §3 right-antipode
cancellation kernel) is no longer required.  The right antipode axiom is
discharged via the convolution / local-nilpotency route
(`AntipodeStrictForestRightReady_ofConvolution`, `AntipodeConvolution.lean`): in
the convolution `Ring` `WithConv (HopfH →ₗ[ℚ] HopfH)` (built from the coalgebra
only), the left identity gives `S * id = 1`, the reduced operator `id − η∘ε` is
locally nilpotent on generators, and a finite "P-trick" yields `id * S = 1`
generator-wise, globalized by `MvPolynomial.algHom_ext`.  The old connector
instance `AntipodeStrictForestRightReady_of_coreIdentity` is retained but unused.

---

## 5. Track R sub-DAG (ResolvedFeynmanGraphs.lean)

```
R-1a  ResolvedEdgeId / ResolvedLegId / ResolvedFeynmanEdge / ResolvedExternalLeg
      ResolvedFeynmanGraph + forget (+ simp lemmas)
        │
R-1b  retarget (id-preserving)  +  EdgeIdsUnique / LegIdsUnique
      ResolvedFeynmanEdge.eq_of_retarget_eq_of_id_unique        (:187)
      ResolvedExternalLeg.eq_of_retarget_eq_of_id_unique        (:198)
        │
R-2a  retargetInternalEdges / retargetExternalLegs / retargetGraph
      forget_retargetInternalEdges / forget_retargetExternalLegs (Multiset.map_map)
      …_injOn
        │
R-3   Multiset.map_eq_of_injOn_le   (:339, generic count-ext lemma)
        │
        ├─ retargetInternalEdges_injective_on_submultisets       (:370)   ∎ kills Gap 2 core
        └─ retargetExternalLegs_injective_on_submultisets        (:385)   ∎ kills Gap 1 core
        │
R-4-link  forget_retargetGraph     (:289)   JAR commuting square
          forget ∘ retargetGraph = (flat retarget by f) ∘ forget
```

Each arrow is a direct Lean dependency.  `Multiset.map_eq_of_injOn_le` is the
single generic engine behind both injectivity theorems.

### Tier 1 bridge (BoundaryResolved.lean)

```
R-3a ──► resolved_insertion_internalEdges_unique      (distilled ForestGraphInsertionUniquenessModel)
R-3b ──► resolved_promotedExternalLegs_unique         (distilled …PromotedExternalLegsLiftableModel)
R-4-link ──► resolved_forget_retargetGraph_commutes   (forgetful recovery of the flat carrier)
        │
        ▼
BoundaryResolvedSemanticModel : Prop                  ✅ inhabited (non-vacuity witness)
  -- (1) injectivity before forgetting (repaired collapse):
  ├ edge_submultiset_retarget_injective    (← R-3a, under EdgeIdsUnique)
  ├ leg_submultiset_retarget_injective     (← R-3b, under LegIdsUnique)
  -- (2) exact projection onto the flat collapse map after forgetting:
  ├ edge_forget_retarget_commutes          (← map_forget_retarget_edges, rfl-level)
  ├ leg_forget_retarget_commutes           (← map_forget_retarget_legs, rfl-level)
  └ forget_retargetGraph_commutes          (← R-4-link)
  inhabited by `boundaryResolvedSemanticModel`
```

These are thin wrappers (`:=` term-mode) over the Track R theorems.  They do
**not** instantiate the flat facade classes (flat-false; `forget` is
resolved→flat).  They exhibit the distilled boundary-semantics principle of each
facade as a theorem on the resolved carrier — the concrete JAR claim.

`BoundaryResolvedSemanticModel` bundles the repaired principles (injectivity
before forgetting + exact projection onto the flat collapse map after forgetting)
into one inhabited `Prop` (`boundaryResolvedSemanticModel`): the **non-vacuity
witness**.  It answers
the "vacuity / unicorn" objection — the flat facades are intentionally uninhabited
(false; the diagnosis), while this is the concrete *inhabited* positive object on
the resolved carrier.

---

## 6. Kernel build/discharge order (for future campaigns)

The only remaining campaign is `R-4-full` (the two flat-false facades are
flat-false, so they can only be discharged on the resolved carrier):

1. **`ForestGraphInsertionUniquenessModel`** — coassoc `forest_inj` is fully
   discharged *gated on this model* (full `q.1` recovery + the fixed-`A`
   outer-subgraph injectivity for the `B` payload); the model itself remains the
   flat-false assumption, dischargeable only via `R-4-full`.
2. **`ForestQuotientForestSigmaForestCoverPromotedExternalLegsLiftableModel`** —
   the promoted-legs branch (likewise flat-false).
3. **`R-4-full`** — re-derive coproduct/coassoc/antipode on
   `ResolvedFeynmanGraph`; discharges kernels 1–2 *as theorems* on the resolved
   carrier and yields the unconditional Hopf structure.

Kernels 1–2 are flat-false, so on the flat carrier they remain assumptions; only
`R-4-full` discharges them, and only on the resolved carrier.  Not in this list:
the forest-cover CD obligation (`forest_cd` / `CoassocStrictForestH58CoverData`),
discharged canonically from the power-counting environment (reverse
forest-contraction reflection); and the former antipode kernel
`AntipodeForestRightCoreIdentity`, **eliminated** by the convolution /
local-nilpotency route (§4) — the right antipode axiom is a theorem, not a kernel.

---

## R-4-superfull — native H5.8 reindexing architecture (standalone, axiom-clean)

> **STATUS ✅ COMPLETE (R-4-full, 2026-06-18).**  The native H5.8 reindex is landed and
> axiom-clean: the public theorem `h58_resolved_carrier_double_sum_reindex`
> (`ResolvedActualSigmaCover.lean`) proves the outer-forest double sum
> `∑_A innerImageSum = ∑_A innerBranchSum` with axioms `[propext, Classical.choice,
> Quot.sound]` — **both** boundary facades discharged resolved-natively.  The "still not
> claimed complete" / "FINAL OBSTRUCTION" / "forest_term not yet proved" notes further down
> are the **historical build-up** (kept for the architecture trail); each has since been
> resolved — see the **R-4-full completion** block at the end of this section for what
> actually closed and how.

```
ResolvedBoundaryRepairCertificate         (resolved repairs on id-unique payload)
        │     (ResolvedUniquePayloadModel: ResolvedHopfPayloadFamilyWithUniqueIds)
        ▼
ResolvedSigmaParentSet                     (constructive σ-index; remnant_vertex_recovery
        │                                    PROVED via connectivity + star freshness)
        ▼
ResolvedBranchMapLayer ───────► ResolvedIndexedBranchClassifier   (∃! preimage)
        │   (forest/mixed image + isForestByStar + inj + cover)
        ▼
ResolvedFiniteBranchMapLayer.sum_reindex   (∑ image = ∑ forest + ∑ mixed)
        ▼
ResolvedH58WeightData / ResolvedFlatH58WeightAlignment   (coassoc-language reindex)
        │
        ▼   [Coassoc public aliases: h58Bridge{QuotientSigma,SplitChoiceSigma,
        │    QuotientIndex,SplitChoiceIndex,QuotientTerm,SplitChoiceTerm,SplitPhi}]
        ▼
ResolvedH58Bridge.resolvedH58ConcreteWeightSumReindex     (CONCRETE flat tensor terms)
        ▼
ResolvedH58ConcreteData ──► ResolvedH58ConcreteIndexMaps
        ▼
ResolvedActualSigmaCover.concrete_sum_reindex   ◄── FINAL OBSTRUCTION
```

**Final obstruction (single node):** construct one `ResolvedActualSigmaCover g`
(`ResolvedActualSigmaCover.lean`) — **not yet constructed**.  Fields: `FL`
(`ResolvedFiniteBranchMapLayer`, carrying cover/injectivity/CD/disjoint/avoidsStars),
`ResolvedH58ConcreteIndexMaps` (resolved→flat index maps + commutation), and
`splitTerm_agreement` (flat σ-cover factorization data).  All σ-cover data, **not**
boundary facades.  The architecture above reaches the concrete flat H5.8 tensor
reindexing identity; only this finite data object remains.  `Main` is unaffected apart
from the thin public aliases in `Coassoc.lean`.

**Cover consolidation.**  The `cover` field is reduced facade-free to one datum:
```
ResolvedCoverPreimageData.cover            (case split on resolvedIsForestByStar)
  ├─ mixed_case  := exists_mixed_preimage_of_not_forest   (structural; ofAdmissibleSubgraph)
  └─ forest_case := forest_case_of_preimageData           (from ResolvedForestCasePreimageData)
        ▲  parentOf : component → parent, parent_remnant_eq
        │
ResolvedForestCaseSupply.cover   ◄── the entire cover obstruction (one datum)
```
`ResolvedForestCaseSupply` = a `parentOf` component-to-parent lift per forest-by-star
image (`resolvedParentRemnant` component-level surjectivity, σ-cover data).  **No flat
`ForestQuotientForestSigmaForestCoverPromotedExternalLegsLiftableModel` is used.**  Full
native resolved H5.8 is **not** claimed complete; the cover obstruction / construction
interface is consolidated to σ-cover data supply.

**De-contraction section (constructed).**  The `parentOf` lift is now **built**, not assumed:
```
parentOfQuotient Aout starOf δ            (edges Aout.internalEdges + quotientEdgePreimage,
  ▲                                        legs quotientLegPreimage — id-preimages via
  │                                        exists_le_map + retarget_residual_*_injective)
  ├─ parentOfQuotient_containsAoutEdges    (le_add_right)
  └─ parentOfQuotient_remnant_eq : resolvedParentRemnant Aout starOf (parentOfQuotient … δ) = δ
        (edge/leg halves constructive; vertex half = hStars + QuotientVertexCovered saturation)
        │
singletonForestImageDataOfParent          (single-parent forest image — all-star containment
  │                                          forces single-parent granularity)
  ├─ CanonicalOuterForestQuotientSupply.forestCarrier / .forest_choiceParents_inj
  └─ ResolvedMixedCarrierSupply.mixedCarrier / .mixed_components_inj   (star-avoiding, no de-contraction)
        │
CanonicalOuterInnerSupplyData.toCanonicalSupply : CanonicalResolvedActualSigmaCoverSupply g
```
So the inner supply is obtainable from genuine de-contraction data; remaining inputs are the
concrete finite quotient/mixed carriers (+ CD/star facts), `ResolvedH58ConcreteIndexMaps`, and
`splitTerm_agreement` — all σ-cover data.  Full native resolved H5.8 still **not** claimed
complete.

**Track S — σ-cover finite-data supply (carrier import, in progress).**  The carrier-import
machinery (S-2 + S-3) is **built**:
```
forget_canonicalOuterContractedGraph     ◄── S-2 contracted-graph forget bridge
  Cres.forget = h58BridgeOuterActualQuotientGraph g A   (Cres := Aout.contractWithStars starOf)
  └─ id-uniqueness payoff: forget distributes over the complement subtraction
     (map_forget_complementEdges_canonicalOuterAout) + star / retargetVertex/Edge/Leg / starVertices align
        │
resolvedSubgraphOfForget (generic forget-subgraph lift, exists_le_map; no id-uniqueness)
  ├─ liftFlatQuotientSubgraphToCres + forget round-trip (HEq, via the bridge)   ◄── S-3a'
  └─ liftFlatQuotientForestToCres   + forget round-trip (HEq)                    ◄── S-3b
```
So flat quotient subgraphs/forests now lift into the resolved contracted graph `Cres` with
(heterogeneous) forget round-trips.  Remaining: **S-3c** build the concrete carriers
(`CanonicalOuterForestQuotientSupply.Q` / `ResolvedMixedCarrierSupply.mixedQ`) from the lifted
images with the CD/star/saturation facts transported; **S-4** `ResolvedH58ConcreteIndexMaps`
(resolved→flat coordinate dictionary, facade-free); **S-5** `splitTerm_agreement`
(resolved-native-or-supplied — the genuine boundary, NOT imported from flat).  Full native
resolved H5.8 still **not** claimed complete.

**Gold path — the boundary reduced to ONE predicate `forest_term`.**  The honest finishing-line
is now a single named theorem.  The reduction chain (all axiom-clean, in
`ResolvedActualSigmaCover.lean`):
```
ResolvedFlatH58Correspondence            ◄── boundary named (index dictionary + weight equality, one datum)
  ├─ flatImageOf  CONSTRUCTED (G-1a)     forget (S-2e bridge) + actual↔rep (h58BridgeActualQuotientToSigma)
  └─ P3 fix: carrier-based dictionary    ResolvedH58CarrierWeightData / …CarrierWeightAlignment
        (whole-type commutation was over-strong — sum_reindex only uses the carriers; P2 pattern)
        │
ResolvedFlatH58CarrierMixedAlignment .combine ResolvedFlatH58CarrierForestBoundary   ◄── mixed killed (G-1c)
        │   (mixed half = flatImageOf + origin-projection mixedSplitOf — mechanical)
ResolvedFlatH58CarrierForestIndexBoundary .combine ResolvedFlatH58CarrierForestTermBoundary  ◄── index vs term (G-2)
        │   (index = origin round-trip — mechanical; term = the factorization)
ResolvedFlatH58CarrierBranchTermBoundary .toForestTermBoundary    ◄── forest ⊕ mixed split (G-3, Sum.isLeft, no wrappers)
        │
forest_term : ∀ s ∈ splitChoiceIndex, s.isLeft → splitChoiceTerm s = quotientTerm (splitPhi s)   ◄── THE GOLD
```
**`full native resolved H5.8` is reduced to proving `forest_term` resolved-natively** — the
forest-branch weight factorization (= flat `forestComponentSplitPhi_term_eq_of_split`'s forest
half, Field-Filling-6's `hForestTerm`), *not* imported from flat's facade-discharged assembly.
The carrier / de-contraction / cover / reindex / dictionary-half / mixed-half are all complete.
`mixed_term` (right branch) is expected mechanical.  *(Historical: at this point `forest_term`
was the open finishing line; the **R-4-full completion** below records that it turned out
**canonical**, not a remaining gap.)*

### R-4-full completion ∎ — what actually closed (Gold sprints G-5…G-13h-10)

```
splitTermAgreementCanonical                ◄── G-9b: TERM side is fully CANONICAL (facade-free)
  (the "forest_term" finishing line above was NOT a gap — forest right + product + mixed_term
   all reduce to canonical certificates; corrects the earlier "right = facade" scout)
        │
canonicalFlatImageOf_liftFlatQuotientForestToCres   ◄── generic cover comm core (any Af + disjoint)
  = h58BridgeActualQuotientToSigma g A Af            (G-12b-1/2; used by BOTH forest and mixed)
        │
forest cover (facade #2 forest)  ──►  fullQuotientForestImageDataOfFlatSplit_comm   (G-13h-3b)
mixed  cover (facade #2 mixed)    ──►  fullMixedImageDataOfFlatSplit_comm           (G-13h-8)
  (mixed = the forest mirror: star-AVOIDING instead of touching; same comm core)
        │
ResolvedFullForestCoverOriginData / ResolvedFullMixedCoverOriginData   ◄── origin-indexed covers
  .toCoverData / .toMixedAlignment   (G-13h-7/8; named-def carrier avoids subst-typed whnf blowup)
        │
CanonicalOuterFullGrainInnerSupplyData.ofCoverOrigins .sum_reindex     ◄── per-A inner reindex (G-13h-8)
        │
ResolvedH58FullGrainOuterSkeleton.outer_sum_reindex                    ◄── outer sum over A (G-13h-9)
        │   (canonicalEmptyParents + Finset.subtype origin enumeration — G-13h-10)
        ▼
h58_resolved_carrier_double_sum_reindex   ◄── PUBLIC, facade-free, axiom-clean   ∎
        #print axioms = [propext, Classical.choice, Quot.sound]
```

- **Both facades discharged on the resolved carrier**: facade #1 (forest insertion uniqueness)
  via `resolvedParentRemnant_injOn` / `ResolvedFullQuotientForestImageData.toImage_injective`;
  facade #2 (cover liftability) via `resolved_promotedComponent_externalLegs_le_plus` + the
  full-grain forest+mixed cover above.  **Neither facade typeclass is instantiated.**
- **The gated `forestComponentSplitPhi_term_eq_of_split` is never exposed**; only facade-free
  building blocks and the final public theorem are surfaced.
- **The old flat `forestComponentSplitPhi` reindex stays facade-conditional BY NECESSITY.**
  Reconnaissance localized the sole flat-facade use to a single `parent_eq_of_remnant_eq` call
  (Coassoc ~12962) and proved no facade-free transport exists: flat insertion uniqueness is
  **false** on the flat carrier (`flatEdgeRetarget_not_injective`) — the flat retarget forgets
  the boundary edge/leg id data the theorem needs.  So the facade-free H5.8 reindex's native
  home is the **resolved carrier**, not the flat statement.  See
  `CK_HOPF_FORMALIZATION_MAP.md` §6 (R-4-full ∎) for the reader-facing account.

`Main` builds green (2938 jobs); the only `Main` touch is the thin public `h58Bridge*` aliases
in `Coassoc.lean` (alias-only, gated theorem not exposed).

---

## R-6c — native `Δᵣ`-coassociativity reduction campaign (in progress)

> **STATUS (2026-07-05).**  Native resolved coassociativity of `Δᵣ` on `ResolvedHopfH` is being reduced,
> one axiom-clean file per task (`GaugeGeometry/QFT/HopfAlgebra/ResolvedHopfCoproductCoassoc*.lean`), to a
> finite set of *named irreducible* geometry/measure supplies.  Every file `#print axioms =
> [propext, Classical.choice, Quot.sound]`; no facade, no flat term, no `forgetHopf`, no rep/perm.

The wiring funnel (already closed — heart support-9):
```
FinalLeafInventory (leaf-38)
   ▼   ResolvedCoassocGrandFullSupply
   ▼   ResolvedCoassocGlobalCoverSupply       (repGraph + finite + image/branch agreements)
   ▼   (∀ x) ResolvedCoassocFullCompatibilitySupply
   ▼   .coassoc_gen (x) : D.coassocLeft (X x) = D.coassocRight (X x)     ◄── capstone
```
`term_eq` (the heart) is `product_eq + right_eq`; `right_eq`'s route dependency is the three-route
vertex correspondence + `{Transport, QuotientStar, star_injective×2, starOf_fresh}`.

### Reduction DAG — what each remaining supply reduces to

```
occurrence_inj  (Product remnantInj + Sector forest_forward_injective)      (body-7)
   ▼   parent_inj            contracted-graph eq ⇒ parent component eq
   ▼   parent_graph_inj      ⇒ parent INTRINSIC-graph eq (ResolvedFeynmanSubgraph.ext)   (body-19)
   ▼   parentKey (vertex)    contractWithStars LOSSY (body-20/21: shape lost, ids remain);
   │                         leg-ids insufficient (body-23) → vertex key
   ▼   vertices_determine_parent   PROVED by surviving-vs-star chase                      (body-24)
        ├─ parent_disjoint         PROVED from s.1.1.pairwiseDisjoint                     (body-25)
        └─ ResolvedStarGlobalGapSupply   ◄── THE star kernel (irreducible for parametric D)
              star_avoids_outer_vertices + star_trace + contracted_nonempty              (body-26)
              (strictly ⊋ component-local ResolvedCanonicalStarFacts.starOf_fresh/_injective)

retarget_corr_on_vertices  (leaf-37, contract-twice = one-stage in corr coords)          (body-27)
   ├─ outer route (survivingOriginal)   PROVED concrete (body-8/9 + freshB)          (body-28/29b)
   ├─ inner-left route                  via threeRoute_invFun_leftStar_val + recovery (body-30)
   ├─ inner-right route                 via threeRoute_invFun_star_val + recovery     (body-31)
   ▼  ResolvedRetargetThreeRouteSupply  (Outer+Left+Right+same_innerLeft)             (body-32)
        (invFun value lemmas packaged at Three.toVertexCorrespondence level           (body-29))

innerCD_forget (leaf-18, doubly-contracted CD)                                           (body-33)
   ▼   contract_preserves_CD (CK power-counting stability) + D.hCD (ambient, defeq)
cd_nonempty (leaf-11 / component nonemptiness, measure)                                   (body-1)
   ▼   ResolvedMeasureLeafSupply  = cd_nonempty + contract_preserves_CD   (2-field measure record) (body-34)

quotientForest_union / toImage_split                                                      (body-14/17)
   ▼   (imageOf s).quotientForest = fullQuotientOf.toImage = remnant ⊔ right   BY rfl     (body-35)
        (concrete image side; sigma-cover Aout/starOf = selectedOuter+star definitionally)

FinsetSubtypePermExtensionSupply (leaf-35, nonlocal pure combinatorics)                   (body-18)
   ▼   CONSTRUCTED (Equiv.extendSubtype on ↥(s∪t), lifted by identity outside)   ∎ CLOSED

Product/Sector/Codomain element shapes (transport machinery)                           (bodies 2,3,5,6,
   ▼   elements_transport / elements_disjoint_transport (subst h; rfl)               10–16)
        + Product forest elements (existing @[simp] rfl) — all concrete
```

### Remaining named irreducible supplies (the honest floor)

| Supply | Nature | Status |
|---|---|---|
| `ResolvedMeasureLeafSupply` (`cd_nonempty`, `contract_preserves_CD`) | power-counting measure | fielded (2 axioms) |
| `ResolvedStarGlobalGapSupply` (global star freshness + cross-parent trace) | star id-traceability | fielded (⊋ canonical-local) |
| retarget `leftStar_recovery` / `rightStar_recovery` + inner applicability | three-route star recovery | fielded |
| support-9 representative lift (`repGraph`/`repCD`/`rep_eq`/`grand`) | cover geometry | pending |
| `ResolvedOuterImageFiberSupply` / `ResolvedOuterBranchFiberSupply` (2 fiber maps + maps_to + fiberwise agree) | OUTPUT σ-cover double sum | fielded (body-56/57) |
| `innerLeft = leftSelected` concretization; off-vertex retarget bridge (leaf-21 `∀v`) | connector | pending |

Everything structural or transport-shaped is `rfl` or proved (`parent_disjoint`, `vertices_determine_parent`,
`outer_case`, `FinsetSubtypePermExtensionSupply`, `quotientForest = remnant⊔right`).  The OUTPUT reindex is now
fully factored (bodies 52–57): its partition (`grandFull_partition_reindex`) and fibration
(`resolved_outer_cover_fibration`) engines are **proved** resolved-natively, and
`resolved_output_reindex_of_fibers` re-exports the two fiber supplies to `coassoc_gen` — so the only OUTPUT gap
left is the two fiber constructions.  No open-ended structural gap remains; each pending field is a recognized
geometry/measure assumption.

### R-6c bodies 88–136 — the term/index double sum folded into two bundles (2026-07-04)

The OUTPUT reindex (bodies 52–57) is the *outer-forest* double sum.  The per-`A` **inner** term/index bijection —
`∑_p splitChoiceTerm ⟨A,p⟩ = ∑_B leftTerm A ⊗ (leftTerm B ⊗ rightTerm B)` — is the remaining content, and bodies
88–136 reduce it, one axiom-clean file each, to a two-bundle assembly reaching `coassoc_gen` directly:

```
coassoc_gen  ⟸  ResolvedForestBlockBijectionSideSupply            (body-130, → body-113 → coassoc_gen)
             =  ResolvedConcreteSummandBundleSupply               (body-129: the whole PRODUCT side)
              + [ invConstruct + 8 membership/inverse laws ]      (the index/cover BIJECTION)
              + [ contract-twice geometry ]                       (bodies 27–49)
              + [ carrier_isProperForest + rep/repCD/rep_gen ]    (base)
```

**PRODUCT side — the four factor products + summand agreement (bodies 92–129), all closed to base supplies:**

```
resolvedSplitChoiceTerm ⟨A,p⟩ = leftTerm(selectedOuterOf) ⊗ (leftTerm B ⊗ rightTerm B)   (body-100/108/109/111/127)
   │  splitTerm = (∏ localLeftFactor) ⊗ ((∏ localRightFactor) ⊗ rightTerm)                (resolved_splitChoiceTerm_factor)
   ├─ ∏ localLeftFactor  = leftTerm(selectedOuterOf)   ← left_primitive (119, PROVED) + promoted (122, hPD)
   ├─ ∏ localRightFactor = leftTerm B                  ← right_primitive (120+125) + remnant (123+126)
   └─ rightTerm A' = rightTerm B (contract-twice)      ← quot_eq (111, ← contract geometry 27–49)
        │
   right_primitive: ∏ localRightFactor = leftTerm(rightSurvivor)   ← rightSurvivor_region_eq (RightFactorGen)
        via survivorInj + survivorGen[rfl]  (ResolvedRightSurvivorTransportSupply, body-125)
   remnant:        ∏ localRightFactor = leftTerm(remnant)          ← remnant_region_eq (RightFactorGen)
        via remnantInj + remnantGen[de-contraction]  (ResolvedRemnantTransportSupply, body-126)
        │
   forward-map coherence (body-128): the CONCRETE resolvedConcreteSelectedOuterImageSupply makes the ambient
   contract graph (selectedOuterOf q).1.contractWithStars  =  q.selectedOuterContractGraph  BY rfl,
   so the 125/126 forests slot into the summand bundle with NO cast (only selectedOuter_mem closure fielded).
        │
   ResolvedConcreteSummandBundleSupply (body-129) = Forward(128) + Measure(124) + Survivor(125) + Remnant(126)
        + [ quotientForest + union(115) + quot_eq ] ;  .summand_agree streams 119/122/124 by DEFEQ
```

**BIJECTION side — fully skeletonized (bodies 131–136):**

```
ResolvedOuterMixingBijectionProvider (body-131)  = invConstruct + 8 membership/inverse laws, classified vs sector:
   ├─ 4 membership (mixed/forest toFun_mem/invFun_mem) → Finset.sigma PLUMBING (bodies 132/133, PROVED)
   │     toFun_mem  ← resolvedIsForestImage star-touch classifier (2 fielded star facts, body-132)
   │     invFun_mem ← forestChoiceCarrier membership + isForestCarryingChoice tag (2 fielded, body-133)
   ├─ invConstruct  = ⟨recoverOuter, recoverChoice⟩  (body-134 skeleton; STRUCTURED, no longer opaque)
   │     grounded into 3 tagged regions leftRegion/rightRegion/forestRegion + region_cover  (body-135)
   │        left = A's left residual (inl true) ; right = B survivors via componentToRight (inl false)
   │        forest = B remnants via componentToForest (inr Bγ)
   └─ 4 inverse laws  = Sigma.ext adapters (body-136, PROVED):
         left_inv  = Sigma.ext (recoverOuter roundtrip)  (choice HEq)      [region-wise vs SectorLeafBundle]
         right_inv = Sigma.ext (selectedOuterOf roundtrip)(quotient HEq)
```

Every file `#print axioms = [propext, Classical.choice, Quot.sound]`.  The whole of `Δᵣ`-coassociativity now
rests on: **the concrete `recoverOuter`/`recoverChoice` backward reconstruction** (the flat
`forestComponentSplitPhiInverseConstruction` port — resolves the per-`s` sector-map `s`-dependence) with its 2
outer roundtrip eqs + 2 HEq roundtrips + the 4 star/tag facts; and the **non-bijection providers** — contract-twice
geometry (27–49), the survivor/remnant `Inj`/`Gen` (reembed), the measure leaf (124), and the base
(`carrier_isProperForest`, `selectedOuter_mem`, `rep`).  All wiring, decomposition, membership plumbing and
inverse-law splitting are done; only concrete geometry/reconstruction provider proofs remain.

### R-6c bodies 137–148 — the backward map built, proof-shape complete (2026-07-05)

Bodies 137–148 finish the *proof-shape* phase: the backward reconstruction `witnessSplit` is built branch-by-branch
down to region-local geometry, and the base providers are banked.  The residual is now a finite list of named local
geometry / measure / kernel facts — no structural or proof-shape work remains.

**The backward map, fully structured (bodies 138–147).**  The scout chain collapsed the inverse map to one object:

```
invConstruct = witnessSplit : ForestBlockCodType → ResolvedCoassocSplitChoice        (body-138: = ForestBlockDomType, defeq)
   │  recoverOuter/recoverChoice = the two projections of ONE map (no per-s reconstruction; s IS the output)
   ▼
witnessSplit z = if resolvedIsForestImage z.1 z.2 then forestPreimage z else mixedPreimage z   (body-141, flat classifier form 28811)
   │     forward_witness / backward_witness  PROVED from 4 branch specs (apply_dite + split_ifs)   (body-141)
   ├─ mixed branch  (B avoids star): primitive-only; ¬isForestCarrying PROVED from all-inl          (body-142)
   ├─ forest branch (B touches star): de-contraction parents; isForestCarrying PROVED from ∃-inr     (body-143)
   └─ combiner Mixed ⊕ Forest → ResolvedWitnessSplitConcreteData → witnessSplit → 4 inverse laws     (body-144)
   ▼
recovered outer A' = leftResidual(A) ∪ rightRecovered(B) ∪ forestRecovered(B)     (body-145, three-region union + union_eq)
   │     left → inl true ; right → componentToRight → inl false ; forest → componentToForest → inr Bγ
   ├─ region tags → branch p-tags (all_inl / exists_inr)  PROVED via Finset.ext_iff on union_eq      (body-146)
   └─ region round-trips → 4 branch forward/backward specs  PROVED via Sigma.ext                      (body-147)
         (mixed_forward = forest_forward = Sigma.ext forward_outer forward_quotient ; backward analog)
```

So the whole index/cover bijection flows from `ResolvedRegionRoundTripReductionSupply` (body-147), whose residual is
purely region geometry: the outer union (`leftResidual`/`rightRecovered`/`forestRecovered`/`unionOuter`/`union_eq`),
the three region tags + `forestRecovered` empty/nonempty, and the two `Sigma`-level round-trips
(`forward_outer`/`forward_quotient` HEq / `backward_outer`/`backward_choice` HEq).

**Base providers banked (bodies 137/140/148, alongside 124).**  Each recurring base leaf is pinned to one record:

| provider | body | content | status |
|---|---|---|---|
| `ResolvedCarrierProperProvider` | 137 | `carrier_isProperForest` | field / `ofFlatForest_isProperForest` for canonical `D` |
| `ResolvedContractGeometryProvider` | 140 | contract-twice `ResolvedContractTwiceOnceGeometrySupply` | bundles the 27–49 vertex/edge/retarget layer (`vertices_eq` = three-route star corr) |
| `ResolvedSurvivorRemnantProvider` | 148 | `survivorInj`/`survivorGen`/`remnantInj`/`remnantGen` | banks bodies 125/126; injectivities ⇐ star kernel via `occurrence_inj` |
| `ResolvedMeasureLeafSupply` | 124 | `cd_nonempty` + `contract_preserves_CD` | 2-field measure record |

**Final residual provider list (the honest floor).**  Every entry is a named local geometry / measure / kernel fact:

* **region geometry** (bodies 145–147): outer union + region tags + the two `Sigma`-level round-trips;
* **star facts** (body-132, `mixed_avoids_star`/`forest_touches_star`) + `forestChoiceCarrier` membership (body-133);
* **contract geometry** (body-140 → `vertices_eq`, the three-route star correspondence of bodies 27–32);
* **measure** (body-124);
* **star / global-gap kernel** (`ResolvedStarGlobalGapSupply`, powers `survivorInj`/`remnantInj`);
* **survivor / remnant** (body-148);
* **base** — `carrier_isProperForest` (body-137), `rep`, `selectedOuter_mem` (body-128 closure).

Superseded / not on the canonical path: the σ-cover common-cover route (bodies 36–87) is the *other* formulation and
its `cover_on`/`inj_on` are unsatisfiable-as-reused for the outer-mixing route (kept separate, body-139 scout); the
`boundary_tail_eq` well-founded induction (body-89) is superfluous once the nested-forest bijection is direct.

### R-6c bodies 149–154 — the region geometry localised (2026-07-05)

Bodies 149–154 drive the backward map's remaining content down to the **three concrete regions** and four
round-trip facts.  The membership classifiers and the union/tag machinery are proved; what is left is exactly the
region contents (from the sector maps) and the four `selectedOuterOf`/`quotientForest` region decompositions.

**Region geometry chain (all axiom-clean).**  The bijection now flows through the concrete region layer:

```
ResolvedOuterUnionRegionsConcreteSupply   (body-153: unionOuter = (left ∪ right) ∪ forest, union_eq PROVED)
   .toOuterUnionConstructionSupply → ResolvedOuterUnionConstructionSupply (body-145)
ResolvedRegionTagDefinitionSupply         (body-152: recoverChoice = region-priority dite, 3 tags PROVED)
   .toRegionChoiceRoundTripSupply → ResolvedRegionChoiceRoundTripSupply (body-146)
ResolvedConcreteRoundTripObligationSupply (body-154: 4 named round-trips A/B/A'/p)
   .toRegionRoundTripReductionSupply → ResolvedRegionRoundTripReductionSupply (body-147)
      → WitnessSplitBranchCombiner (144) → WitnessSplitConcrete (141) → WitnessSplitCoverSupply (139)
      → BijectionProvider (131) → coassoc_gen
```

Classifiers proved from the region data:

* `mixed_avoids_star` / `forest_touches_star` (body-150) — the `toFun_mem` star facts, from `survivor_avoids` +
  `mixed_remnant_empty` (mixed, PROVED via the summand bundle's `union_eq`) and `forest_quotient_touch` (forest);
* `mixed_inv_tag` / `forest_inv_tag` (body-151) — the `invFun_mem` `p`-tags: `forestChoiceCarrier` membership is
  `piCarrier` membership (**always** true) + non-extremality; forest side PROVED from the `inr` witness, mixed side
  from the primitive-mixture nontriviality; and the three region tags (body-152) are PROVED from the region-priority
  `recoverChoice`.

**What is proved / banked (the whole classifier + assembly layer):** the four membership fields (`toFun_mem` /
`invFun_mem` plumbing, bodies 132/133/150/151); the three region tags (body-152); `union_eq` (body-153, via
`Finset.ext` + `union_elements`, absorbing the `Finset` `DecidableEq` instance diamond); the summand-agreement bundle
(body-129); the survivor/remnant provider (body-148).

**Residual region providers (the honest floor now):**

* **region construction** (body-153) — the three region forests `leftResidual` ("not represented in `B`"),
  `rightRecovered` (`componentToRight` image), `forestRecovered` (`componentToForest` image), plus the two
  cross-disjointnesses and the carrier membership;
* **round-trips** (body-154) — `forward_outer` (A-reconstruction), `forward_quotient` (B-reconstruction),
  `backward_outer` (A'-recovery), `backward_choice` (p-recovery) — the `selectedOuterOf` / `quotientForest` region
  decompositions;
* **classifiers** (bodies 150/151/152) — `survivor_avoids` / `mixed_remnant_empty` / `forest_quotient_touch` (star),
  `mixed_ne_pR` / `mixed_ne_pL` (mixed non-extremality), the forest-index map `forestTag` and the region
  exclusivities;
* plus the non-region base — contract `vertices_eq`, measure, star/global-gap kernel, survivor/remnant Inj/Gen, and
  `carrier_isProperForest` / `rep` / `selectedOuter_mem`.

So the bijection's proof-shape is entirely closed; the next front is the region contents proper — constructing
`rightRecovered` / `forestRecovered` from the sector backward maps (`componentToRight` / `componentToForest`) and
`leftResidual` from the "not represented in `B`" filter, then discharging the four round-trip decompositions.

### R-6c bodies 155–160 — the region contents built (2026-07-05)

Bodies 155–160 build the three regions concretely and reduce the union assembly and outer round-trips to their
element-level content.  Every region now has an explicit `Finset`-of-components shape; the residual is exactly the
element partitions, the pairwise disjointnesses, the carrier closure, and the two heterogeneous quotient / choice
round-trips.

**The three regions, concrete (bodies 156/157).**  For `z = (A, B)` (`A = z.1`, `B = z.2` over
`A.1.contractWithStars`, split by the outer star `starOfZ z = z.1.1.starVertices (starOf G z.1.1)`):

```
rightRecovered  z = ofElements ((rightDomain z).attach.image  (componentToRight  z)) …   (body-156, survivors of B)
forestRecovered z = ofElements ((forestDomain z).attach.image (componentToForest z)) …   (body-156, remnants of B)
leftResidual    z = z.1.1.filterElements (fun γ => ¬ representedInQuotient z γ)          (body-157, A not represented)
```

with `rightRecovered_elements_eq` / `forestRecovered_elements_eq` / `leftResidual_elements_eq` all `rfl`
(`ofElements_elements` / `filterElements_elements`).  This is the backward mirror of the forward survivor forest
(body-125).

**The union assembly reduced (bodies 158/159).**  The two union cross-disjointnesses reduce to the three pairwise
region disjointnesses — `hcross_lr = left_right_disjoint`, `hcross_lrf` by `union_elements` + `mem_union`
case-split (body-158) — and the union's carrier membership is pinned to a single named leaf `recovered_outer_mem`
(body-159), parallel to `selectedOuter_mem` (body-128): a theorem for a canonical carrier, a genuine primitive for
an abstract parametric `D.carrier`.

**The outer round-trips reduced to element equalities (body-160).**  `forward_outer` / `backward_outer` (the two
`{A // A ∈ carrier}` round-trips) are proved by `Subtype.ext` + `ResolvedAdmissibleSubgraph.ext_elements` from the
element partitions `selectedOuter_partition` (`selectedOuterOf(recovered).elements = A.elements`) and
`recoveredOuter_partition` (`unionOuter(forward).elements = A'.elements`); the two heterogeneous `forward_quotient`
/ `backward_choice` round-trips are kept as fielded `HEq`.

**Residual region leaves (the honest floor now):**

* **element partitions** (body-160) — `selectedOuter_partition` (A = recovered selected outer) and
  `recoveredOuter_partition` (A' = reconstruction of forward image), at the `Finset`-of-components level;
* **heterogeneous round-trips** (body-160) — `forward_quotient` (B-reconstruction) and `backward_choice`
  (p-recovery), each needing the sector `componentToRight` / `componentToForest` round-trip;
* **pairwise disjointnesses** (body-158) and the **carrier closure** (body-159);
* **sector maps** (body-156, `componentToRight` / `componentToForest` + their `CD` / disjointness) and
  `representedInQuotient` (body-157, its equality with the sector-map images);
* **region classifiers** (bodies 150/151/152) and the non-region base (contract `vertices_eq`, measure,
  star/global-gap kernel, survivor/remnant Inj/Gen, `carrier_isProperForest` / `rep` / `selectedOuter_mem`).

So the region construction is fully localised; the next front is the element partition proofs (from `A = leftResidual
∪ represented` and the `selectedOuterOf` region decomposition) and the sector round-trips.

### R-6c bodies 161–165 — the four round-trips localised (2026-07-05)

Bodies 161–165 close the round-trip proof-shape: each of body-160's four round-trip obligations is reduced to a
single region partition or region-`HEq` leaf.  After this pass no round-trip is opaque — all four are named local
region facts, and the residual is the region partitions, the two `HEq` transports, and the pairwise / carrier /
sector / base geometry.

**The four round-trips, localised.**  Each is reduced to its region content:

| round-trip | body | reduced form |
|---|---|---|
| forward outer (A-reconstruction) | 162 | `selectedOuterOf(recovered).elements = A.elements` via `selectedOuterOf = leftOf ⊔ promotedOf` (`selectedOuter_mem_iff` PROVED), then the `leftOf ∪ promotedOf = A` partition |
| backward outer (A'-recovery) | 163 | `unionOuter(forward).elements = A'.elements` via body-145's `union_eq`, then the `leftResidual ∪ rightRecovered ∪ forestRecovered = A'` region partition |
| backward choice (p-recovery) | 164 | the `HEq (recoverChoice(forward)) q.2` leaf — region tags read back |
| forward quotient (B-reconstruction) | 165 | the `HEq (quotientForest(recovered)) B` leaf — survivors ⊔ remnants reconstruct `B` |

The two outer round-trips are **proved** from element partitions (`Subtype.ext` +
`ResolvedAdmissibleSubgraph.ext_elements`, body-160; `selectedOuter_mem_iff` via `simp` at the membership level,
body-162; `union_eq.trans`, body-163); the two heterogeneous ones are kept as named region-`HEq` leaves (bodies
164/165), their region-tag / survivor-remnant meaning documented.

**The chain (all axiom-clean).**  These feed the bijection unchanged:

```
162 (selectedOuter_partition) / 163 (recoveredOuter_partition) / 164 (backward_choice) / 165 (forward_quotient)
   → RoundTripComponentPartition (160) → ConcreteRoundTripObligations (154) → RegionRoundTripReduction (147)
   → WitnessSplitBranchCombiner (144) → WitnessSplitConcrete (141) → WitnessSplitCoverSupply (139)
   → BijectionProvider (131) → coassoc_gen
```

**Residual (the honest floor now):**

* **region partitions** — `leftOf_promotedOf_partition` (body-162, `leftOf ∪ promotedOf = A`) and
  `recovered_region_partition` (body-163, `leftResidual ∪ rightRecovered ∪ forestRecovered = A'`);
* **`HEq` transports** — `backward_choice_heq` (body-164) and `forward_quotient_heq` (body-165), the dependent
  transports across the outer / contract-graph equalities;
* **pairwise disjointnesses** (body-158) and the **carrier closure** (body-159);
* **sector maps** (body-156) and `representedInQuotient` (body-157);
* **region classifiers** (bodies 150/151/152) and the non-region base (contract `vertices_eq`, measure,
  star/global-gap kernel, survivor/remnant Inj/Gen, `carrier_isProperForest` / `rep` / `selectedOuter_mem`).

So the round-trip proof-shape is entirely closed; the next front is splitting the region partitions
(`leftOf_promotedOf_partition` / `recovered_region_partition`) into region-local sector facts.

### R-6c bodies 166–168 — the outer partitions split into region facts (2026-07-05)

Bodies 166–168 split the two outer round-trip partitions (bodies 162/163) into region-local facts, so the forward /
backward outer partitions are now entirely in region vocabulary.  What remains before the sector bridge is exactly
the region equalities and the target partition.

**Forward outer split (body-167).**  `leftOf ∪ promotedOf = A` (body-162) reduces to three region facts:

```
leftOf_recovered_eq      (leftOf recovered).elements   = leftResidual z .elements     (inl true)
promotedOf_recovered_eq  (promotedOf recovered).elements = forestRecovered z .elements  (inr)
target_outer_partition   (γ ∈ leftResidual ∨ γ ∈ forestRecovered) ↔ γ ∈ A.elements
```

so `selectedOuterOf(recovered) = leftResidual ⊔ forestRecovered = A` — the `inl false` right-primitive
(`rightRecovered`) region is *not* in the outer (it went into the quotient `B`).  Proved by `rw` of the region
equalities into the membership disjunction + the target partition.

**Backward outer split (body-168).**  `leftResidual ∪ rightRecovered ∪ forestRecovered = A'` (body-163) reduces to
the component membership partition

```
recovered_region_membership  (γ ∈ leftResidual ∨ γ ∈ rightRecovered ∨ γ ∈ forestRecovered) ↔ γ ∈ A'.elements
```

— the three recovered regions of the forward image classify `A'`'s components by their tags (`inl true` /
`inl false` / `inr`).  Proved by `Finset.ext` + `mem_union` + `or_assoc` (membership form used to avoid the
dependent `q.2 γ` tag).

**Chain.**  Both feed the bijection unchanged:

```
167 → SelectedOuterPartition (162) → 160 → 154 → 147 → witnessSplit → coassoc_gen
168 → RecoveredOuterPartition (163) → 160 → 154 → 147 → witnessSplit → coassoc_gen
```

**Residual (the honest floor now):**

* **region partition facts** — `leftOf_recovered_eq`, `promotedOf_recovered_eq`, `target_outer_partition`
  (body-167) and `recovered_region_membership` (body-168);
* **`HEq` transports** — `backward_choice_heq` (body-164), `forward_quotient_heq` (body-165);
* **sector bridge** — `rightRecovered` / `forestRecovered` are the `componentToRight` / `componentToForest` images
  (body-156), `representedInQuotient` (body-157), and the sector round-trips linking the region equalities to the
  `q.2` tags;
* **pairwise disjointnesses** (body-158) and the **carrier closure** (body-159);
* **region classifiers** (bodies 150/151/152) and the non-region base (contract `vertices_eq`, measure,
  star/global-gap kernel, survivor/remnant Inj/Gen, `carrier_isProperForest` / `rep` / `selectedOuter_mem`).

So both outer partitions are region-local; the next front is the **sector bridge** — connecting the region
equalities (`leftOf = leftResidual`, `rightRecovered`/`forestRecovered` = sector images) to the original choice
tags, starting with the survivor (`right`) side.

### R-6c bodies 169–175 — the sector bridges, backward trichotomy, and the forward asymmetry (2026-07-06)

Bodies 170–172 field the three **sector bridges** (each recovered region ↔ a choice tag on the forward image);
body-173 assembles the backward-outer partition from them; bodies 174/175 open the forward-outer partition and
discover that its two halves are *different in kind* — one is tag-level, the other geometry-level.

```text
sector bridges (fielded, region ↔ q.2 tag on the forward image)
  right   body-170  rightRecovered (forward q) ↔ rightPrimSelected q   (inl false)
  forest  body-171  forestRecovered (forward q) ↔ forestChoiceSelected q (inr)
  left    body-172  leftResidual (forward q)   ↔ leftSelectedConcrete q (inl true)

backward outer (PROVED to trichotomy)
  body-173  recovered_region_membership
            = rw the 3 bridges into the disjunction, then choice_tag_trichotomy
            choice_tag_trichotomy (PROVED): every component of q.1 has exactly one tag
              (inl true ∨ inl false ∨ inr) ↔ γ ∈ q.1.1.elements   (Sum/Bool case analysis)

forward outer  (asymmetry discovered)
  body-174  leftOf_recovered_eq       PROVED from tags + union_eq
              (leftSelection.leftOf recovered).elements = leftResidual z .elements
              leftOf = filter(leftSelectedConcrete); imageSupply.leftSelection = concrete def,
              so leftSelected = leftSelectedConcrete; forward = left_tag, backward = union_eq
              case-split with right_tag/forest_tag contradictions  (the all_inl/exists_inr pattern)
  body-174  promotedOf_recovered_eq   does NOT follow from tags — fielded
  body-175  promoted_region_eq        isolated as its own de-contraction geometry leaf
```

**The asymmetry (the body-174/175 finding).**  `leftOf` is **tag-level**: it is the `filter` of the recovered
outer by the `inl true` predicate, so it matches `leftResidual` by a pure region-tag argument (no new fielding).
`promotedOf` is **geometry-level**: `promotedOf recovered .elements = recovered.promotedElements` is the
**de-contracted** promoted forest (the `biUnion` over the forest-tagged components of `(promote γ Bᵧ).elements`),
whereas `forestRecovered z .elements` is the forest-choice **parents** (`componentToForest` images of the remnant
components).  Their equality is a **sector promotion / de-contraction round-trip**, not a tag lemma — so it stays
fielded, now as the named leaf `promoted_region_eq` (body-175).

**Residual (the honest floor now):**

* **forward-outer, two leaves** — `promoted_region_eq` (body-175, promotion / de-contraction round-trip) and
  `target_outer_partition` (`leftResidual ∪ forestRecovered = A`, the star-touch / remnant coverage);
* **backward-outer** — PROVED to `choice_tag_trichotomy` (body-173), standing on the three sector bridges
  (bodies 170/171/172);
* **`HEq` transports** — `backward_choice_heq` (body-164), `forward_quotient_heq` (body-165);
* **sector bridge internals** — the `componentToRight` / `componentToForest` round-trips inside the three bridges,
  `representedInQuotient` (body-157), the `promote` de-contraction for `promoted_region_eq`;
* **pairwise disjointnesses** (body-158) and the **carrier closure** (body-159);
* **region classifiers** (bodies 150/151/152) and the non-region base (contract `vertices_eq`, measure,
  star/global-gap kernel, survivor/remnant Inj/Gen, `carrier_isProperForest` / `rep` / `selectedOuter_mem`).

So the backward outer is proved down to the trichotomy, and the forward outer is cleanly split into a tag half
(PROVED) and a geometry half (`promoted_region_eq`) plus coverage (`target_outer_partition`); the next front is
`target_outer_partition` — the "`A`'s components are exactly `leftResidual` or forest/remnant-represented"
coverage — which fully separates the promotion side from the coverage side.

### R-6c bodies 177–181 — the forward outer coverage assembled to its floor (2026-07-06)

Bodies 177–181 take the forward-outer partition all the way down.  Body-177 recast `target_outer_partition` as a
**coverage classification**; bodies 178–180 discharged or isolated its three facts; body-181 assembled them and ran
the whole forward-outer partition out to body-162 in one line.

```text
leftResidual_mem      body-178  PROVED by filterElements (leftResidual = A.filter (¬ representedInQuotient))
                                over the fielded wiring bridge leftResidual_eq (abstract union ↔ body-157)
forest recovery box   body-179  forestRecovered_mem + promoted_region_eq — the two faces of the one
                                componentToForest de-contraction round-trip, shared in one provider
coverage classifier   body-180  coverage PROVED from represented_cases (represented → representedByForest)
                                by excluded middle; survivor case vacuous for the target outer
assembly              body-181  178 + 179 + 180 → 177 → 174 → 167 → 162, predicates pinned
                                (represented := representedInQuotient, representedByForest := body-179's)
```

**Forward outer final floor (the asymmetry, fully descended).**

```text
leftOf side       leftOf_recovered_eq   PROVED by tags (body-174)
coverage side     leftResidual_mem      PROVED by filterElements (body-178)
                  forestRecovered_mem   fielded in the forest-recovery box (body-179)
                  coverage              PROVED from represented_cases (body-180)
promotion side    promoted_region_eq    fielded in the forest-recovery box (body-179)
```

So the *only* genuinely fielded forward-outer content is now: the **forest-recovery geometry** (`forestRecovered_mem`
+ `promoted_region_eq`, body-179 — the `componentToForest` / `promote` de-contraction round-trip), the **star/remnant
classifier** (`represented_cases`, body-180), and the **wiring bridge** (`leftResidual_eq`, body-178).  Everything
else on the forward outer is proved.

**Canonical chain.**

```text
181 → 177 → 174 → 167 → 162 → 160 → 154 → 147 → witnessSplit → coassoc_gen
```

**Residual (the honest floor now):**

* **forward-outer, forest-recovery geometry** — `forestRecovered_mem` and `promoted_region_eq` (body-179, the one
  `componentToForest` de-contraction round-trip);
* **forward-outer, classifier** — `represented_cases` (body-180) and the wiring bridge `leftResidual_eq` (body-178);
* **backward-outer** — the three sector bridges (bodies 170/171/172), PROVED up to `choice_tag_trichotomy` (body-173);
* **`HEq` transports** — `backward_choice_heq` (body-164), `forward_quotient_heq` (body-165);
* **pairwise disjointnesses** (body-158) and the **carrier closure** (body-159);
* **region classifiers** (bodies 150/151/152) and the non-region base (contract `vertices_eq`, measure,
  star/global-gap kernel, survivor/remnant Inj/Gen, `carrier_isProperForest` / `rep` / `selectedOuter_mem`).

So both outer partitions are down to their floors: the backward outer stands on the three sector bridges + a proved
trichotomy, and the forward outer on the forest-recovery geometry + the classifier.  The next front is the
**forest-recovery geometry** — the `componentToForest` inverse / promotion de-contraction — the genuinely geometric
remaining leaf of the outer partition.

### R-6c bodies 183–186 — the forest-recovery deep leaf isolated (2026-07-06)

Bodies 183–186 open the forest-recovery box (body-179) and drive it down to a single geometric obstruction split
into two inclusions.  Body-183 split the box into three leaves; bodies 184/185 discharged the two shallow ones; body
-186 audited and split the deep one.

```text
body-183  forest-recovery box split into three leaves:
            forestRecovered_eq            (abstract union region ↔ body-156 componentToForest image)
            parent_mem_carrier            (a forest parent lands in A)
            promoted_eq_forestRecovered   (the deep de-contraction round-trip)
          with representedByForest := γ ∈ Construction.forestRecovered; forestRecovered_mem /
          promoted_region_eq PROVED from the leaves → body-179's supply.

body-184  forestRecovered_eq (and body-178's leftResidual_eq) become rfl by BUILDING the outer union from
          the concrete region constructions (body-156 right/forest + body-157 left); the abstract-union ↔
          concrete-construction gap is closed by construction, not fielded.

body-185  parent_mem_carrier reduced to the componentwise membership forestComponentMem
          (each componentToForest parent ∈ A), the parent leaf read off by Finset.mem_image.

body-186  promoted_eq_forestRecovered split into two inclusions (antisymm):
            forestRecovered_subset_promoted   LIGHT — a parent is a de-contracted component of its own
                                              promoted subforest (forest_tag + promotedComponentElements_inr
                                              + promote_elements + forestRecovered_elements_eq)
            promoted_subset_forestRecovered   HEAVY — every de-contracted component is a componentToForest parent
```

**The negative finding (body-186).**  This equality is *not* supplied by the sector inverse laws alone.  The sector
inverse (`forest_left_inv` / `forest_right_inv`) relates `componentToForest` to `forestToComponent` (= the
quotient-side `remnantComponent` into `selectedOuterContractGraph`) — it does **not** connect `componentToForest`
with `promote` / de-contraction into `G`.  The product-level de-contraction facts (`remnant_region_eq`,
`product_remnantGen_of_decontraction`) live on the quotient side at the polynomial/class level, not as element-level
`Finset` equalities.  So the remaining proof requires **concrete `componentToForest` / `forestTag` / `promote`
compatibility**, which the abstract supplies do not provide — this is the genuinely fresh geometric leaf.

**Canonical chain.**

```text
186 → 183 → 179 → 181 → 177 → 174 → 167 → 162 → 160 → 154 → 147 → witnessSplit → coassoc_gen
```

**Residual (the honest floor now):**

* **deep forest recovery** — `forestRecovered_subset_promoted` (light) and `promoted_subset_forestRecovered` (heavy),
  both resting on the prerequisite: concrete `componentToForest` / `forestTag` / `promote` compatibility;
* **forest membership** — `forestComponentMem` (body-185, each parent ∈ A);
* **classifier** — `represented_cases` (body-180);
* **backward-outer** — the three sector bridges (bodies 170/171/172), proved up to `choice_tag_trichotomy` (body-173);
* **`HEq` transports** — `backward_choice_heq` (body-164), `forward_quotient_heq` (body-165);
* **pairwise disjointnesses** (body-158) and the **carrier closure** (body-159);
* **region classifiers** (bodies 150/151/152) and the non-region base (contract `vertices_eq`, measure,
  star/global-gap kernel, survivor/remnant Inj/Gen, `carrier_isProperForest` / `rep` / `selectedOuter_mem`).

So the forward-outer geometry is one leaf in two inclusions, gated on making `componentToForest` / `promote`
concrete.  The next front is the **`componentToForest` concretization scout** — how far `componentToForest` can be
made concrete from `ForestPrimitiveIndex.toOccurrence` / `forest_surj` / `Classical.choose` — before the inclusion
proofs are attempted.

### R-6c bodies 188–190 — the forward outer geometry closed to compatibility leaves (2026-07-06)

Bodies 188–190 close the forward-outer partition.  Body-188 found the *semantic* content of the deep leaf and named
the compatibility; body-189 proved the de-contraction round-trip; body-190 assembled the whole forward outer down to
body-162.

```text
188  componentToForest / promote compatibility scout — the SEMANTIC finding:
       promotedComponentElements ⟨γ,_⟩ = (promote γ Bᵧ).elements = de-contracted SUB-PIECES of γ (⊆ γ),
       while forestRecovered = the PARENTS. So promotedOf recovered = forestRecovered holds IFF each
       promoted subforest collapses to its parent: (promote γ Bᵧ).elements = {γ}.
       Fielded: forestTag (Bᵧ), recoverChoice_forest_eq (tag pinning), promote_collapse ({γ}).
       PROVED: promotedComponentElements_forestRecovered = {γ} (per-component collapse).

189  promoted_region_eq PROVED by a biUnion collapse — promotedOf recovered .elements =
       unionOuter.attach.biUnion promotedComponentElements; union_eq splits into three regions: the inl-tagged
       left/right give ∅, each forestRecovered parent gives {γ}; the biUnion lands on forestRecovered.

190  forward outer geometry assembly — 188 (Compat) + 185 (forestComponentMem) + 180 (represented_cases) +
       178/183 wiring bridges + region constructions → body-179 → body-181 → body-162 in one line.
```

**Canonical chain.**

```text
190 → 181 → 177 → 174 → 167 → 162 → 160 → 154 → 147 → witnessSplit → coassoc_gen
```

**Forward outer final leaf list (the irreducible geometry).**

```text
forestTag                 body-188   the forest index Bᵧ of a recovered parent
recoverChoice_forest_eq   body-188   tag pinning (recoverChoice = inr Bᵧ on the forest region)
promote_collapse          body-188   (promote γ Bᵧ).elements = {γ} (the tag is the whole component)
forestComponentMem        body-185   each componentToForest parent ∈ A
represented_cases         body-180   a quotient-represented A-component is a forest parent
region construction/wiring          body-156/157 constructions + leftResidual_eq / forestRecovered_eq bridges
```

Everything structural above these is proved: `leftOf` (body-174), `leftResidual_mem` (body-178), `coverage`
(body-180), `forestRecovered_mem` / `promoted_region_eq` (bodies 185/189).

**Residual (the honest floor now):**

* **forward-outer** — *closed to the compatibility leaves above* (`forestTag`, `recoverChoice_forest_eq`,
  `promote_collapse`, `forestComponentMem`, `represented_cases`, region construction/wiring);
* **backward-outer** — the three sector bridges (bodies 170/171/172), proved up to `choice_tag_trichotomy` (body-173);
* **`HEq` transports** — `backward_choice_heq` (body-164), `forward_quotient_heq` (body-165);
* **sector bridge internals** — the `componentToRight` / `componentToForest` round-trips, `representedInQuotient`;
* **pairwise disjointnesses** (body-158) and the **carrier closure** (body-159);
* **region classifiers** (bodies 150/151/152) and the non-region base (contract `vertices_eq`, measure,
  star/global-gap kernel, survivor/remnant Inj/Gen, `carrier_isProperForest` / `rep` / `selectedOuter_mem`).

So the forward outer is closed to its irreducible geometric compatibility, verified in one chain to body-162.  The
next front is the **`HEq` transports** (`backward_choice_heq` / `forward_quotient_heq`) — splitting the remaining
round-trip content into component/sector facts.

### R-6c bodies 192–194 — the backward-choice HEq reduced to a forest value equality (2026-07-06)

Bodies 192–194 retire the backward-choice `HEq` mismatch and drive its content down to a single forest value fact.

```text
192  HEq scout — backward_choice_heq HEq (recoverChoice (fwdMap q)) q.2 is LIGHT (same codomain per component,
       reduces to a homogeneous componentwise Eq under the proved outer partition); forward_quotient_heq is HEAVY
       (ForestIdx over two contract-with-stars graphs, needs B = survivor ⊔ remnant).

193  heq_of_index_eq — the reusable dependent-function transport: (A = B) + pointwise Eq ⟹ HEq (subst + heq_of_eq
       + funext, the flat-Coassoc pattern as a clean Resolved lemma).  backward_choice_heq PROVED from the outer
       partition (body-160) + the componentwise Eq.

194  choice component cases — case on q.2 γ:
       inl false  → rightPrimSelected → right bridge (body-170) → region right_tag  ✓
       inl true   → leftSelectedConcrete → left bridge (body-172) → region left_tag  ✓
       inr B      → forestChoiceSelected → forest bridge (body-171) → region forest_tag gives ∃ B',
                    and the value match B' = B is fielded as forest_value_eq (the single fresh leaf).
```

**Canonical chain.**

```text
194 → 193 → 164 → 160 → 154 → 147 → witnessSplit → coassoc_gen
```

**Residual (the honest floor now):**

* **backward-choice** — the single `inr` value fact `forest_value_eq` (the choice-value de-contraction: on a
  forward image, the recovered forest tag equals the original forest index) + the reused tags / bridges + the proved
  index transport;
* **forward-quotient** — `forward_quotient_heq` (the heavier `ForestIdx` reconstruction, untouched);
* **forward outer** — closed to the compatibility leaves (bodies 188/185/180, documented above);
* **backward outer** — the three sector bridges (bodies 170/171/172), proved up to `choice_tag_trichotomy` (body-173);
* **sector bridge internals** — the `componentToRight` / `componentToForest` round-trips, `representedInQuotient`;
* **pairwise disjointnesses** (body-158) and the **carrier closure** (body-159);
* **region classifiers** (bodies 150/151/152) and the non-region base (contract `vertices_eq`, measure,
  star/global-gap kernel, survivor/remnant Inj/Gen, `carrier_isProperForest` / `rep` / `selectedOuter_mem`).

So the backward-choice `HEq` is retired to `forest_value_eq`; the next front is the **`forest_value_eq` scout** — the
choice-value de-contraction relating `recoverChoice`'s `forestTag` on a forward image to `q`'s original forest index.

### R-6c bodies 196–200 — the backward-choice closed to a forest parent recovery (2026-07-06)

Bodies 196–200 drive the backward-choice residual all the way down to a single homogeneous geometry leaf — the
milestone `body-200`.

```text
196  forest_value_eq split — recoverChoice tag pinning (body-188 pattern) + forestTag_forward_eq
       (forestTag_fwd = B, the genuinely fresh forward-forest coherence).
197  forward-quotient recovery scout — verdict: forestTag_forward_eq and forward_quotient_heq are DUAL siblings
       (domain q vs codomain z), NOT the same leaf; attack separately (they share only the remnant kernel).
198  forestTag_forward_eq reduced — Sum.inr.inj ⟹ forest_choiceAt_eq (q.2 γ = inr forestTag_fwd).
199  backward-choice final leaf — the whole backward_choice_heq chain (198 → 196 → 194 → 193 → 164) supplied by
       forest_choiceAt_eq + the reused tags / bridges / index transport.
200  occurrence recovery — forest_choiceAt_eq PROVED: a forest-region component γ is the parent of a recovered
       occurrence occ (carrying occ.hchoice : choiceAt q occ.γ = inr occ.B for free); with the fielded
       parent_recovered : occ.γ = γ, heq_transport_choice (cases the parent Eq, then occ.hchoice) closes it.
```

**Canonical chain.**

```text
200 → 198 → 196 → 194 → 193 → 164 → 160 → 154 → 147 → witnessSplit → coassoc_gen
```

**The remaining backward-choice geometry** is no longer an `HEq` or a choice-value abstraction — it is the
homogeneous **parent recovery**

```text
parent_recovered : occ.γ = γ
```

an `Eq` of outer components (the forward round-trip parent identity), plus the occurrence construction.

**Residual (the honest floor now):**

* **backward-choice** — the single homogeneous `parent_recovered` (`occ.γ = γ`) + the occurrence construction;
* **forward-quotient** — `forward_quotient_heq` (the dual, heavier `ForestIdx` reconstruction, untouched);
* **forward outer** — closed to the compatibility leaves (bodies 188/185/180);
* **backward outer** — the three sector bridges (bodies 170/171/172), proved up to `choice_tag_trichotomy` (body-173);
* **sector bridge internals** — the `componentToRight` / `componentToForest` round-trips, `representedInQuotient`;
* **pairwise disjointnesses** (body-158) and the **carrier closure** (body-159);
* **region classifiers** (bodies 150/151/152) and the non-region base (contract `vertices_eq`, measure,
  star/global-gap kernel, survivor/remnant Inj/Gen, `carrier_isProperForest` / `rep` / `selectedOuter_mem`).

So the backward-choice is closed to the forest parent recovery; the next front is the **`parent_recovered` scout** —
the sector forest round-trip (`componentToForest (fwdMap q)` recovering the original `γ`, i.e. occurrence parent
injectivity).

### R-6c bodies 202–208 — all four round-trips reduced to local bridges (2026-07-06)

Bodies 202–208 drive the last two round-trip leaves — the backward-choice `parent_recovered` and the
forward-quotient `HEq` — down to local sector bridges, so **all four round-trip obligations of the resolved
coassociativity backward map now consume only local sector / compatibility bridges**.

```text
backward outer    170/171/172 + 173     floor: three sector bridges + choice_tag_trichotomy (proved)
forward outer     190                    floor: compatibility leaves (188/185/180) + region constructions
backward choice   202 → 200 → 199        floor: parent_recovered = rfl from the forest bridge (171)
forward quotient  206/207 → 208          floor: survivor_mem + remnant_mem (the duals of 170/171)
```

**Backward choice (bodies 202/200/199).**  `parent_recovered : occ.γ = γ` **collapses to `rfl`** — the recovered
forest-choice occurrence is read straight off body-171's `forestRecovered_forward_membership` witness, so its
parent is definitionally `γ`.  The whole backward-choice `HEq` (through `heq_of_index_eq`, the tag cases, and the
occurrence) rests on the three sector bridges.

**Forward quotient (bodies 203–208).**  The `HEq` of two `ForestIdx` over different contract-with-stars graphs
reduces (via `heq_forestIdx` + the already-proved ambient transport `selectedOuter_partition`) to a `HEq` of the
component Finsets, then (via `heq_of_membership_split` / `heq_finset_of_mem_iff` + the `union_eq` survivor ⊔ remnant
split and the star `filter` split) to the two membership bridges `survivor_mem` / `remnant_mem` — the recovered-side
survivor / remnant sector bridges, duals of bodies 170/171.

**Canonical chains.**

```text
backward choice   202 → 200 → 198 → 196 → 194 → 193 → 164 → 160 → 154 → 147 → witnessSplit → coassoc_gen
forward quotient  208 → 206/207 → 204 → 203 → 165 → 160 → 154 → 147 → witnessSplit → coassoc_gen
```

**Main statement.**  The `witnessSplit` round-trip proof-shape is complete: all four round-trip obligations now
consume only local sector / compatibility bridges — no global `HEq` or `Sigma` proof-shape remains.

**Residual (the honest floor now):**

* **sector bridge internals** — the left / right / forest bridges (bodies 170/171/172, `componentToRight` /
  `componentToForest` round-trips) and the recovered-side `survivor_mem` / `remnant_mem` (bodies 206/207);
* **forward compatibility** — `forestTag` / `recoverChoice_forest_eq` / `promote_collapse` (body-188),
  `forestComponentMem` (body-185), `represented_cases` (body-180);
* **pairwise disjointnesses** (body-158) and the **carrier closure** (body-159);
* **region classifiers** (bodies 150/151/152) and the non-region base (contract geometry `vertices_eq`, measure,
  survivor/remnant `Inj`/`Gen`, `carrier_isProperForest` / `rep` / `selectedOuter_mem`).

So the round-trip proof-shape is entirely closed to local bridges; the next front is the **sector bridge internals**,
starting with the lighter survivor / right side (`survivor_mem` / `rightRecovered_forward_membership`), leaving the
heavier remnant / forest side for later.

### R-6c bodies 210–211 — the right / survivor sector bridge floor (2026-07-07)

Bodies 210/211 open the lighter right / survivor sector bridge.  Body-210 (scout) found the two right leaves are
*dual but not identical*; body-211 reduced the survivor leaf to a single image correspondence.

```text
210  right sector scout — rightRecovered_forward_membership (170) and survivor_mem (206) are DUAL, not identical:
       rightRecovered_forward_membership = G-level, backward componentToRight (δ ↦ G-parent)
       survivor_mem                      = quotient-level, forward survivorComponent = survivorReembed
     opposite halves of one right-sector round-trip, over different graphs — no shared provider (attack separately).
     The abstract sector-index right inverse (right_left_inv / right_right_inv, ResolvedRightSectorEquivSupply) is
     already proved and underlies leaf 170.

211  survivor_mem reduction — rightDomain_mem_iff (Finset.mem_filter) proved; rightSurvivorForest_elements rfl;
     survivor_mem reduced (via body-206's heq_finset_of_mem_iff) to survivor_image_correspondence.
```

**The survivor-side residual.**

```text
survivor_image_correspondence :
  x₁ ∈ rightComponents(recovered).attach.image survivorComponent   -- recoverChoice z γ = inl false, reembedded
    ↔ x₂ ∈ z.2.1.elements ∧ Disjoint x₂.vertices (starOfZ z)        -- star-avoiding components of B
  (with survivorReembed_toResolvedFeynmanGraph = rfl — vertices preserved; the pure inl-false ⟷ star-avoid tag)
```

**Residual (the honest floor now):**

* **survivor side** — `survivor_image_correspondence` (body-211, the `inl false` ⟷ star-avoiding tag correspondence);
* **right / G side** — `rightRecovered_forward_membership` (body-170, the G-level `componentToRight` round-trip);
* **remnant / forest side** — `remnant_mem` (body-207) and `forestRecovered_forward_membership` (body-171), the
  heavier de-contraction bridges;
* **forward compatibility** — `forestTag` / `recoverChoice_forest_eq` / `promote_collapse` (body-188),
  `forestComponentMem` (body-185), `represented_cases` (body-180);
* **pairwise disjointnesses** (body-158) and the **carrier closure** (body-159);
* **region classifiers** (bodies 150/151/152) and the non-region base (contract geometry, measure, survivor/remnant
  `Inj`/`Gen`, `carrier_isProperForest` / `rep` / `selectedOuter_mem`).

So the survivor side is down to a tag correspondence and the right / G side to a `componentToRight` round-trip; the
next front is the **`rightRecovered_forward_membership`** (body-170) — the G-level right side, where the already-proved
`rightEquiv` / sector inverse may apply — leaving the heavier remnant / forest side for later.

### R-6c bodies 210–213 — the right sector reduced to two image correspondences (2026-07-07)

Bodies 210–213 reduce **both** right-sector leaves to image correspondences.  Body-210 scouted the duality; bodies
211/213 reduced the two sides.

```text
210  scout — rightRecovered_forward_membership (170) and survivor_mem (206) are DUAL but not identical
211  survivor side — survivor_mem → survivor_image_correspondence
       x₁ ∈ rightComponents(recovered).attach.image survivorComponent ↔ x₂ ∈ rightDomain z   (survivorReembed rfl)
213  G-side — rightRecovered_forward_membership → right_image_correspondence
       γ ∈ (rightDomain (fwdMap q)).attach.image componentToRight ↔ rightPrimSelected q γ    (over a wiring bridge)
```

**The `rightEquiv` negative finding (body-213).**  The proved abstract right-sector inverse
(`ResolvedRightSectorEquivSupply.rightEquiv : RightPrimitiveIndex D G s ≃ (rightForest s).elements`,
`right_left_inv` / `right_right_inv`) does **not** directly discharge either leaf: it lives at the *sector-index /
quotient-graph* level (forward `survivorComponent`), while the region maps use *abstract `componentToRight` fields*
disconnected from it.  So the remaining right content is the correspondence between **star-avoiding quotient
components** of `B` and **`inl false` source choices** of `q` — fielded fresh on each side, not routed through
`rightEquiv`.

**Residual (the honest floor now):**

* **right sector** — `survivor_image_correspondence` (body-211) and `right_image_correspondence` (body-213), the two
  star-avoiding ⟷ `inl false` correspondences;
* **remnant / forest sector** — `remnant_mem` (body-207) and `forestRecovered_forward_membership` (body-171), the
  heavier de-contraction bridges;
* **forward compatibility** — `forestTag` / `recoverChoice_forest_eq` / `promote_collapse` (body-188),
  `forestComponentMem` (body-185), `represented_cases` (body-180);
* **pairwise disjointnesses** (body-158) and the **carrier closure** (body-159);
* **region classifiers** (bodies 150/151/152) and the non-region base (contract geometry, measure, survivor/remnant
  `Inj`/`Gen`, `carrier_isProperForest` / `rep` / `selectedOuter_mem`).

So the right sector is closed to two image correspondences; the next front is the heavier **remnant / forest sector**
(`remnant_mem` / `forestRecovered_forward_membership`), where the de-contraction may share the promotion compatibility.

### R-6c bodies 211–216 — all sector leaves reduced to image correspondences (2026-07-07)

Bodies 211/213/215/216 reduce **all four** sector bridge leaves to image correspondences — the same
`ofElements`-image + wiring / filter scaffolding on each side.

```text
survivor quotient side  body-211  survivor_image_correspondence   rightComponents image ↔ star-avoiding
right    G-side         body-213  right_image_correspondence      componentToRight image ↔ inl false
forest   G-side         body-215  forest_image_correspondence     componentToForest image ↔ inr (forestChoiceSelected)
remnant  quotient side  body-216  remnant_image_correspondence    remnantComponent image ↔ star-touching
```

**The one heavy correspondence.**  The first three are **tag / image correspondences** — the `G`-side maps are
abstract `componentToRight` / `componentToForest` fields, and the survivor `survivorReembed` preserves vertices at
`rfl`, so only the `inl false` / `inr` tag ⟷ star-avoiding / star-touching content remains.  The **remnant**
correspondence is the genuine **de-contraction** leaf: `remnantComponent` lands in the contracted graph with a
nontrivial `remnantClass_eq`, so its `HEq` bridges genuinely different vertex sets (bodies 126/183).

**Canonical connection.**

```text
survivor → 206 → 208 → forward_quotient_heq
right    → 170 → backward-outer / backward-choice floors
forest   → 171 → backward-outer / backward-choice floors
remnant  → 207 → 208 → forward_quotient_heq
```

**Residual (the honest floor now):**

* **image correspondences** — `survivor_image_correspondence` (211), `right_image_correspondence` (213),
  `forest_image_correspondence` (215) [three tag correspondences], and `remnant_image_correspondence` (216) [the one
  de-contraction correspondence];
* **forward compatibility** — `forestTag` / `recoverChoice_forest_eq` / `promote_collapse` (body-188),
  `forestComponentMem` (body-185), `represented_cases` (body-180);
* **pairwise disjointnesses** (body-158) and the **carrier closure** (body-159);
* **region classifiers** (bodies 150/151/152) and the non-region base (contract geometry, measure, survivor/remnant
  `Inj`/`Gen`, `carrier_isProperForest` / `rep` / `selectedOuter_mem`).

So the sector bridges are all four image correspondences; the next front is to bundle the three light tag
correspondences, leaving the single heavy `remnant_image_correspondence` (the de-contraction) for a focused attack.

### R-6c bodies 219–222 — the sector correspondences reduced to sound / complete directions (2026-07-07)

Bodies 219–222 reduce **all four** sector image correspondences to two `Finset.mem_image` directions each — a uniform
`sound` / `complete` proof-shape.  Body-218's scout established the three tag correspondences do not bundle, so each is
attacked separately; the reduction scaffolding is nonetheless identical.

```text
right     body-219  right_sound    / right_complete      componentToRight  round-trip ↔ inl false     (G-side, no HEq)
forest    body-220  forest_sound   / forest_complete     componentToForest round-trip ↔ inr B         (G-side, no HEq)
survivor  body-221  survivor_sound / survivor_complete   survivorComponent round-trip ↔ star-avoiding (quotient, HEq)
remnant   body-222  remnant_sound  / remnant_complete    remnantComponent  round-trip ↔ star-touching (quotient, HEq, de-contraction)
```

**Main statement.**  All four sector image correspondences now have the same proof-shape: `image correspondence =
sound + complete`, proved by term-mode `Finset.mem_image.mp` / `.mpr` (the `@[simp]` form does not fire through `simp`
due to a `DecidableEq` instance mismatch), with the quotient-side pair (survivor / remnant) carrying the cross-graph
`HEq` closed by `eq_of_heq`.  The only heavy pair is **remnant**, whose directions carry genuine de-contraction
geometry (`remnantComponent` into the contracted graph, `remnantClass_eq`); the other three are tag round-trips.

**Canonical links.**

```text
right / forest    → backward-outer and backward-choice floors (bodies 170/171)
survivor / remnant → forward-quotient floor (bodies 206/207 → 208)
```

**Residual (the honest floor now):**

* **eight sector `sound` / `complete` directions** — `right_sound` / `right_complete` (219), `forest_sound` /
  `forest_complete` (220), `survivor_sound` / `survivor_complete` (221), `remnant_sound` / `remnant_complete` (222);
* **forward compatibility** — `forestTag` / `recoverChoice_forest_eq` / `promote_collapse` (body-188),
  `forestComponentMem` (body-185), `represented_cases` (body-180);
* **pairwise disjointnesses** (body-158) and the **carrier closure** (body-159);
* **region classifiers** (bodies 150/151/152) and the non-region base (contract geometry, measure, survivor/remnant
  `Inj`/`Gen`, `carrier_isProperForest` / `rep` / `selectedOuter_mem`).

So the sector bridge layer's proof-shape is uniform (eight `sound` / `complete` directions); the next front is the
**deeper sector-inverse wiring** — starting with the lightest G-side `right_sound` / `right_complete`, where the
already-proved `right_surj` / `right_left_inv` / `right_right_inv` may apply.

### R-6c body 224 — the sector-inverse wiring stops at the abstract-region floor (2026-07-07)

Body-224 (scout) tested whether the eight sector `sound` / `complete` directions can be discharged by wiring the
abstract region maps (`componentToRight` / `componentToForest`) to the already-proved sector inverse (`rightEquiv` /
`right_surj` / `right_left_inv` / `right_right_inv`).  **They cannot** — three mismatches make the sector inverse the
wrong tool:

```text
Sector inverse is NOT the next reduction path.
- The region maps componentToRight / componentToForest are ABSTRACT FIELDS
  (only rightComponentCD / rightComponentDisjoint), and ResolvedRegionConstructionFromSectorSupply is NEVER
  instantiated — so right_surj / componentToRight_spec cannot even be named in a proof about them.
- The sector index over fwdMap q gives a parent in (selectedOuterOf q).1 (the recovered / left-factor outer),
  NOT q.1.1 (the original domain outer); no lemma equates them.
- The sector inl-false / inr tag is over fwdMap q's recoverChoice-derived structure, NOT q.2.
Therefore the eight sound/complete leaves are the honest floor for the ABSTRACT region construction;
discharging them (not just fielding) requires concretizing the whole region construction (region/recoverChoice layer).
```

So the **sector-inverse route is retired / saturated**: no further abstract reduction of the sector bridges is
available without concretizing the region maps.

**Residual (the honest floor now):**

* **sector / round-trip — floor reached** — the eight `sound` / `complete` directions (bodies 219–222); no further
  abstract reduction via the sector inverse;
* **forward compatibility (reducible candidate)** — `forestTag` / `recoverChoice_forest_eq` / `promote_collapse`
  (body-188), `forestComponentMem` (body-185), `represented_cases` (body-180);
* **disjoint / carrier (reducible candidate)** — the pairwise disjointnesses (body-158) and the recovered-outer
  carrier closure (body-159);
* **non-region base** — contract geometry, measure, survivor/remnant `Inj`/`Gen` providers, `carrier_isProperForest`
  / `rep` / `selectedOuter_mem`.

So the round-trip and sector layers are fully mapped to their floors; the next front is the **disjoint / carrier**
candidates (bodies 158/159), which may still admit a shallow provider reduction — leaving the deeper forward
compatibility and the non-region base for later.

### R-6c bodies 226–228 — canonical carrier grounding begins (`carrier_isProperForest` proved) (2026-07-09)

Bodies 226/227 (scouts) tested the disjoint / carrier candidates, and body-228 (proof) grounded the one genuine win.

```text
226 scout: recovered-outer disjoint (158) + carrier closure (159) are BOTH abstract floor vs arbitrary D.
  - 158's three cross-disjointnesses are RAW FIELDS (representedInQuotient is an opaque abstract Prop, not linked
    to the componentToRight/Forest images; A's own disjoint is itself a fielded primitive).
  - 159's recovered_outer_mem ≡ selectedOuter_mem (128): D.carrier is abstract (no proper-forest/union/closure).

227 scout: instantiating D to the CANONICAL carrier is a REPACKAGING, not a discharge.
  - mem_properDisjointAdmissibleDivergentSubgraphs re-expresses ∈ carrier as IsProperForest ∧ disjoint ∧ ….
  - For a CONSTRUCTED object (selectedOuterRawOf, region union, the 3 regions) that obligation is the properness /
    disjointness of the construction — loops back to the abstract componentToRight/promote geometry.
  - Only carrier_isProperForest (137) is a genuine free win. No canonical D exists yet; it must be constructed.

228 proof: ResolvedCanonicalCarrierProperSupply (wrapper) + .toData + .toCarrierProperProvider.
  index : (G) → ResolvedProperForestFiniteIndex G   -- carrier + mem_proper (ResolvedCoproduct.lean:172)
  carrier G := (index G).carrier
  carrier_isProperForest := fun G A hA => (index G).mem_proper A hA   -- PROVED, not a field
```

**The finding that matters:** the canonical carrier is **not merely repackaging** — it genuinely discharges
`carrier_isProperForest` (137). But `selectedOuter_mem` (128) / `recovered_outer_mem` (159) membership still requires
proving the *constructed* objects (`selectedOuterRawOf`, the region union) are proper / disjoint / admissible; the
region cross-disjointnesses (158) likewise. Those stay construction-specific.

**Status table (the four closure floor leaves):**

```text
carrier_isProperForest   grounded by 228 (proved from ResolvedProperForestFiniteIndex.mem_proper)
selectedOuter_mem        construction-specific (constructed object must be a canonical member)
region cross-disjoint    construction-specific (3 regions must be pieces of one member / representedInQuotient concrete)
recovered_outer_mem      construction-specific (constructed region union must be a canonical member)
```

**Residual (refreshed):**

* **grounded** — `carrier_isProperForest` (body-228, via the proper-forest finite index);
* **still construction-specific** — `selectedOuter_mem` (128), `recovered_outer_mem` (159), the region pairwise
  disjointnesses (158) — all reduce to the constructed regions being canonical members (proper / disjoint / admissible);
* **other floors** — the eight sector `sound` / `complete` directions (bodies 219–222), forward compatibility
  (`forestTag` / `promote_collapse` 188, `forestComponentMem` 185, `represented_cases` 180), and the non-region base
  (contract geometry, measure, survivor/remnant `Inj`/`Gen`, `rep`, and the heavy canonical fields `index` / `starOf`
  / `hCD` / `mapPerm` naturalities).

The canonical-instance phase has begun: the next front is a **`mem_rewrite` adapter** that reshapes `selectedOuter_mem`
/ `recovered_outer_mem` from carrier membership into "the constructed forest is proper / disjoint / admissible" — a
reshaping (not a proof) that puts the residual obligations into canonical form.

### R-6c bodies 230–233 — canonical membership route established (2026-07-10)

The `mem_rewrite` adapter is now built and connected: `selectedOuter_mem` (128) and `recovered_outer_mem` (159) are
supplied from membership certificates.

```text
230  scout:  membership = isProper + canonical/section, NOT isProper alone.
     Resolved-index forget_complete gives EXISTENCE only; forget is not globally injective, so the constructed
     forest's identity must be supplied (the section condition A = ofForgetForest A.forget).

231  forget_union_elements (PROVED, infra):
     (A.union B).forget.elements = A.forget.elements ∪ B.forget.elements    (simp: union_elements + forget_elements
     + Finset.image_union). The tool for building certificates on the constructed unions.

232  ResolvedCanonicalMembershipCertificate (C : ResolvedProperForestFiniteCover G) (A):
       isProper     : A.IsProperForest
       recovered_eq : ∀ Ares ∈ C.index.carrier, Ares.forget = A.forget → Ares = A   (section, generic form)
     cert_mem (PROVED) : certificate → A ∈ C.index.carrier
       (forget_complete recovers Ares sharing A's forget; recovered_eq identifies it with A).

233  ResolvedCanonicalCarrierWiring D { cover ; carrier_eq : D.carrier G = (cover G).index.carrier }:
       .selectedOuterMem      (PROVED) : ∀ s, cert (selectedOuterRawOf s) → selectedOuter_mem (128)
       .recoveredOuterSupply  (PROVED) : ∀ z, cert (region union) → ResolvedRecoveredOuterCarrierSupply (159)
```

**The route:**

```text
forget_union infra (231)
  → certificate fields  isProper + recovered_eq  (232)
  → cert_mem                                     (232)
  → selectedOuter_mem / recovered_outer_mem      (233, via carrier_eq)
```

**Status table (the four closure floor leaves):**

```text
carrier_isProperForest   grounded by 228 (proved from ResolvedProperForestFiniteIndex.mem_proper)
selectedOuter_mem        reduced to selectedOuter_cert + carrier_eq (body-233)
recovered_outer_mem      reduced to recoveredOuter_cert + carrier_eq (body-233)
region cross-disjoint    still construction-specific (158)
```

**Residual (refreshed):**

* **grounded** — `carrier_isProperForest` (body-228);
* **certificate fields (the new residual for 128/159)** — `isProper` (five `IsProperForest` conjuncts) and
  `recovered_eq` (the section condition), each per constructed forest; plus the `carrier_eq` canonical-`D` wiring;
* **still construction-specific** — the region pairwise disjointnesses (158);
* **other floors** — the eight sector `sound` / `complete` directions (bodies 219–222), forward compatibility
  (`forestTag` / `promote_collapse` 188, `forestComponentMem` 185, `represented_cases` 180), and the non-region base
  (contract geometry, measure, survivor/remnant `Inj`/`Gen`, `rep`, and the heavy canonical fields).

The next front is to **fill a certificate field** — the first `IsProperForest` conjunct (e.g. `IsNonempty`) for
`selectedOuterRawOf` / the region union, using `forget_union_elements` — reached via an `IsProper conjunct` scout that
picks the conjunct that falls first.

---

*Keep this file in sync with the Lean source line numbers when the kernels move.
Reader-facing narrative lives in `CK_HOPF_FORMALIZATION_MAP.md`; do not duplicate
sprint logs here.*
