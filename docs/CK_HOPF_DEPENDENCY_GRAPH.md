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

*Keep this file in sync with the Lean source line numbers when the kernels move.
Reader-facing narrative lives in `CK_HOPF_FORMALIZATION_MAP.md`; do not duplicate
sprint logs here.*
