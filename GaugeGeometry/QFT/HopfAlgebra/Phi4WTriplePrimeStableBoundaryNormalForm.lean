import GaugeGeometry.QFT.HopfAlgebra.Phi4WTriplePrimeEdgeCompleteCarrier
import GaugeGeometry.QFT.HopfAlgebra.Phi4WTriplePrimeLeftFactorProduct

/-!
# QFT-R1-body-626 — stable boundary NORMAL FORM: an OWNERSHIP AUDIT (verdict = single Prop record)

Body-625 proved a genuine **class-level no-go** (`…_nestedLeft_class_ne_of_inheritedOuter`): the FOREST
left factor's naive nested completion `δ.boundaryCompletedResolvedGraph` does NOT match the promoted
branch's root-direct `(rootRelativeInner γ δ).boundaryCompletedResolvedGraph` at the resolved-class level.
An inherited outer boundary leg is re-encoded EVEN locally (`existingLegId ℓ = 4·e+2`) but stays ODD at
root (`boundaryLegId e = 2·e+1`); the `legId` profile is a `mapPerm`-invariant, so no relabeling reconciles
them and the two generators differ.  The physics content: *a first-order-correct rigidification that is not
idempotent under iteration breaks coassociativity.*

The chosen repair (a body-627+ construction) is a **stable / idempotent completion parallel carrier**:
normalize external-leg IDs ONCE at root entry; on completion keep inherited external legs VERBATIM and give
a fresh boundary ID only to genuinely new cut edges.  The target law is the raw graph equality
`stableComplete (stableComplete γ) δ = stableComplete (rootRelativeInner γ δ)`.

**This body is an AUDIT, NOT a construction.**  Its whole value is to establish — honestly, from EXISTING
assets — the minimal ownership the 627+ carrier needs, so that construction is de-risked.  It emits NO
coproduct, NO Hopf carrier, NO instance.  It emits exactly ONE `Prop` ownership record and its discharge
theorem, plus one observational item-8 anchor.  Body-625's no-go is left standing untouched (it is imported
as the live witness of *why* this normal form is needed).

## The eight audited items

1. **TYPE of the root-once normalizer.**  The root-entry external-leg-ID normalization is
   `ResolvedFeynmanSubgraph.boundaryCompletedResolvedGraph : ResolvedFeynmanSubgraph G → ResolvedFeynmanGraph`
   (body-589): it re-encodes existing legs into the EVEN `existingLegId` namespace and induces the fresh cut
   legs into the ODD `boundaryLegId` namespace, ONCE.  The nested-stable variant that keeps inherited legs
   verbatim is `stableNestedBoundaryCompletedGraph γ δ` (body-597), same output TYPE `ResolvedFeynmanGraph`.
   The "normalize once" TYPE is therefore *owned*: `ResolvedFeynmanSubgraph G → ResolvedFeynmanGraph`.
2. **Condition to KEEP inherited legs without re-encoding.**  Membership `e ∈ inheritedOuter γ δ`; on it the
   root leg and the inner leg literally coincide — `γ.boundaryExternalLeg e = (rootRelativeInner γ δ)
   .boundaryExternalLeg e` — so keeping verbatim IS the root completion's own leg.  ONLY
   `newRootBoundary γ δ` receives a fresh ODD id.
3. **Unique edge-origin traceability of new boundary legs.**  Each fresh root-boundary leg has a UNIQUE
   originating boundary edge of `R := rootRelativeInner γ δ`, gated by root `G.EdgeIdsUnique`.
4. **`EdgeIdsUnique` / `LegIdsUnique`.**  The stable normal form has unique edge ids (internal edges = `δ`'s,
   unchanged from ambient `G`) and unique leg ids (EVEN×EVEN via `LegIdsUnique`, ODD×ODD via `EdgeIdsUnique`,
   cross by parity).
5. **`mapPerm` coherence.**  The stable normal form commutes with the identity-preserving vertex relabeling
   `mapPerm σ`.
6. **Closure — the graph STAYS in the same normal form.**  The stable nested completion of `δ` (nested in the
   once-normalized `γ.boundaryCompletedResolvedGraph`) is RAW-equal to the single root completion of the lift
   `R`; and under vertex-induced internal-edge completeness the induced root boundary splits cleanly
   `R.resolvedBoundaryEdges = inheritedOuter γ δ + δ.resolvedBoundaryEdges` (no hidden root boundary), so
   re-completion invents nothing — the normal form is stable under iteration.
7. **Correspondence table (item 7).**

   | ownership field                     | item | discharged by (EXACT theorem)                                        | body |
   |-------------------------------------|------|----------------------------------------------------------------------|------|
   | `keep_inherited_verbatim`           | 2    | `boundaryExternalLeg_agree_on_inherited`                             | 597  |
   | `legs_eq_single_root`               | 2,6  | `stableNestedResolvedExternalLegs_eq`                               | 597  |
   | `normal_form_closed`                | 6    | `stableNestedBoundaryCompletedGraph_eq`                             | 597  |
   | `new_boundary_traceable`            | 3    | `stableNestedRootBoundaryLegs_traceable`                           | 598  |
   | `edgeIds_unique`                    | 4    | `stableNestedBoundaryCompletedGraph_edgeIdsUnique`                 | 598  |
   | `legIds_unique`                     | 4    | `stableNestedBoundaryCompletedGraph_legIdsUnique`                  | 598  |
   | `mapPerm_coherent`                  | 5    | `stableNestedBoundaryCompletedGraph_mapPerm`                       | 598  |
   | `boundary_split_of_edgeComplete`    | 6    | `rootRelativeInner_resolvedBoundaryEdges_eq_of_edgeComplete`        | 600  |

   The TYPE of item 1 and the reason of item 8 are documentation observations (item 1 = the shared output
   type `ResolvedFeynmanSubgraph G → ResolvedFeynmanGraph`; item 8 below); item 8 additionally carries the
   machine-checked anchor `resolvedGeneratorProperty_forgets_ids`.

8. **TYPE AUDIT — the unrestricted `ResolvedPhi4HopfGen` CANNOT recover this owner.**
   `ResolvedPhi4HopfGen = ResolvedHopfGenFor phi4… = { c : ResolvedFeynmanGraphClass // c
   .IsConnectedDivergentFor phi4… }` (body-584).  It carries EXACTLY two things: an id-preserving *class*
   `c : ResolvedFeynmanGraphClass` (a `mapPerm`-iso quotient — no raw representative, hence no
   normal-form/leg-ID field at all) and a proof of `IsConnectedDivergentFor`.  By definition (body-584)
   `ResolvedFeynmanGraphClass.IsConnectedDivergentFor D Inv c = FeynmanGraphClass.IsConnectedDivergentFor D
   Inv c.toFlatClass`, i.e. the ONLY carried property reads the FORGOTTEN (flat) class `c.toFlatClass`, in
   which every `edgeId` / `legId` — and therefore the entire EVEN/ODD `existingLegId`/`boundaryLegId`
   normal form — has been dropped.  So the generator is structurally *blind* to the leg-ID encoding the
   stable normal form is ABOUT; there is no field in which "already normalized at root entry" could live.
   Worse, body-625's `…_nestedLeft_class_ne_of_inheritedOuter` shows the naive-local key
   `δ.boundaryCompletedResolvedGraph.toResolvedClass` and the stable-root key
   `(rootRelativeInner γ δ).boundaryCompletedResolvedGraph.toResolvedClass` are DISTINCT generators with no
   selector between them — so the generator layer cannot even *identify* the normal form, let alone certify
   it.  Conclusion: the owner MUST be a separate parallel record on the raw
   `stableNestedBoundaryCompletedGraph` (this body), NOT a refinement of `ResolvedPhi4HopfGen`.  The
   item-8 anchor `resolvedGeneratorProperty_forgets_ids` records the load-bearing defeq.

## Verdict

A **single `Prop` ownership record** `StableBoundaryNormalFormOwnership γ δ` with all eight fields
DETERMINED and each discharged by a named body-597 / 598 / 600 theorem
(`stableBoundaryNormalFormOwnership_holds`, unconditional — every ambient hypothesis is internalized as a
field antecedent).  No fields were left undetermined, so this is NOT a docstring-only STOP.

## HALT compliance
NO coproduct / Hopf carrier / instance emitted; the FROZEN `coproduct_resolved_edgeComplete_phi4` /
`ResolvedPhi4HopfH` and every existing file are untouched.  EXACTLY ONE new `structure`, and it is
`Prop`-valued.  Body-625's no-go is neither erased nor circumvented (no quotient, no vertex correcting
permutation, no `forget`-flattening); the record NEVER identifies body-597's `stableNestedBoundaryCompletedGraph`
with the naive `δ.boundaryCompletedResolvedGraph` / old `localLeftFactor` — every equation targets only
`(rootRelativeInner γ δ).boundaryCompletedResolvedGraph`.  No flat descent; no right factor / `quot_eq`.
Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); ZERO forbidden divergence classes in any
declaration TYPE; NO public `HEq` / `cast` / `▸`; NO `sorry` / `admit` / `native_decide`.  No new
`class` / `instance` (no divergence-measure local instance was needed — the record is purely combinatorial).
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

open ResolvedFeynmanSubgraph

variable {G : ResolvedFeynmanGraph}

/-! ## Item 8 anchor — the generator property forgets ids -/

/-- **body-626 (item 8, TYPE-AUDIT anchor).**  The ONLY property a `ResolvedHopfGenFor D Inv` generator
carries factors, *by definition* (body-584), through `toFlatClass` — the id-forgetting map.  Hence the
generator (and its φ⁴ specialization `ResolvedPhi4HopfGen`) is structurally blind to the `edgeId` / `legId`
encoding, so it cannot host the stable-boundary normal-form ownership; that owner must be a separate
parallel record on the raw completed graph (this file).  `rfl` — this IS the defeq. -/
theorem resolvedGeneratorProperty_forgets_ids
    (D : DivergenceMeasureFamily) (Inv : PermInvariantDivergenceMeasureFamily D)
    (c : ResolvedFeynmanGraphClass) :
    ResolvedFeynmanGraphClass.IsConnectedDivergentFor D Inv c
      = FeynmanGraphClass.IsConnectedDivergentFor D Inv c.toFlatClass := rfl

/-! ## The single Prop ownership record -/

/-- **body-626 — stable boundary NORMAL-FORM ownership record.**  The minimal ownership a body-627+ stable /
idempotent completion carrier for the occurrence `(γ, δ)` must satisfy, audited BEFORE construction.  Every
field is a `Prop` whose ambient hypotheses are internalized as antecedents (so the record itself is
unconditional), and each is discharged by a named body-597 / 598 / 600 theorem (see the correspondence
table in the module docstring).  Emitting this record is an AUDIT: it neither builds nor keys a coproduct /
Hopf generator, and it NEVER equates the stable graph with the naive `δ.boundaryCompletedResolvedGraph`. -/
structure StableBoundaryNormalFormOwnership (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph) : Prop where
  /-- **Item 2 (597 `boundaryExternalLeg_agree_on_inherited`).**  On an inherited outer boundary edge the
  root leg and the inner leg coincide — so keeping the inherited leg VERBATIM already reproduces the single
  root completion's own leg; no re-encoding is needed or permitted. -/
  keep_inherited_verbatim : ∀ e, e ∈ inheritedOuter γ δ →
    γ.boundaryExternalLeg e = (rootRelativeInner γ δ).boundaryExternalLeg e
  /-- **Item 2 / 6 (597 `stableNestedResolvedExternalLegs_eq`).**  Under both saturations the stable nested
  legs (inherited verbatim + fresh root boundary) equal the single root completion's leg multiset. -/
  legs_eq_single_root : ResolvedExternalLegSaturated G γ →
    ResolvedExternalLegSaturated γ.boundaryCompletedResolvedGraph δ →
    stableNestedResolvedExternalLegs γ δ
      = (rootRelativeInner γ δ).boundaryCompletedResolvedExternalLegs
  /-- **Item 6 (597 `stableNestedBoundaryCompletedGraph_eq`).**  The headline closure: the stable nested
  completion is RAW-equal to the single root completion of the lift `R = rootRelativeInner γ δ` — the exact
  idempotent-completion law `stableComplete (stableComplete γ) δ = stableComplete (rootRelativeInner γ δ)`. -/
  normal_form_closed : ResolvedExternalLegSaturated G γ →
    ResolvedExternalLegSaturated γ.boundaryCompletedResolvedGraph δ →
    stableNestedBoundaryCompletedGraph γ δ
      = (rootRelativeInner γ δ).boundaryCompletedResolvedGraph
  /-- **Item 3 (598 `stableNestedRootBoundaryLegs_traceable`).**  Each fresh root-boundary leg traces back to
  a UNIQUE resolved boundary edge of `R`, gated by root `G.EdgeIdsUnique`. -/
  new_boundary_traceable : G.EdgeIdsUnique → ∀ ℓ, ℓ ∈ stableNestedRootBoundaryLegs γ δ →
    ∃! e, e ∈ (rootRelativeInner γ δ).resolvedBoundaryEdges
      ∧ (rootRelativeInner γ δ).boundaryExternalLeg e = ℓ
  /-- **Item 4 (598 `stableNestedBoundaryCompletedGraph_edgeIdsUnique`).**  The stable normal form has unique
  edge ids. -/
  edgeIds_unique : ResolvedExternalLegSaturated G γ →
    ResolvedExternalLegSaturated γ.boundaryCompletedResolvedGraph δ → G.EdgeIdsUnique →
    (stableNestedBoundaryCompletedGraph γ δ).EdgeIdsUnique
  /-- **Item 4 (598 `stableNestedBoundaryCompletedGraph_legIdsUnique`).**  The stable normal form has unique
  leg ids (EVEN×EVEN via `LegIdsUnique`, ODD×ODD via `EdgeIdsUnique`, cross by parity). -/
  legIds_unique : ResolvedExternalLegSaturated G γ →
    ResolvedExternalLegSaturated γ.boundaryCompletedResolvedGraph δ → G.LegIdsUnique → G.EdgeIdsUnique →
    (stableNestedBoundaryCompletedGraph γ δ).LegIdsUnique
  /-- **Item 5 (598 `stableNestedBoundaryCompletedGraph_mapPerm`).**  The stable normal form commutes with
  the identity-preserving vertex relabeling `mapPerm σ`. -/
  mapPerm_coherent : ResolvedExternalLegSaturated G γ →
    ResolvedExternalLegSaturated γ.boundaryCompletedResolvedGraph δ → ∀ σ : Equiv.Perm VertexId,
    stableNestedBoundaryCompletedGraph (γ.mapPerm σ) (mapPermNestedBoundarySubgraph σ γ δ)
      = (stableNestedBoundaryCompletedGraph γ δ).mapPerm σ
  /-- **Item 6 (600 `rootRelativeInner_resolvedBoundaryEdges_eq_of_edgeComplete`).**  Under vertex-induced
  internal-edge completeness the induced root boundary splits cleanly (NO hidden root boundary), so the
  normal form is stable under iteration — re-completion invents nothing. -/
  boundary_split_of_edgeComplete : ResolvedInternalEdgeComplete γ →
    (rootRelativeInner γ δ).resolvedBoundaryEdges = inheritedOuter γ δ + δ.resolvedBoundaryEdges

/-- **body-626 (HEADLINE) — the stable boundary normal-form ownership record HOLDS for every occurrence.**
Unconditional: each field's ambient hypotheses are its own antecedents, so every guarantee is discharged
directly by its named body-597 / 598 / 600 theorem.  This is the audited ownership the body-627+ stable /
idempotent completion carrier may assume — established WITHOUT emitting any coproduct, carrier, or
instance, and WITHOUT erasing body-625's no-go. -/
theorem stableBoundaryNormalFormOwnership_holds (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph) :
    StableBoundaryNormalFormOwnership γ δ where
  keep_inherited_verbatim := fun _e he => boundaryExternalLeg_agree_on_inherited γ δ he
  legs_eq_single_root := fun hγsat hδsat => stableNestedResolvedExternalLegs_eq γ δ hγsat hδsat
  normal_form_closed := fun hγsat hδsat => stableNestedBoundaryCompletedGraph_eq γ δ hγsat hδsat
  new_boundary_traceable := fun hEdge _ℓ hℓ => stableNestedRootBoundaryLegs_traceable γ δ hEdge hℓ
  edgeIds_unique := fun hγsat hδsat hEdge =>
    stableNestedBoundaryCompletedGraph_edgeIdsUnique γ δ hγsat hδsat hEdge
  legIds_unique := fun hγsat hδsat hLeg hEdge =>
    stableNestedBoundaryCompletedGraph_legIdsUnique γ δ hγsat hδsat hLeg hEdge
  mapPerm_coherent := fun hγsat hδsat σ =>
    stableNestedBoundaryCompletedGraph_mapPerm σ γ δ hγsat hδsat
  boundary_split_of_edgeComplete := fun hEC =>
    rootRelativeInner_resolvedBoundaryEdges_eq_of_edgeComplete γ δ hEC

end GaugeGeometry.QFT.Combinatorial
