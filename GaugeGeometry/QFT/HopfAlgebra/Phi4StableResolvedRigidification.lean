import GaugeGeometry.QFT.HopfAlgebra.Phi4WTriplePrimeStableBoundaryNormalForm

/-!
# QFT-R1-body-627 — stable resolved rigidification: root-once entry + one-step action

Body-625 proved a class-level **no-go**: the naive nested completion `δ.boundaryCompletedResolvedGraph`
re-encodes an inherited outer boundary leg EVEN locally (`existingLegId ℓ = 4·e+2`) while the root-direct
route keeps it ODD (`boundaryLegId e = 2·e+1`) — the `legId` profile is a `mapPerm`-invariant, so no
relabeling reconciles them.  That witness is promoted to a **standing design principle**, not erased.

Body-626 established the stable-completion OWNERSHIP (`StableBoundaryNormalFormOwnership`,
`stableBoundaryNormalFormOwnership_holds`, all eight fields discharged by named body-597 / 598 / 600
theorems).  This body **realizes** that normal form's ENTRY and its ONE-STEP action, consuming body-626
directly — without ever equating body-597's stable graph with body-625's naive
`δ.boundaryCompletedResolvedGraph`.

## Steps

* Step 1 `stableRootNormalize K hWF := (K.resolvedSelf hWF).boundaryCompletedResolvedGraph` — the
  root-once EVEN normalizer.  `K.resolvedSelf hWF` is the full resolved subgraph (its boundary is EMPTY,
  `resolvedSelf_resolvedBoundaryEdges`), so the external legs are EXACTLY `K.externalLegs.map
  encodeExistingLeg` — existing legs are made EVEN exactly ONCE and NO ODD leg is generated yet.  Anchors:
  vertices / internalEdges = `K`'s; the externalLegs raw equality; `forget` = `K.forget` raw equality;
  EdgeIdsUnique / LegIdsUnique; `mapPerm` coherence; WellFormed / support.
* Step 2 `phi4StableRigidifiedGraph x := stableRootNormalize (phi4RigidifiedGraph x) …` — the chosen φ⁴
  normalized rigidification.  The well-formed witness is RECOVERED from body-585/586's ambient CD owner
  (`rigidifyPhi4Gen`.property → `isConnectedDivergentFor_toResolvedClass`), NOT taken as a hypothesis.
  Victory anchor `(phi4StableRigidifiedGraph x).forget.toClass = x.val`; plus family-explicit graph CD,
  EdgeIdsUnique, LegIdsUnique.  NOT packaged into `ResolvedPhi4HopfGen`.
* Step 3 `stableBoundaryCompleteOne K hWF δ := stableNestedBoundaryCompletedGraph (K.resolvedSelf hWF) δ`
  for `δ` on the normalized root.  Its external legs are the DEFINITIONAL stable form
  `δ.externalLegs + (newRootBoundary …).map (rootRelativeInner …).boundaryExternalLeg`: inherited legs are
  kept VERBATIM; only genuinely new cut edges are ODD-ized; `encodeExistingLeg` is NOT called a second time.
* Step 4 (one-step normal form) — under external-leg saturation, consume body-626's owner DIRECTLY to emit
  the RAW GRAPH EQUALITY `stableBoundaryCompleteOne K hWF δ = (rootRelativeInner (K.resolvedSelf hWF)
  δ).boundaryCompletedResolvedGraph`.  Thin derivations: strict `forget` equality; support / WellFormed;
  new-boundary traceability; EdgeIdsUnique / LegIdsUnique; `mapPerm` coherence; the edge-complete exact
  boundary split; the class / φ⁴ graph-CD transport across the raw equality.

## Victory
chosen flat generator → unique-ID resolved representative → root-once EVEN normalization → first-order
completion with inherited IDs UNTOUCHED → RAW equality with the single-root completion.

## HALT / red lines
NO new `structure` / `class` / `instance` (only `def`s + `theorem`s; no divergence-measure local instance was
needed).  NO HopfGen / HopfH / coproduct emitted; nested idempotence is body-628 and is NOT proved here.
`δ.boundaryCompletedResolvedGraph` is NEVER called a stable completion and NEVER bridged to body-625's no-go
(it stays a standing witness); `existingLegId (boundaryExternalLeg e)` never appears on the construction
path (the forbidden second re-encoding).  NO orbit quotient / dedup / `toFinset`; NO forbidden divergence
class in any declaration TYPE; NO public `HEq` / `cast` / graph-data `▸`; ZERO `sorry` / `admit` /
`native_decide`.  Every equation targets only `(rootRelativeInner (K.resolvedSelf hWF) δ)
.boundaryCompletedResolvedGraph`.  Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

open ResolvedFeynmanSubgraph

/-! ## The full resolved subgraph (root carrier of the normalizer) -/

namespace ResolvedFeynmanGraph

/-- **body-627 — the full resolved subgraph of `K`.**  The resolved mirror of the flat
`FeynmanSubgraph.self`: same vertices / internal edges / external legs as `K`, with support read off the
forgotten well-formedness `hWF : K.forget.WellFormed` (endpoints/attachments of `K` land in `K.vertices`
because `forget` preserves them, `rfl`).  A plain `def` — no new structure/class/instance. -/
def resolvedSelf (K : ResolvedFeynmanGraph) (hWF : K.forget.WellFormed) : ResolvedFeynmanSubgraph K where
  vertices := K.vertices
  internalEdges := K.internalEdges
  externalLegs := K.externalLegs
  vertices_subset := fun _v hv => hv
  internalEdges_le := le_refl _
  externalLegs_le := le_refl _
  edges_supported := fun e he => hWF.1 e.forget (Multiset.mem_map_of_mem _ he)
  legs_supported := fun ℓ hℓ => hWF.2 ℓ.forget (Multiset.mem_map_of_mem _ hℓ)

@[simp] theorem resolvedSelf_vertices (K : ResolvedFeynmanGraph) (hWF : K.forget.WellFormed) :
    (K.resolvedSelf hWF).vertices = K.vertices := rfl

@[simp] theorem resolvedSelf_internalEdges (K : ResolvedFeynmanGraph) (hWF : K.forget.WellFormed) :
    (K.resolvedSelf hWF).internalEdges = K.internalEdges := rfl

@[simp] theorem resolvedSelf_externalLegs (K : ResolvedFeynmanGraph) (hWF : K.forget.WellFormed) :
    (K.resolvedSelf hWF).externalLegs = K.externalLegs := rfl

/-- **body-627 (Step 1, EMPTY-BOUNDARY-of-self) — the full subgraph has no boundary edges.**  Every internal
edge of `K` has both endpoints inside `K.vertices = (K.resolvedSelf hWF).vertices`, so the resolved boundary
predicate fails for all of them and the boundary-edge filter is empty.  Exact multiplicity (`= 0`). -/
theorem resolvedSelf_resolvedBoundaryEdges (K : ResolvedFeynmanGraph) (hWF : K.forget.WellFormed) :
    (K.resolvedSelf hWF).resolvedBoundaryEdges = 0 := by
  unfold ResolvedFeynmanSubgraph.resolvedBoundaryEdges
  rw [Multiset.filter_eq_nil]
  intro e he hb
  rcases hb with ⟨_, ht⟩ | ⟨hs, _⟩
  · exact ht ((K.resolvedSelf hWF).edges_supported e he).2
  · exact hs ((K.resolvedSelf hWF).edges_supported e he).1

end ResolvedFeynmanGraph

/-! ## Step 1 — the root-once EVEN normalizer -/

/-- **body-627 (Step 1) — the root-once external-leg-ID normalizer.**  Complete the full resolved subgraph
`K.resolvedSelf hWF` ONCE at root entry: existing legs are embedded into the EVEN `existingLegId` namespace
and — since the self-boundary is EMPTY — NO ODD boundary leg is generated yet.  Type owned by body-589's
`ResolvedFeynmanSubgraph → ResolvedFeynmanGraph`. -/
noncomputable def stableRootNormalize (K : ResolvedFeynmanGraph) (hWF : K.forget.WellFormed) :
    ResolvedFeynmanGraph :=
  (K.resolvedSelf hWF).boundaryCompletedResolvedGraph

@[simp] theorem stableRootNormalize_vertices (K : ResolvedFeynmanGraph) (hWF : K.forget.WellFormed) :
    (stableRootNormalize K hWF).vertices = K.vertices := rfl

@[simp] theorem stableRootNormalize_internalEdges (K : ResolvedFeynmanGraph) (hWF : K.forget.WellFormed) :
    (stableRootNormalize K hWF).internalEdges = K.internalEdges := rfl

/-- **body-627 (Step 1, HEADLINE legs) — existing legs made EVEN exactly ONCE, no ODD leg yet.**  The
normalized root's external legs are EXACTLY the EVEN re-encoding `K.externalLegs.map encodeExistingLeg`;
the ODD induced-leg family is EMPTY because the self-boundary is empty. -/
theorem stableRootNormalize_externalLegs (K : ResolvedFeynmanGraph) (hWF : K.forget.WellFormed) :
    (stableRootNormalize K hWF).externalLegs = K.externalLegs.map encodeExistingLeg := by
  unfold stableRootNormalize
  rw [boundaryCompletedResolvedGraph_externalLegs]
  unfold ResolvedFeynmanSubgraph.boundaryCompletedResolvedExternalLegs
  rw [K.resolvedSelf_resolvedBoundaryEdges hWF, Multiset.map_zero, add_zero,
    K.resolvedSelf_externalLegs hWF]

/-- **body-627 (Step 1, LOAD-BEARING) — the normalized root forgets RAW-equal to `K.forget`.**  The EVEN
re-encoding is invisible to `forget` (`encodeExistingLeg_forget`), and no ODD leg exists, so all three flat
fields coincide.  Not a class equality. -/
theorem stableRootNormalize_forget (K : ResolvedFeynmanGraph) (hWF : K.forget.WellFormed) :
    (stableRootNormalize K hWF).forget = K.forget := by
  have hleg : (stableRootNormalize K hWF).externalLegs.map ResolvedExternalLeg.forget
      = K.externalLegs.map ResolvedExternalLeg.forget := by
    rw [stableRootNormalize_externalLegs, Multiset.map_map]
    exact Multiset.map_congr rfl (fun ℓ _ => encodeExistingLeg_forget ℓ)
  simp only [ResolvedFeynmanGraph.forget, FeynmanGraph.mk.injEq]
  exact ⟨rfl, rfl, hleg⟩

/-- **body-627 (Step 1) — the normalized root forgets to a WELL-FORMED flat graph** (via the raw forget
equality + the input witness). -/
theorem stableRootNormalize_forget_wellFormed (K : ResolvedFeynmanGraph) (hWF : K.forget.WellFormed) :
    (stableRootNormalize K hWF).forget.WellFormed := by
  rw [stableRootNormalize_forget]; exact hWF

/-- **body-627 (Step 1) — the normalized root has unique edge ids** (internal edges unchanged from `K`). -/
theorem stableRootNormalize_edgeIdsUnique (K : ResolvedFeynmanGraph) (hWF : K.forget.WellFormed)
    (hE : K.EdgeIdsUnique) : (stableRootNormalize K hWF).EdgeIdsUnique :=
  (K.resolvedSelf hWF).boundaryCompletedResolvedGraph_edgeIdsUnique hE

/-- **body-627 (Step 1) — the normalized root has unique leg ids** (EVEN×EVEN via `LegIdsUnique`; the ODD
family is empty here, so parity is vacuous). -/
theorem stableRootNormalize_legIdsUnique (K : ResolvedFeynmanGraph) (hWF : K.forget.WellFormed)
    (hL : K.LegIdsUnique) (hE : K.EdgeIdsUnique) : (stableRootNormalize K hWF).LegIdsUnique :=
  (K.resolvedSelf hWF).boundaryCompletedResolvedGraph_legIdsUnique hL hE

/-- **body-627 (Step 1) — the normalizer commutes with the identity-preserving relabeling `mapPerm σ`.** -/
theorem stableRootNormalize_mapPerm (σ : Equiv.Perm VertexId)
    (K : ResolvedFeynmanGraph) (hWF : K.forget.WellFormed) :
    ((K.resolvedSelf hWF).mapPerm σ).boundaryCompletedResolvedGraph
      = (stableRootNormalize K hWF).mapPerm σ :=
  boundaryCompletedResolvedGraph_mapPerm σ (K.resolvedSelf hWF)

/-! ## Step 2 — the chosen φ⁴ normalized rigidification -/

/-- **body-627 (Step 2, well-formed witness RECOVERY) — the chosen rigidification forgets to a well-formed
graph.**  Recovered from the family-CD owner: `rigidifyPhi4Gen x`.property is the resolved-class CD of
`phi4RigidifiedGraph x`, whose `isConnectedDivergentFor_toResolvedClass` bundles the flat well-formedness of
`(phi4RigidifiedGraph x).forget`.  So the witness is NOT an external hypothesis. -/
theorem phi4RigidifiedGraph_forget_wellFormed (x : Phi4HopfGen) :
    (phi4RigidifiedGraph x).forget.WellFormed := by
  have hcd : ResolvedFeynmanGraphClass.IsConnectedDivergentFor
      phi4DivergenceMeasureFamily phi4PermInvariantDivergenceMeasureFamily
      (phi4RigidifiedGraph x).toResolvedClass := by
    have h := (rigidifyPhi4Gen x).property
    rwa [rigidifyPhi4Gen_val] at h
  exact ((ResolvedFeynmanGraphClass.isConnectedDivergentFor_toResolvedClass
    phi4DivergenceMeasureFamily phi4PermInvariantDivergenceMeasureFamily
    (phi4RigidifiedGraph x)).mp hcd).choose

/-- **body-627 (Step 2) — the chosen φ⁴ normalized rigidification.**  The unique-ID resolved representative
`phi4RigidifiedGraph x`, root-once EVEN-normalized.  The well-formed witness is recovered internally
(`phi4RigidifiedGraph_forget_wellFormed`), NOT exposed.  NOT packaged into `ResolvedPhi4HopfGen`. -/
noncomputable def phi4StableRigidifiedGraph (x : Phi4HopfGen) : ResolvedFeynmanGraph :=
  stableRootNormalize (phi4RigidifiedGraph x) (phi4RigidifiedGraph_forget_wellFormed x)

/-- **body-627 (Step 2, VICTORY) — the φ⁴ normalized rigidification forgets to the generator's class.**  The
root-once normalization is invisible to `forget` (Step 1), and the rigidification forgets to `x.val`
(body-585). -/
@[simp] theorem phi4StableRigidifiedGraph_forget_toClass (x : Phi4HopfGen) :
    (phi4StableRigidifiedGraph x).forget.toClass = x.val := by
  unfold phi4StableRigidifiedGraph
  rw [stableRootNormalize_forget, phi4RigidifiedGraph_forget_toClass]

/-- **body-627 (Step 2) — family-explicit resolved graph CD of the φ⁴ normalized rigidification.**  Its
resolved class is family-connected-divergent, read through the forgotten class `= x.val` (`x.property`). -/
theorem phi4StableRigidifiedGraph_isConnectedDivergentFor (x : Phi4HopfGen) :
    ResolvedFeynmanGraphClass.IsConnectedDivergentFor
      phi4DivergenceMeasureFamily phi4PermInvariantDivergenceMeasureFamily
      (phi4StableRigidifiedGraph x).toResolvedClass := by
  unfold ResolvedFeynmanGraphClass.IsConnectedDivergentFor
  rw [ResolvedFeynmanGraphClass.toFlatClass_mk, phi4StableRigidifiedGraph_forget_toClass]
  exact x.property

/-- **body-627 (Step 2) — the φ⁴ normalized rigidification has unique edge ids.** -/
theorem phi4StableRigidifiedGraph_edgeIdsUnique (x : Phi4HopfGen) :
    (phi4StableRigidifiedGraph x).EdgeIdsUnique :=
  stableRootNormalize_edgeIdsUnique (phi4RigidifiedGraph x) (phi4RigidifiedGraph_forget_wellFormed x)
    (phi4RigidifiedGraph_edgeIdsUnique x)

/-- **body-627 (Step 2) — the φ⁴ normalized rigidification has unique leg ids.** -/
theorem phi4StableRigidifiedGraph_legIdsUnique (x : Phi4HopfGen) :
    (phi4StableRigidifiedGraph x).LegIdsUnique :=
  stableRootNormalize_legIdsUnique (phi4RigidifiedGraph x) (phi4RigidifiedGraph_forget_wellFormed x)
    (phi4RigidifiedGraph_legIdsUnique x) (phi4RigidifiedGraph_edgeIdsUnique x)

/-! ## Step 3 — the one-step stable completion -/

/-- **body-627 (Step 3) — the one-step stable completion of `δ` on the normalized root.**  Complete the
nested subgraph `δ` of `stableRootNormalize K hWF` by body-597's stable nested completion of the full root
carrier.  Its external legs keep inherited legs VERBATIM and give a fresh ODD id only to genuinely new cut
edges. -/
noncomputable def stableBoundaryCompleteOne (K : ResolvedFeynmanGraph) (hWF : K.forget.WellFormed)
    (δ : ResolvedFeynmanSubgraph (stableRootNormalize K hWF)) : ResolvedFeynmanGraph :=
  stableNestedBoundaryCompletedGraph (K.resolvedSelf hWF) δ

@[simp] theorem stableBoundaryCompleteOne_vertices (K : ResolvedFeynmanGraph) (hWF : K.forget.WellFormed)
    (δ : ResolvedFeynmanSubgraph (stableRootNormalize K hWF)) :
    (stableBoundaryCompleteOne K hWF δ).vertices = δ.vertices := rfl

@[simp] theorem stableBoundaryCompleteOne_internalEdges (K : ResolvedFeynmanGraph)
    (hWF : K.forget.WellFormed) (δ : ResolvedFeynmanSubgraph (stableRootNormalize K hWF)) :
    (stableBoundaryCompleteOne K hWF δ).internalEdges = δ.internalEdges := rfl

/-- **body-627 (Step 3, CRUX) — the one-step completion's external legs, DEFINITIONAL form.**  Inherited
legs `δ.externalLegs` are kept VERBATIM; ONLY the freshly-cut root-boundary edges `newRootBoundary
(K.resolvedSelf hWF) δ` receive an ODD induced leg via `boundaryExternalLeg`.  `encodeExistingLeg` is NOT
called a second time — no `existingLegId (boundaryExternalLeg …)` re-encoding. -/
theorem stableBoundaryCompleteOne_externalLegs (K : ResolvedFeynmanGraph) (hWF : K.forget.WellFormed)
    (δ : ResolvedFeynmanSubgraph (stableRootNormalize K hWF)) :
    (stableBoundaryCompleteOne K hWF δ).externalLegs
      = δ.externalLegs
        + (newRootBoundary (K.resolvedSelf hWF) δ).map
            (rootRelativeInner (K.resolvedSelf hWF) δ).boundaryExternalLeg := rfl

/-! ## Step 4 — the one-step normal-form theorem (consumes body-626's owner) -/

/-- **body-627 (Step 4, HEADLINE) — the one-step stable completion is RAW-equal to the single root
completion.**  Under both external-leg saturations, consume body-626's ownership `normal_form_closed`
DIRECTLY: the stable one-step completion of `δ` equals the single root completion of the lift
`rootRelativeInner (K.resolvedSelf hWF) δ`.  Exact ID / multiplicity — NOT a class equality, no `HEq` /
`cast`.  This never touches body-625's naive `δ.boundaryCompletedResolvedGraph`. -/
theorem stableBoundaryCompleteOne_normalForm (K : ResolvedFeynmanGraph) (hWF : K.forget.WellFormed)
    (δ : ResolvedFeynmanSubgraph (stableRootNormalize K hWF))
    (hγsat : ResolvedExternalLegSaturated K (K.resolvedSelf hWF))
    (hδsat : ResolvedExternalLegSaturated (stableRootNormalize K hWF) δ) :
    stableBoundaryCompleteOne K hWF δ
      = (rootRelativeInner (K.resolvedSelf hWF) δ).boundaryCompletedResolvedGraph :=
  (stableBoundaryNormalFormOwnership_holds (K.resolvedSelf hWF) δ).normal_form_closed hγsat hδsat

/-- **body-627 (Step 4, thin) — strict `forget` equality** of the one-step completion with the single root
completion (congr of the raw equality). -/
theorem stableBoundaryCompleteOne_forget (K : ResolvedFeynmanGraph) (hWF : K.forget.WellFormed)
    (δ : ResolvedFeynmanSubgraph (stableRootNormalize K hWF))
    (hγsat : ResolvedExternalLegSaturated K (K.resolvedSelf hWF))
    (hδsat : ResolvedExternalLegSaturated (stableRootNormalize K hWF) δ) :
    (stableBoundaryCompleteOne K hWF δ).forget
      = (rootRelativeInner (K.resolvedSelf hWF) δ).boundaryCompletedResolvedGraph.forget :=
  congrArg ResolvedFeynmanGraph.forget (stableBoundaryCompleteOne_normalForm K hWF δ hγsat hδsat)

/-- **body-627 (Step 4, thin) — support / WellFormed** of the one-step completion's forget. -/
theorem stableBoundaryCompleteOne_forget_wellFormed (K : ResolvedFeynmanGraph) (hWF : K.forget.WellFormed)
    (δ : ResolvedFeynmanSubgraph (stableRootNormalize K hWF))
    (hγsat : ResolvedExternalLegSaturated K (K.resolvedSelf hWF))
    (hδsat : ResolvedExternalLegSaturated (stableRootNormalize K hWF) δ) :
    (stableBoundaryCompleteOne K hWF δ).forget.WellFormed := by
  rw [stableBoundaryCompleteOne_forget K hWF δ hγsat hδsat]
  exact (rootRelativeInner (K.resolvedSelf hWF) δ).boundaryCompletedResolvedGraph_forget_wellFormed

/-- **body-627 (Step 4, thin) — new-boundary traceability.**  Each fresh root-boundary leg traces back to a
UNIQUE resolved boundary edge of the lift, gated by root `EdgeIdsUnique` (owner `new_boundary_traceable`). -/
theorem stableBoundaryCompleteOne_newBoundary_traceable (K : ResolvedFeynmanGraph)
    (hWF : K.forget.WellFormed) (δ : ResolvedFeynmanSubgraph (stableRootNormalize K hWF))
    (hE : K.EdgeIdsUnique) {ℓ : ResolvedExternalLeg}
    (hℓ : ℓ ∈ stableNestedRootBoundaryLegs (K.resolvedSelf hWF) δ) :
    ∃! e, e ∈ (rootRelativeInner (K.resolvedSelf hWF) δ).resolvedBoundaryEdges
      ∧ (rootRelativeInner (K.resolvedSelf hWF) δ).boundaryExternalLeg e = ℓ :=
  (stableBoundaryNormalFormOwnership_holds (K.resolvedSelf hWF) δ).new_boundary_traceable hE ℓ hℓ

/-- **body-627 (Step 4, thin) — the one-step completion has unique edge ids** (owner `edgeIds_unique`). -/
theorem stableBoundaryCompleteOne_edgeIdsUnique (K : ResolvedFeynmanGraph) (hWF : K.forget.WellFormed)
    (δ : ResolvedFeynmanSubgraph (stableRootNormalize K hWF))
    (hγsat : ResolvedExternalLegSaturated K (K.resolvedSelf hWF))
    (hδsat : ResolvedExternalLegSaturated (stableRootNormalize K hWF) δ) (hE : K.EdgeIdsUnique) :
    (stableBoundaryCompleteOne K hWF δ).EdgeIdsUnique :=
  (stableBoundaryNormalFormOwnership_holds (K.resolvedSelf hWF) δ).edgeIds_unique hγsat hδsat hE

/-- **body-627 (Step 4, thin) — the one-step completion has unique leg ids** (owner `legIds_unique`). -/
theorem stableBoundaryCompleteOne_legIdsUnique (K : ResolvedFeynmanGraph) (hWF : K.forget.WellFormed)
    (δ : ResolvedFeynmanSubgraph (stableRootNormalize K hWF))
    (hγsat : ResolvedExternalLegSaturated K (K.resolvedSelf hWF))
    (hδsat : ResolvedExternalLegSaturated (stableRootNormalize K hWF) δ)
    (hL : K.LegIdsUnique) (hE : K.EdgeIdsUnique) :
    (stableBoundaryCompleteOne K hWF δ).LegIdsUnique :=
  (stableBoundaryNormalFormOwnership_holds (K.resolvedSelf hWF) δ).legIds_unique hγsat hδsat hL hE

/-- **body-627 (Step 4, thin) — `mapPerm` coherence of the one-step completion** (owner `mapPerm_coherent`). -/
theorem stableBoundaryCompleteOne_mapPerm (K : ResolvedFeynmanGraph) (hWF : K.forget.WellFormed)
    (δ : ResolvedFeynmanSubgraph (stableRootNormalize K hWF))
    (hγsat : ResolvedExternalLegSaturated K (K.resolvedSelf hWF))
    (hδsat : ResolvedExternalLegSaturated (stableRootNormalize K hWF) δ) (σ : Equiv.Perm VertexId) :
    stableNestedBoundaryCompletedGraph ((K.resolvedSelf hWF).mapPerm σ)
        (mapPermNestedBoundarySubgraph σ (K.resolvedSelf hWF) δ)
      = (stableBoundaryCompleteOne K hWF δ).mapPerm σ :=
  (stableBoundaryNormalFormOwnership_holds (K.resolvedSelf hWF) δ).mapPerm_coherent hγsat hδsat σ

/-- **body-627 (Step 4, thin) — the edge-complete exact boundary split.**  The full root carrier is
internal-edge complete (its edges ARE the ambient's), so the induced root boundary of the lift splits
cleanly with NO hidden root boundary (owner `boundary_split_of_edgeComplete`). -/
theorem stableBoundaryCompleteOne_boundary_split (K : ResolvedFeynmanGraph) (hWF : K.forget.WellFormed)
    (δ : ResolvedFeynmanSubgraph (stableRootNormalize K hWF)) :
    (rootRelativeInner (K.resolvedSelf hWF) δ).resolvedBoundaryEdges
      = inheritedOuter (K.resolvedSelf hWF) δ + δ.resolvedBoundaryEdges :=
  (stableBoundaryNormalFormOwnership_holds (K.resolvedSelf hWF) δ).boundary_split_of_edgeComplete
    (Multiset.filter_le _ _)

/-- **body-627 (Step 4, thin) — resolved-class transport across the raw equality.**  The one-step
completion and the single root completion carry the SAME `mapPerm`-iso resolved class (congr of the raw
equality); hence any class-level property (family CD included) transfers between them. -/
theorem stableBoundaryCompleteOne_toResolvedClass (K : ResolvedFeynmanGraph) (hWF : K.forget.WellFormed)
    (δ : ResolvedFeynmanSubgraph (stableRootNormalize K hWF))
    (hγsat : ResolvedExternalLegSaturated K (K.resolvedSelf hWF))
    (hδsat : ResolvedExternalLegSaturated (stableRootNormalize K hWF) δ) :
    (stableBoundaryCompleteOne K hWF δ).toResolvedClass
      = (rootRelativeInner (K.resolvedSelf hWF) δ).boundaryCompletedResolvedGraph.toResolvedClass :=
  congrArg ResolvedFeynmanGraph.toResolvedClass (stableBoundaryCompleteOne_normalForm K hWF δ hγsat hδsat)

/-- **body-627 (Step 4, thin — explicit φ⁴ graph-CD transport).**  Under saturation, the family-explicit φ⁴
connected-divergence of the single root completion transports across the raw equality to the one-step stable
completion (via the shared resolved class).  No class equality is fabricated: it is `stableBoundaryComplete
One_toResolvedClass` rewritten into the CD predicate. -/
theorem stableBoundaryCompleteOne_phi4_isConnectedDivergentFor (K : ResolvedFeynmanGraph)
    (hWF : K.forget.WellFormed) (δ : ResolvedFeynmanSubgraph (stableRootNormalize K hWF))
    (hγsat : ResolvedExternalLegSaturated K (K.resolvedSelf hWF))
    (hδsat : ResolvedExternalLegSaturated (stableRootNormalize K hWF) δ)
    (hCD : ResolvedFeynmanGraphClass.IsConnectedDivergentFor
      phi4DivergenceMeasureFamily phi4PermInvariantDivergenceMeasureFamily
      (rootRelativeInner (K.resolvedSelf hWF) δ).boundaryCompletedResolvedGraph.toResolvedClass) :
    ResolvedFeynmanGraphClass.IsConnectedDivergentFor
      phi4DivergenceMeasureFamily phi4PermInvariantDivergenceMeasureFamily
      (stableBoundaryCompleteOne K hWF δ).toResolvedClass := by
  rw [stableBoundaryCompleteOne_toResolvedClass K hWF δ hγsat hδsat]
  exact hCD

end GaugeGeometry.QFT.Combinatorial
