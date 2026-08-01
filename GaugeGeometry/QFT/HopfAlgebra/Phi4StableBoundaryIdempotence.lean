import GaugeGeometry.QFT.HopfAlgebra.Phi4StableResolvedRigidification

/-!
# QFT-R1-body-628 — root-relative stable-completion IDEMPOTENCE (the repair paired with body-625's no-go)

Body-625 proved a class-level **no-go** (`phi4WTriplePrime_nestedLeft_class_ne_of_inheritedOuter`): the
naive nested completion `δ.boundaryCompletedResolvedGraph` re-encodes an inherited outer boundary leg EVEN
locally (`existingLegId ℓ = 4·e+2`) while the root-direct route keeps it ODD (`boundaryLegId e = 2·e+1`);
the `legId` profile (`phi4WTriplePrime_legIdProfile`) is a `mapPerm`-invariant, so no relabeling reconciles
them.  That witness is a **standing design principle**, not erased.

Body-626 established the stable-completion OWNERSHIP (`StableBoundaryNormalFormOwnership`,
`stableBoundaryNormalFormOwnership_holds`).  Body-627 realized its ENTRY and its ONE-STEP action for the
root-carrier `K.resolvedSelf hWF`.  This body **generalizes** body-627's Step-4 one-step normal form to an
ARBITRARY occurrence `(γ, δ)` and states the headline as an IDEMPOTENCE law: iterating the stable completion
returns to the ROOT normal form of the lift.

## The two-argument API (TYPE CORRECTION — no dependent transport)

The informal `stableComplete (stableComplete γ) δ` splits into two total APIs, whose `δ` lives over the
COMPLETED graph:

* `stableBoundaryNormalForm γ := γ.boundaryCompletedResolvedGraph`
  (`ResolvedFeynmanSubgraph G → ResolvedFeynmanGraph`);
* `stableBoundaryIterate γ δ := stableNestedBoundaryCompletedGraph γ δ`,
  for `δ : ResolvedFeynmanSubgraph (stableBoundaryNormalForm γ)`.

## Steps

* Step 1 — the stable algebra API: the two `def`s + raw field anchors (vertices `= δ.vertices`,
  internalEdges `= δ.internalEdges`, inherited external legs VERBATIM + only the fresh `newRootBoundary γ δ`
  legs made ODD; `encodeExistingLeg` is NOT re-applied to inherited legs).
* Step 2 — the HEADLINE `stableBoundaryIterate_idempotent`: a RAW `ResolvedFeynmanGraph` equality
  `stableBoundaryIterate γ δ = stableBoundaryNormalForm (rootRelativeInner γ δ)`, returning body-626 owner's
  `normal_form_closed hγsat hδsat` DIRECTLY — geometry is NOT re-proved.
* Step 3 — idempotence observables, thin `congrArg` of the HEADLINE: strict `forget` / `toResolvedClass`
  equality; the `legIdProfile` equality (the head-on answer to body-625's no-go); external-leg multiset /
  `card` equality; `physicalExternalLegCount` / φ⁴ superficial-degree equality; family-explicit φ⁴ CD
  transport.
* Step 4 — ownership preservation on general `(γ, δ)`: new-boundary unique traceability, `EdgeIdsUnique`,
  `LegIdsUnique`, `mapPerm` coherence, edge-complete exact boundary split — each consuming a body-626 owner
  field directly.
* Step 5 — body-627 specialization: with `γ := K.resolvedSelf hWF` the 627 API is a `rfl`-SPECIALIZATION of
  the HEADLINE (`stableBoundaryCompleteOne = stableBoundaryIterate (K.resolvedSelf hWF)` and, by proof
  irrelevance, `stableBoundaryCompleteOne_normalForm = stableBoundaryIterate_idempotent`), so 627 and 628 are
  ONE system.

## The counterpoint to body-625

| route          | `legId` profile vs. root                                 | body |
|----------------|----------------------------------------------------------|------|
| naive nested   | profile MISMATCH PROVED (`…_nestedLeft_class_ne…`)        | 625  |
| stable nested  | profile EQUALITY PROVED (`stableBoundaryIterate_legIdProfile_eq`) | 628  |

## HALT / red lines
NO new `structure` / `class` / `instance` (only `def`s + `theorem`s).  The idempotent operation is the
ROOT-RELATIVE inherited-preserving action `stableBoundaryIterate`; there is NO
`stableRootNormalize (stableRootNormalize …)` claim (that would re-encode EVEN `2n ↦ 4n`, which is NOT the
wanted idempotence).  On the nested route `δ.boundaryCompletedResolvedGraph` is NEVER used and
`encodeExistingLeg` is NEVER re-applied to inherited legs; every equation targets only
`(rootRelativeInner γ δ).boundaryCompletedResolvedGraph = stableBoundaryNormalForm (rootRelativeInner γ δ)`.
NO carrier / HopfGen / HopfH / coproduct (that is 629).  Multiplicity-exact (`Multiset`), NO dedup /
`toFinset`.  NO forbidden divergence class in any declaration TYPE; NO public `HEq` / `cast` / graph-data
`▸`; ZERO `sorry` / `admit` / `native_decide`.  body-625's no-go and every existing file are UNEDITED.
Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

open ResolvedFeynmanSubgraph

variable {G : ResolvedFeynmanGraph}

/-! ## Step 1 — the stable algebra API -/

/-- **body-628 (Step 1) — the stable-boundary NORMAL FORM.**  The root-once completion of a subgraph `γ`:
existing legs into the EVEN `existingLegId` namespace, fresh cut edges into the ODD `boundaryLegId`
namespace, ONCE.  A plain rename of body-589's `boundaryCompletedResolvedGraph` — same output TYPE
`ResolvedFeynmanSubgraph G → ResolvedFeynmanGraph`. -/
noncomputable def stableBoundaryNormalForm (γ : ResolvedFeynmanSubgraph G) : ResolvedFeynmanGraph :=
  γ.boundaryCompletedResolvedGraph

/-- **body-628 (Step 1) — the stable-boundary ITERATE.**  Complete the nested subgraph `δ` (over the
completed graph `stableBoundaryNormalForm γ`) via body-597's root-relative stable nested completion:
inherited legs are kept VERBATIM (no re-encoding) and ONLY genuinely new cut edges receive a fresh ODD leg.
This is the ROOT-RELATIVE inherited-preserving iteration — NOT a second root re-encoding. -/
noncomputable def stableBoundaryIterate (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph (stableBoundaryNormalForm γ)) : ResolvedFeynmanGraph :=
  stableNestedBoundaryCompletedGraph γ δ

@[simp] theorem stableBoundaryIterate_vertices (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph (stableBoundaryNormalForm γ)) :
    (stableBoundaryIterate γ δ).vertices = δ.vertices := rfl

@[simp] theorem stableBoundaryIterate_internalEdges (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph (stableBoundaryNormalForm γ)) :
    (stableBoundaryIterate γ δ).internalEdges = δ.internalEdges := rfl

/-- **body-628 (Step 1, CRUX) — the iterate's external legs, DEFINITIONAL form.**  Inherited legs
`δ.externalLegs` are kept VERBATIM; ONLY the freshly-cut root-boundary edges `newRootBoundary γ δ` receive an
ODD induced leg via `(rootRelativeInner γ δ).boundaryExternalLeg`.  `encodeExistingLeg` is NOT re-applied. -/
theorem stableBoundaryIterate_externalLegs (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph (stableBoundaryNormalForm γ)) :
    (stableBoundaryIterate γ δ).externalLegs
      = δ.externalLegs
        + (newRootBoundary γ δ).map (rootRelativeInner γ δ).boundaryExternalLeg := rfl

/-! ## Step 2 — the HEADLINE idempotence law -/

/-- **body-628 (Step 2, HEADLINE) — the stable completion is IDEMPOTENT: iterating returns the ROOT normal
form.**  Under both external-leg saturations, `stableBoundaryIterate γ δ` (inherited legs verbatim + fresh
root-boundary legs) is RAW-equal to `stableBoundaryNormalForm (rootRelativeInner γ δ)`, the single root
completion of the lift.  This consumes body-626's ownership `normal_form_closed` DIRECTLY — a raw
`ResolvedFeynmanGraph` equality (exact ID / multiplicity), NOT a class equality, no `HEq` / `cast`, and it
never touches body-625's naive `δ.boundaryCompletedResolvedGraph`.  This GENERALIZES body-627's Step-4
`stableBoundaryCompleteOne_normalForm` from `K.resolvedSelf hWF` to an ARBITRARY `(γ, δ)`. -/
theorem stableBoundaryIterate_idempotent (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph (stableBoundaryNormalForm γ))
    (hγsat : ResolvedExternalLegSaturated G γ)
    (hδsat : ResolvedExternalLegSaturated (stableBoundaryNormalForm γ) δ) :
    stableBoundaryIterate γ δ = stableBoundaryNormalForm (rootRelativeInner γ δ) :=
  (stableBoundaryNormalFormOwnership_holds γ δ).normal_form_closed hγsat hδsat

/-! ## Step 3 — idempotence observables (thin `congrArg` of the HEADLINE) -/

/-- **body-628 (Step 3, thin) — strict `forget` equality.** -/
theorem stableBoundaryIterate_forget_eq (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph (stableBoundaryNormalForm γ))
    (hγsat : ResolvedExternalLegSaturated G γ)
    (hδsat : ResolvedExternalLegSaturated (stableBoundaryNormalForm γ) δ) :
    (stableBoundaryIterate γ δ).forget
      = (stableBoundaryNormalForm (rootRelativeInner γ δ)).forget :=
  congrArg ResolvedFeynmanGraph.forget (stableBoundaryIterate_idempotent γ δ hγsat hδsat)

/-- **body-628 (Step 3, thin) — resolved-class equality**, hence any class-level property transfers. -/
theorem stableBoundaryIterate_toResolvedClass_eq (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph (stableBoundaryNormalForm γ))
    (hγsat : ResolvedExternalLegSaturated G γ)
    (hδsat : ResolvedExternalLegSaturated (stableBoundaryNormalForm γ) δ) :
    (stableBoundaryIterate γ δ).toResolvedClass
      = (stableBoundaryNormalForm (rootRelativeInner γ δ)).toResolvedClass :=
  congrArg ResolvedFeynmanGraph.toResolvedClass (stableBoundaryIterate_idempotent γ δ hγsat hδsat)

/-- **body-628 (Step 3, HEAD-ON ANSWER TO body-625's NO-GO) — the `legId` PROFILE EQUALITY.**  Where the
naive nested completion mismatched the root profile (body-625's `mapPerm`-invariant obstruction), the STABLE
iterate has an EXACT `legId`-profile equality with the root normal form.  A `congrArg` of the raw HEADLINE:
equal raw graphs force equal `phi4WTriplePrime_legIdProfile`. -/
theorem stableBoundaryIterate_legIdProfile_eq (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph (stableBoundaryNormalForm γ))
    (hγsat : ResolvedExternalLegSaturated G γ)
    (hδsat : ResolvedExternalLegSaturated (stableBoundaryNormalForm γ) δ) :
    phi4WTriplePrime_legIdProfile (stableBoundaryIterate γ δ)
      = phi4WTriplePrime_legIdProfile (stableBoundaryNormalForm (rootRelativeInner γ δ)) :=
  congrArg phi4WTriplePrime_legIdProfile (stableBoundaryIterate_idempotent γ δ hγsat hδsat)

/-- **body-628 (Step 3, thin) — external-leg MULTISET equality.** -/
theorem stableBoundaryIterate_externalLegs_eq (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph (stableBoundaryNormalForm γ))
    (hγsat : ResolvedExternalLegSaturated G γ)
    (hδsat : ResolvedExternalLegSaturated (stableBoundaryNormalForm γ) δ) :
    (stableBoundaryIterate γ δ).externalLegs
      = (stableBoundaryNormalForm (rootRelativeInner γ δ)).externalLegs :=
  congrArg ResolvedFeynmanGraph.externalLegs (stableBoundaryIterate_idempotent γ δ hγsat hδsat)

/-- **body-628 (Step 3, thin) — external-leg CARD equality** (`card` of the multiset equality). -/
theorem stableBoundaryIterate_externalLegs_card_eq (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph (stableBoundaryNormalForm γ))
    (hγsat : ResolvedExternalLegSaturated G γ)
    (hδsat : ResolvedExternalLegSaturated (stableBoundaryNormalForm γ) δ) :
    (stableBoundaryIterate γ δ).externalLegs.card
      = (stableBoundaryNormalForm (rootRelativeInner γ δ)).externalLegs.card :=
  congrArg Multiset.card (stableBoundaryIterate_externalLegs_eq γ δ hγsat hδsat)

/-- **body-628 (Step 3, thin) — physical external-leg count equality of the two completed self-subgraphs.**
The completed graph carries no induced boundary, so `physicalExternalLegCount` of its self-subgraph is
`externalLegs.card` (body-561 `self_physicalExternalLegCount`); the `forget` equality transports it. -/
theorem stableBoundaryIterate_physicalExternalLegCount_eq (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph (stableBoundaryNormalForm γ))
    (hγsat : ResolvedExternalLegSaturated G γ)
    (hδsat : ResolvedExternalLegSaturated (stableBoundaryNormalForm γ) δ)
    (hWF₁ : (stableBoundaryIterate γ δ).forget.WellFormed)
    (hWF₂ : (stableBoundaryNormalForm (rootRelativeInner γ δ)).forget.WellFormed) :
    (FeynmanSubgraph.self (stableBoundaryIterate γ δ).forget hWF₁).physicalExternalLegCount
      = (FeynmanSubgraph.self
          (stableBoundaryNormalForm (rootRelativeInner γ δ)).forget hWF₂).physicalExternalLegCount := by
  rw [FeynmanSubgraph.self_physicalExternalLegCount, FeynmanSubgraph.self_physicalExternalLegCount,
    stableBoundaryIterate_forget_eq γ δ hγsat hδsat]

/-- **body-628 (Step 3, thin) — φ⁴ superficial-DEGREE equality of the two completed self-subgraphs.**
`ωφ4(self) = 4 − externalLegs.card` (body-561 `phi4SuperficialDegree_self`); the `forget` equality closes
it.  The idempotent completion preserves the φ⁴ degree of divergence exactly. -/
theorem stableBoundaryIterate_phi4SuperficialDegree_eq (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph (stableBoundaryNormalForm γ))
    (hγsat : ResolvedExternalLegSaturated G γ)
    (hδsat : ResolvedExternalLegSaturated (stableBoundaryNormalForm γ) δ)
    (hWF₁ : (stableBoundaryIterate γ δ).forget.WellFormed)
    (hWF₂ : (stableBoundaryNormalForm (rootRelativeInner γ δ)).forget.WellFormed) :
    (FeynmanSubgraph.self (stableBoundaryIterate γ δ).forget hWF₁).phi4SuperficialDegree
      = (FeynmanSubgraph.self
          (stableBoundaryNormalForm (rootRelativeInner γ δ)).forget hWF₂).phi4SuperficialDegree := by
  rw [FeynmanSubgraph.phi4SuperficialDegree_self, FeynmanSubgraph.phi4SuperficialDegree_self,
    stableBoundaryIterate_forget_eq γ δ hγsat hδsat]

/-- **body-628 (Step 3, thin — family-explicit φ⁴ CD transport).**  The family-explicit φ⁴
connected-divergence of the root normal form transports across the HEADLINE (via the shared resolved class)
to the stable iterate.  No class equality is fabricated: it is `stableBoundaryIterate_toResolvedClass_eq`
rewritten into the CD predicate. -/
theorem stableBoundaryIterate_phi4_isConnectedDivergentFor (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph (stableBoundaryNormalForm γ))
    (hγsat : ResolvedExternalLegSaturated G γ)
    (hδsat : ResolvedExternalLegSaturated (stableBoundaryNormalForm γ) δ)
    (hCD : ResolvedFeynmanGraphClass.IsConnectedDivergentFor
      phi4DivergenceMeasureFamily phi4PermInvariantDivergenceMeasureFamily
      (stableBoundaryNormalForm (rootRelativeInner γ δ)).toResolvedClass) :
    ResolvedFeynmanGraphClass.IsConnectedDivergentFor
      phi4DivergenceMeasureFamily phi4PermInvariantDivergenceMeasureFamily
      (stableBoundaryIterate γ δ).toResolvedClass := by
  rw [stableBoundaryIterate_toResolvedClass_eq γ δ hγsat hδsat]
  exact hCD

/-! ## Step 4 — ownership preservation on general `(γ, δ)` (body-626 owner fields) -/

/-- **body-628 (Step 4) — new-boundary UNIQUE traceability.**  Each fresh root-boundary leg traces back to a
UNIQUE resolved boundary edge of `R := rootRelativeInner γ δ`, gated by root `G.EdgeIdsUnique`
(owner `new_boundary_traceable`). -/
theorem stableBoundaryIterate_newBoundary_traceable (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph (stableBoundaryNormalForm γ)) (hE : G.EdgeIdsUnique)
    {ℓ : ResolvedExternalLeg} (hℓ : ℓ ∈ stableNestedRootBoundaryLegs γ δ) :
    ∃! e, e ∈ (rootRelativeInner γ δ).resolvedBoundaryEdges
      ∧ (rootRelativeInner γ δ).boundaryExternalLeg e = ℓ :=
  (stableBoundaryNormalFormOwnership_holds γ δ).new_boundary_traceable hE ℓ hℓ

/-- **body-628 (Step 4) — the iterate has unique edge ids** (owner `edgeIds_unique`). -/
theorem stableBoundaryIterate_edgeIdsUnique (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph (stableBoundaryNormalForm γ))
    (hγsat : ResolvedExternalLegSaturated G γ)
    (hδsat : ResolvedExternalLegSaturated (stableBoundaryNormalForm γ) δ) (hE : G.EdgeIdsUnique) :
    (stableBoundaryIterate γ δ).EdgeIdsUnique :=
  (stableBoundaryNormalFormOwnership_holds γ δ).edgeIds_unique hγsat hδsat hE

/-- **body-628 (Step 4) — the iterate has unique leg ids** (EVEN×EVEN via `LegIdsUnique`, ODD×ODD via
`EdgeIdsUnique`, cross by parity; owner `legIds_unique`). -/
theorem stableBoundaryIterate_legIdsUnique (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph (stableBoundaryNormalForm γ))
    (hγsat : ResolvedExternalLegSaturated G γ)
    (hδsat : ResolvedExternalLegSaturated (stableBoundaryNormalForm γ) δ)
    (hL : G.LegIdsUnique) (hE : G.EdgeIdsUnique) :
    (stableBoundaryIterate γ δ).LegIdsUnique :=
  (stableBoundaryNormalFormOwnership_holds γ δ).legIds_unique hγsat hδsat hL hE

/-- **body-628 (Step 4) — `mapPerm` coherence** of the iterate with the identity-preserving relabeling
`mapPerm σ` (owner `mapPerm_coherent`). -/
theorem stableBoundaryIterate_mapPerm (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph (stableBoundaryNormalForm γ))
    (hγsat : ResolvedExternalLegSaturated G γ)
    (hδsat : ResolvedExternalLegSaturated (stableBoundaryNormalForm γ) δ) (σ : Equiv.Perm VertexId) :
    stableNestedBoundaryCompletedGraph (γ.mapPerm σ) (mapPermNestedBoundarySubgraph σ γ δ)
      = (stableBoundaryIterate γ δ).mapPerm σ :=
  (stableBoundaryNormalFormOwnership_holds γ δ).mapPerm_coherent hγsat hδsat σ

/-- **body-628 (Step 4) — edge-complete EXACT boundary split.**  Under vertex-induced internal-edge
completeness of `γ` the induced root boundary of the lift splits cleanly (NO hidden root boundary), so the
normal form is stable under iteration — re-completion invents nothing (owner
`boundary_split_of_edgeComplete`). -/
theorem stableBoundaryIterate_boundary_split (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph (stableBoundaryNormalForm γ)) (hEC : ResolvedInternalEdgeComplete γ) :
    (rootRelativeInner γ δ).resolvedBoundaryEdges
      = inheritedOuter γ δ + δ.resolvedBoundaryEdges :=
  (stableBoundaryNormalFormOwnership_holds γ δ).boundary_split_of_edgeComplete hEC

/-! ## Step 5 — body-627 is the `rfl`-SPECIALIZATION of the HEADLINE (one system, not two) -/

/-- **body-628 (Step 5, OPERATION) — the 627 one-step completion IS the 628 iterate specialized.**  With
`γ := K.resolvedSelf hWF`, body-627's `stableBoundaryCompleteOne K hWF δ` is DEFINITIONALLY
`stableBoundaryIterate (K.resolvedSelf hWF) δ` (both unfold to `stableNestedBoundaryCompletedGraph`). -/
theorem stableBoundaryCompleteOne_eq_stableBoundaryIterate (K : ResolvedFeynmanGraph)
    (hWF : K.forget.WellFormed) (δ : ResolvedFeynmanSubgraph (stableRootNormalize K hWF)) :
    stableBoundaryCompleteOne K hWF δ = stableBoundaryIterate (K.resolvedSelf hWF) δ := rfl

/-- **body-628 (Step 5, TARGET) — the two headlines target the SAME root completion.**  Body-627's target
`(rootRelativeInner (K.resolvedSelf hWF) δ).boundaryCompletedResolvedGraph` is DEFINITIONALLY
`stableBoundaryNormalForm (rootRelativeInner (K.resolvedSelf hWF) δ)`. -/
theorem stableBoundaryCompleteOne_normalForm_target (K : ResolvedFeynmanGraph)
    (hWF : K.forget.WellFormed) (δ : ResolvedFeynmanSubgraph (stableRootNormalize K hWF)) :
    (rootRelativeInner (K.resolvedSelf hWF) δ).boundaryCompletedResolvedGraph
      = stableBoundaryNormalForm (rootRelativeInner (K.resolvedSelf hWF) δ) := rfl

/-- **body-628 (Step 5, PROOF) — body-627's `stableBoundaryCompleteOne_normalForm` IS the HEADLINE
specialized.**  Both prove DEFINITIONALLY-equal `ResolvedFeynmanGraph` equalities, so by proof irrelevance the
two proof terms coincide (`rfl`).  This certifies the 627 and 628 APIs are ONE system: 628's
`stableBoundaryIterate_idempotent` generalizes 627's Step-4 normal form, and specializing at
`γ := K.resolvedSelf hWF` recovers it exactly. -/
theorem stableBoundaryCompleteOne_normalForm_eq_idempotent (K : ResolvedFeynmanGraph)
    (hWF : K.forget.WellFormed) (δ : ResolvedFeynmanSubgraph (stableRootNormalize K hWF))
    (hγsat : ResolvedExternalLegSaturated K (K.resolvedSelf hWF))
    (hδsat : ResolvedExternalLegSaturated (stableRootNormalize K hWF) δ) :
    stableBoundaryIterate_idempotent (K.resolvedSelf hWF) δ hγsat hδsat
      = stableBoundaryCompleteOne_normalForm K hWF δ hγsat hδsat := rfl

end GaugeGeometry.QFT.Combinatorial
