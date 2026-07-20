import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCrossAmbientStarAudit
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCorrectingPermFacts

/-!
# R-6c-body-447 — the LOCAL fixing domain of the cross-ambient correcting permutation (PROVED)

Four-hundred-and-forty-seventh genuine-body step — pinning, in Lean, exactly which vertices the body-446 correcting
permutation `ρ` must fix.  The decisive point (and the trap body-403 warns against): **`ρ` must NOT fix all of
`G.vertices`.**  The local allocator's star is fresh only relative to the PARENT ambient, and may legitimately collide
with an unrelated `G` survivor vertex; requiring `ρ = 1` on all of `G` would over-constrain and re-introduce the
strict obstruction.  The needed fixing range is LOCAL.

## The generic local-fixing perm (banked)

`ρ` is the body-18 `finsetSubtypeExtensionPerm` between the OLD star set `T` (the inner stars, fresh w.r.t. the parent
ambient) and the NEW star set `S` (the promoted/outer stars, fresh w.r.t. `G`).  Its two point laws are:

* `crossAmbientStarRenamePerm_fixes_of_avoid` — `ρ` fixes ANY base finset `V` that BOTH star sets avoid; taking
  `V := parent-ambient vertices` gives the LOCAL fixing.  It does NOT need `V = G.vertices` — only a set both star sets
  miss;
* `crossAmbientStarRenamePerm_on_t` — `ρ` sends each old star to its corresponding new star (via the star-set bijection).

## The two live domains (the verdict on the fixing range)

```text
Promoted side   base V := o.γ.1.vertices          (the occurrence parent's vertices)
  old stars T = inner stars   `starOf o.γ.1 o.B b`      — fresh w.r.t. o.γ.1              (avoid V ✓)
  new stars S = promoted stars `starOf G (selectedOuter) (o.γ.promote b)` — fresh w.r.t. G ⊇ o.γ.1.vertices (avoid V ✓)
  correspondence  b ∈ o.B.elements ↔ o.γ.1.promote b ∈ promoted forest
Inner side      base V := (Core.parent z δ).vertices
  old stars T = inner stars   `starOf parent innerRaw (toInner A)` — fresh w.r.t. parent        (avoid V ✓)
  new stars S = touched outer stars `starOf G z.1.1 A.1` — fresh w.r.t. G ⊇ parent.vertices      (avoid V ✓)
  correspondence  A ∈ touchedOuterComponents ↔ toInner A ∈ innerRaw.elements
```

In BOTH cases the fixing base `V` is the PARENT ambient's vertices — a strict subset of `G.vertices` — and both star
sets avoid it by freshness (the inner directly; the outer/promoted because `V ⊆ G.vertices` and its stars avoid all of
`G.vertices`).  So `crossAmbientStarRenamePerm_fixes_of_avoid` applies with the LOCAL `V`, confirming: **local correcting
permutations are constructible and fix only the parent-ambient vertices, never all of `G`.**

## Ownership audit (which consumers need only local fixing — verdict pending on the last)

The consumers rewriting through `ρ` operate at the parent scope: `parent`-reconstruction vertices / internalEdges /
externalLegs (body-385/386), `contractedSourceGraph`, the corrected remnant component, and the target-graph
`reembedAsSubgraph`.  All of these live inside `(Core.parent z δ).vertices` / `o.γ.1.vertices`, so LOCAL fixing suffices.
The single place that could force fixing an UNRELATED `G` survivor vertex is the `ForestIdx` transport across the whole
recovered union — whether `VBuild` / `Concrete` can absorb `ρ` at the remnant-ownership boundary (so `ρ = 1` on the live
domain, or the global survivors are provably disjoint from both star sets) is the decisive follow-up, still pending.

## Verdict

```text
local correcting permutations                         CONSTRUCTIBLE  (this body: fixes a local base V, not all of G)
exact local contraction equality (mapPerm ρ graphs)   likely derivable (next: the corrected graph equality)
V / Concrete absorb corrections at the ownership bdy   AUDIT PENDING (ForestIdx transport / global survivor disjointness)
```

Per the HALT/guards: `ρ v = v` is NOT required on all of `G`; the strict `StarProm` / `InnerStarRaw` are not revived; only
the permutation + the two point laws are built here (no corrected-graph equality yet, no `Concrete` wiring); body-445
stays a valid conditional theorem.  NOT the unconditional theorem.  No facade, no flat term, no `forgetHopf`, no
rep/perm, and NO `promote_collapse` / singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

/-- **R-6c-body-447 — the cross-ambient star-renaming permutation.**  The body-18 extension of a bijection between the
old star set `T` and the new star set `S`. -/
noncomputable def crossAmbientStarRenamePerm (S T : Finset VertexId)
    (e : {x : VertexId // x ∈ S} ≃ {x : VertexId // x ∈ T}) : Equiv.Perm VertexId :=
  finsetSubtypeExtensionPerm S T e

/-- **R-6c-body-447 ∎ — LOCAL fixing.**  `ρ` fixes any base finset `V` that BOTH star sets avoid — for the cross-ambient
sockets this is the PARENT ambient's vertices, a strict subset of `G.vertices`, NOT all of `G`. -/
theorem crossAmbientStarRenamePerm_fixes_of_avoid (S T : Finset VertexId)
    (e : {x : VertexId // x ∈ S} ≃ {x : VertexId // x ∈ T}) {V : Finset VertexId}
    (hS : ∀ v ∈ S, v ∉ V) (hT : ∀ v ∈ T, v ∉ V) {v : VertexId} (hv : v ∈ V) :
    crossAmbientStarRenamePerm S T e v = v :=
  finsetSubtypeExtensionPerm_apply_of_not_mem S T e
    (fun hvS => hS v hvS hv) (fun hvT => hT v hvT hv)

/-- **R-6c-body-447 — the star point law.**  `ρ` sends each old star to its corresponding new star. -/
theorem crossAmbientStarRenamePerm_on_t (S T : Finset VertexId)
    (e : {x : VertexId // x ∈ S} ≃ {x : VertexId // x ∈ T}) {v : VertexId} (hv : v ∈ T) :
    crossAmbientStarRenamePerm S T e v = (e.symm ⟨v, hv⟩).1 :=
  finsetSubtypeExtensionPerm_on_t S T e hv

end GaugeGeometry.QFT.Combinatorial
