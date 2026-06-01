import GaugeGeometry.QFT.HopfAlgebra.QuotientLift

/-!
# Subgraph isomorphism classes (ambient-fixed)  [Sprint B' — H2.4]

**Path B** (ambient-family) for `FeynmanSubgraphClass`: for each fixed
`G : FeynmanGraph`, `FeynmanSubgraphClass G` is the quotient of
`FeynmanSubgraph G` by the action of the *ambient-graph stabilizer*
`{ π : Equiv.Perm VertexId // G.mapPerm π = G }`.

## Rationale (confirmed 2026-04-23)

The alternative (Path A) — a single quotient of the Σ-type
`Σ G, FeynmanSubgraph G` by a joint relation on ambient-and-subgraph
pairs — requires `HEq` / `cast` gymnastics because
`γ.mapPerm π : FeynmanSubgraph (G.mapPerm π)` has a different *type*
from `γ : FeynmanSubgraph G`.

Path B keeps the ambient fixed, pays no type-cast cost, and maps
cleanly onto H4's coproduct design where `Γ : FeynmanGraphClass` is
first fixed, then the sum `∑_{γ ⊊ Γ}` ranges over its subgraphs. The
`c`-independence of `FeynmanSubgraphClass c` (well-definedness across
representatives of the ambient class) is a separate statement and is
deferred to Sprint C when it is actually needed by H4.

## Setoid: 3-field criterion avoiding HEq

A direct relation `γ₂ = γ₁.mapPerm π` between `FeynmanSubgraph G`
elements is ill-typed when `G.mapPerm π = G` is known only
propositionally: `γ₁.mapPerm π : FeynmanSubgraph (G.mapPerm π)`,
which is a defeq-distinct type from `FeynmanSubgraph G`.

We avoid this by comparing the three data fields directly
(`vertices`, `internalEdges`, `externalLegs`), which are
`FeynmanGraph`-agnostic (`Finset VertexId`,
`Multiset FeynmanEdge`, `Multiset ExternalLeg`). The well-formedness
proofs (`vertices_subset`, etc.) carry no mathematical content beyond
existence.

## Tag map (HOPF_DECOMPOSITION.md § H2)

* `[Def]` `FeynmanSubgraph.isoSetoid` — subgraph-level iso relation (H2.4 core)
* `[Def]` `FeynmanSubgraphClass` — H2.4 quotient carrier
* `[Def]` `FeynmanSubgraph.toSubgraphClass` — quotient injection

Later in this file (H2.1 / H2.2 / H2.5) we add the class-level
`contract` and `IsConnectedDivergent` predicates.
-/

namespace GaugeGeometry.QFT.Combinatorial

namespace FeynmanSubgraph

variable {G : FeynmanGraph}

/--
**H2.4 core** — Subgraph-iso relation on `FeynmanSubgraph G`: two
subgraphs of the same ambient `G` are equivalent when some vertex
permutation fixes `G` (as a `FeynmanGraph`) and carries one to the
other field-for-field.

The three conjuncts `vertices / internalEdges / externalLegs` are the
concrete `FeynmanSubgraph` fields. Comparing them directly — rather
than writing `γ₂ = γ₁.mapPerm π` — avoids the dependent-type mismatch
between `FeynmanSubgraph G` and `FeynmanSubgraph (G.mapPerm π)`.
-/
def IsIso (γ₁ γ₂ : FeynmanSubgraph G) : Prop :=
  ∃ π : Equiv.Perm VertexId,
    G.mapPerm π = G ∧
    γ₂.vertices = γ₁.vertices.image π ∧
    γ₂.internalEdges = γ₁.internalEdges.map (FeynmanEdge.map π) ∧
    γ₂.externalLegs = γ₁.externalLegs.map (ExternalLeg.map π)

theorem IsIso.refl (γ : FeynmanSubgraph G) : γ.IsIso γ := by
  refine ⟨1, G.mapPerm_one, ?_, ?_, ?_⟩
  · simp
  · -- `(FeynmanEdge.map 1) = id`
    simp [FeynmanEdge.map]
  · -- `(ExternalLeg.map 1) = id`
    simp [ExternalLeg.map]

theorem IsIso.symm {γ₁ γ₂ : FeynmanSubgraph G} (h : γ₁.IsIso γ₂) :
    γ₂.IsIso γ₁ := by
  rcases h with ⟨π, hG, hv, hi, he⟩
  refine ⟨π⁻¹, ?_, ?_, ?_, ?_⟩
  · -- `G.mapPerm π⁻¹ = G` follows from `G.mapPerm π = G`
    have : (G.mapPerm π).mapPerm π⁻¹ = G.mapPerm π⁻¹ := by
      rw [hG]
    have hinv : G.mapPerm π⁻¹ = G := by
      rw [← this]
      rw [← FeynmanGraph.mapPerm_mul]
      simp
    exact hinv
  · -- vertices
    rw [hv, Finset.image_image]
    have hcomp : (⇑π⁻¹ ∘ ⇑π) = (id : VertexId → VertexId) := by
      funext x; simp
    rw [hcomp, Finset.image_id]
  · -- internalEdges
    rw [hi, Multiset.map_map]
    have hcomp : (FeynmanEdge.map π⁻¹) ∘ (FeynmanEdge.map π) = id := by
      funext e
      cases e with
      | mk source target sector =>
        simp [FeynmanEdge.map, Function.comp]
    rw [hcomp, Multiset.map_id]
  · -- externalLegs
    rw [he, Multiset.map_map]
    have hcomp : (ExternalLeg.map π⁻¹) ∘ (ExternalLeg.map π) = id := by
      funext ℓ
      cases ℓ with
      | mk attachedTo sector =>
        simp [ExternalLeg.map, Function.comp]
    rw [hcomp, Multiset.map_id]

theorem IsIso.trans {γ₁ γ₂ γ₃ : FeynmanSubgraph G}
    (h₁ : γ₁.IsIso γ₂) (h₂ : γ₂.IsIso γ₃) : γ₁.IsIso γ₃ := by
  rcases h₁ with ⟨π, hG, hv, hi, he⟩
  rcases h₂ with ⟨σ, hG', hv', hi', he'⟩
  refine ⟨σ * π, ?_, ?_, ?_, ?_⟩
  · -- `G.mapPerm (σ * π) = G`
    rw [FeynmanGraph.mapPerm_mul, hG, hG']
  · -- vertices
    rw [hv', hv, Finset.image_image]
    rfl
  · -- internalEdges
    rw [hi', hi, Multiset.map_map]
    congr 1
  · -- externalLegs
    rw [he', he, Multiset.map_map]
    congr 1

theorem isIso_equivalence (G : FeynmanGraph) :
    Equivalence (IsIso : FeynmanSubgraph G → FeynmanSubgraph G → Prop) :=
  ⟨IsIso.refl, IsIso.symm, IsIso.trans⟩

/-- **H2.4** — the subgraph-iso setoid on `FeynmanSubgraph G`. -/
def isoSetoid (G : FeynmanGraph) : Setoid (FeynmanSubgraph G) where
  r := IsIso
  iseqv := isIso_equivalence G

end FeynmanSubgraph

/--
**H2.4 carrier** — Isomorphism classes of subgraphs of a *fixed*
ambient `G`. Per Path B, the ambient stays outside the quotient; the
coproduct in H4 will range over `FeynmanSubgraphClass Γ` for each
`Γ : FeynmanGraphClass` representative.
-/
def FeynmanSubgraphClass (G : FeynmanGraph) : Type :=
  Quotient (FeynmanSubgraph.isoSetoid G)

namespace FeynmanSubgraph

/-- Quotient map from a subgraph to its class. -/
def toSubgraphClass (γ : FeynmanSubgraph G) : FeynmanSubgraphClass G :=
  Quotient.mk (FeynmanSubgraph.isoSetoid G) γ

@[simp] theorem toSubgraphClass_eq_iff {γ₁ γ₂ : FeynmanSubgraph G} :
    γ₁.toSubgraphClass = γ₂.toSubgraphClass ↔ γ₁.IsIso γ₂ :=
  Quotient.eq

end FeynmanSubgraph

/-! ### H2.1 — Contract is well-defined on `FeynmanSubgraphClass`

Goal: `γ₁ ~_G γ₂ → γ₁.contract.IsIso γ₂.contract` as `FeynmanGraph`
(the `GraphIsomorphism.IsIso` of Sprint A).

**Key construction: `swapFixExtend`.** Given `π : Equiv.Perm VertexId`
with `G.mapPerm π = G`, we build `τ : Equiv.Perm VertexId` that:
* agrees with `π` on `G.vertices`,
* fixes `freshVertex G.vertices` (the Sprint-A chosen contraction star).

Then `γ₂.contract = γ₁.contract.mapPerm τ` holds *literally* as
`FeynmanGraph`, giving `γ₁.contract.IsIso γ₂.contract`.

`τ` is the composition `swap s (π s) * π` where `s = freshVertex G.vertices`.
Since `π` maps `G.vertices` bijectively to itself and `s ∉ G.vertices`,
we also have `π s ∉ G.vertices`, so the swap fixes `G.vertices`
pointwise and leaves `π`'s action on `G.vertices` unchanged.
-/

namespace FeynmanGraph

/--
`G.mapPerm π = G` implies `π` permutes `G.vertices` as a set.
Concretely `G.vertices.image π = G.vertices`.
-/
theorem vertices_image_of_mapPerm_eq {π : Equiv.Perm VertexId}
    {G : FeynmanGraph} (hG : G.mapPerm π = G) :
    G.vertices.image π = G.vertices := by
  have h1 : (G.mapPerm π).vertices = G.vertices := by rw [hG]
  -- `(G.mapPerm π).vertices = G.vertices.image π` definitionally.
  exact h1

/--
If `G.mapPerm π = G` and `v ∉ G.vertices`, then `π v ∉ G.vertices`.
(Permutations restricted to a finite invariant set stay there; therefore
the complement is also invariant.)
-/
theorem not_mem_vertices_of_mapPerm_eq {π : Equiv.Perm VertexId}
    {G : FeynmanGraph} (hG : G.mapPerm π = G)
    {v : VertexId} (hv : v ∉ G.vertices) : π v ∉ G.vertices := by
  intro hπv
  -- If `π v ∈ G.vertices = G.vertices.image π`, there is `w ∈ G.vertices`
  -- with `π w = π v`; by injectivity `w = v`, so `v ∈ G.vertices`.
  rw [← vertices_image_of_mapPerm_eq hG] at hπv
  rcases Finset.mem_image.mp hπv with ⟨w, hw, hwv⟩
  have : w = v := π.injective hwv
  exact hv (this ▸ hw)

end FeynmanGraph

namespace FeynmanSubgraph

/-- Local helper: injective `map` commutes with `Multiset` subtraction
when the subtrahend is a submultiset. Mathlib does not export this
directly; we prove it elementwise via `count`. -/
private theorem map_sub_of_injective {α β : Type*}
    [DecidableEq α] [DecidableEq β] {f : α → β}
    (hf : Function.Injective f) {A B : Multiset α} (hle : B ≤ A) :
    (A - B).map f = A.map f - B.map f := by
  refine Multiset.ext.mpr (fun y => ?_)
  rw [Multiset.count_sub]
  -- Want: (A - B).map f .count y = (A.map f).count y - (B.map f).count y
  by_cases hy : y ∈ A.map f
  · rcases Multiset.mem_map.mp hy with ⟨x, hxA, rfl⟩
    rw [Multiset.count_map_eq_count' _ _ hf,
        Multiset.count_map_eq_count' _ _ hf,
        Multiset.count_map_eq_count' _ _ hf,
        Multiset.count_sub]
  · -- y ∉ A.map f, so count is 0 on both sides. B.map f ≤ A.map f, so y ∉ B.map f too.
    have hBmap_le : B.map f ≤ A.map f := Multiset.map_le_map hle
    have hy_B : y ∉ B.map f := fun hyB => hy (Multiset.mem_of_le hBmap_le hyB)
    have hy_sub : y ∉ (A - B).map f := by
      intro h
      rcases Multiset.mem_map.mp h with ⟨x, hx, rfl⟩
      have hxA : x ∈ A := Multiset.mem_of_le (Multiset.sub_le_self _ _) hx
      exact hy (Multiset.mem_map.mpr ⟨x, hxA, rfl⟩)
    rw [Multiset.count_eq_zero_of_notMem hy_sub,
        Multiset.count_eq_zero_of_notMem hy,
        Multiset.count_eq_zero_of_notMem hy_B]

/--
Given `π` fixing `G` (as a `FeynmanGraph`) and a distinguished vertex
`s`, extend `π` to `τ := swap s (π s) * π`. This `τ` fixes `s` and
agrees with `π` everywhere that `π s ≠` (namely, on `G.vertices` when
`s = freshVertex G.vertices ∉ G.vertices`).
-/
def swapFixExtend (π : Equiv.Perm VertexId) (s : VertexId) :
    Equiv.Perm VertexId :=
  Equiv.swap s (π s) * π

theorem swapFixExtend_apply_fixed (π : Equiv.Perm VertexId) (s : VertexId) :
    swapFixExtend π s s = s := by
  unfold swapFixExtend
  simp [Equiv.swap_apply_right]

/--
On vertices whose image under `π` is neither `s` nor `π s`, `τ` and
`π` agree. We use this specialized to `v ∈ G.vertices` when
`s ∉ G.vertices`.
-/
theorem swapFixExtend_apply_of_not_mem
    {π : Equiv.Perm VertexId} {G : FeynmanGraph} (hG : G.mapPerm π = G)
    (s : VertexId) (hs : s ∉ G.vertices) {v : VertexId} (hv : v ∈ G.vertices) :
    swapFixExtend π s v = π v := by
  unfold swapFixExtend
  show Equiv.swap s (π s) (π v) = π v
  have hπv_mem : π v ∈ G.vertices := by
    rw [← FeynmanGraph.vertices_image_of_mapPerm_eq hG]
    exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
  have hne_s : π v ≠ s := fun h => hs (h ▸ hπv_mem)
  have hπs_notmem : π s ∉ G.vertices :=
    FeynmanGraph.not_mem_vertices_of_mapPerm_eq hG hs
  have hne_πs : π v ≠ π s := fun h => hπs_notmem (h ▸ hπv_mem)
  rw [Equiv.swap_apply_of_ne_of_ne hne_s hne_πs]

/--
`τ = swapFixExtend π s` still fixes `G` as a `FeynmanGraph`, provided
`s ∉ G.vertices` (so the swap is among complement vertices, invisible
to `G`).

This needs `G.WellFormed` because `G` is a raw `FeynmanGraph` (not
a bundled well-formed graph), and we need to know that every
edge/leg of `G` is supported on `G.vertices` to conclude that the
swap on complement vertices leaves `G.internalEdges` /
`G.externalLegs` unchanged. The `WellFormed` assumption is the
Sprint-A-standard pattern (cf. `mapPerm_wellFormed` in
`Permutation.lean`).
-/
theorem swapFixExtend_mapPerm_eq
    {π : Equiv.Perm VertexId} {G : FeynmanGraph} (hGwf : G.WellFormed)
    (hG : G.mapPerm π = G)
    {s : VertexId} (hs : s ∉ G.vertices) :
    G.mapPerm (swapFixExtend π s) = G := by
  -- Strategy: `swapFixExtend π s = swap s (π s) * π`, and
  -- `G.mapPerm (swap s (π s) * π) = (G.mapPerm π).mapPerm (swap s (π s))`
  -- = `G.mapPerm (swap s (π s))` by `hG`. Since `s, π s ∉ G.vertices`,
  -- `swap s (π s)` fixes all of `G.vertices` and (by well-formedness)
  -- all edges/legs of `G`.
  unfold swapFixExtend
  rw [FeynmanGraph.mapPerm_mul, hG]
  -- Now show `G.mapPerm (swap s (π s)) = G` by field equalities.
  have hπs_notmem : π s ∉ G.vertices :=
    FeynmanGraph.not_mem_vertices_of_mapPerm_eq hG hs
  set σ := Equiv.swap s (π s) with hσ_def
  have hfix : ∀ v ∈ G.vertices, σ v = v := by
    intro v hv
    have hv_ne_s : v ≠ s := fun h => hs (h ▸ hv)
    have hv_ne_πs : v ≠ π s := fun h => hπs_notmem (h ▸ hv)
    rw [hσ_def, Equiv.swap_apply_of_ne_of_ne hv_ne_s hv_ne_πs]
  -- Build the 3 field equalities.
  have hV : G.vertices.image σ = G.vertices := by
    ext w
    constructor
    · intro hw
      rcases Finset.mem_image.mp hw with ⟨v, hv, rfl⟩
      rwa [hfix v hv]
    · intro hw
      exact Finset.mem_image.mpr ⟨w, hw, hfix w hw⟩
  have hE : G.internalEdges.map (FeynmanEdge.map σ) = G.internalEdges := by
    rw [show G.internalEdges.map (FeynmanEdge.map σ)
          = G.internalEdges.map id from ?_]
    · simp
    · apply Multiset.map_congr rfl
      intro e he
      have hsupp := hGwf.1 e he
      have hs_mem : e.source ∈ G.vertices := by
        simp [FeynmanEdge.SupportedOn] at hsupp
        exact hsupp.1
      have ht_mem : e.target ∈ G.vertices := by
        simp [FeynmanEdge.SupportedOn] at hsupp
        exact hsupp.2
      cases e with
      | mk src tgt sec =>
        simp [FeynmanEdge.map, hfix src hs_mem, hfix tgt ht_mem]
  have hX : G.externalLegs.map (ExternalLeg.map σ) = G.externalLegs := by
    rw [show G.externalLegs.map (ExternalLeg.map σ)
          = G.externalLegs.map id from ?_]
    · simp
    · apply Multiset.map_congr rfl
      intro ℓ hℓ
      have hsupp := hGwf.2 ℓ hℓ
      have ha_mem : ℓ.attachedTo ∈ G.vertices := by
        simp [ExternalLeg.SupportedOn] at hsupp
        exact hsupp
      cases ℓ with
      | mk att sec =>
        simp [ExternalLeg.map, hfix att ha_mem]
  -- Now assemble the `FeynmanGraph.mapPerm` equality from field equalities.
  show (G.mapPerm σ : FeynmanGraph) = G
  apply FeynmanGraph.mk.injEq _ _ _ _ _ _ |>.mpr
  refine ⟨?_, ?_, ?_⟩
  · show G.vertices.image σ = G.vertices; exact hV
  · show G.internalEdges.map (FeynmanEdge.map σ) = G.internalEdges; exact hE
  · show G.externalLegs.map (ExternalLeg.map σ) = G.externalLegs; exact hX

/-! #### H2.1 main statement

For `γ₁ ~_G γ₂` under the Path-B relation, we build a permutation
`τ` (via `swapFixExtend` on the Sprint-A star `freshVertex G.vertices`)
such that `γ₂.contract = γ₁.contract.mapPerm τ` literally. This gives
`γ₁.contract.IsIso γ₂.contract` as `FeynmanGraph`s (Sprint-A
`FeynmanGraph.IsIso`), hence `γ₁.contract.toClass = γ₂.contract.toClass`.
-/

open FeynmanGraph in
/--
Contract commutes with the `swapFixExtend`-adjusted permutation, as a
literal `FeynmanGraph` equality, when the `IsIso` witness `π` maps
`γ₁` to `γ₂` field-for-field and `s = freshVertex G.vertices`.
-/
theorem contract_mapPerm_of_IsIso
    {G : FeynmanGraph} (hGwf : G.WellFormed)
    {γ₁ γ₂ : FeynmanSubgraph G}
    {π : Equiv.Perm VertexId}
    (hG : G.mapPerm π = G)
    (hV : γ₂.vertices = γ₁.vertices.image π)
    (hE : γ₂.internalEdges = γ₁.internalEdges.map (FeynmanEdge.map π))
    (_hX : γ₂.externalLegs = γ₁.externalLegs.map (ExternalLeg.map π)) :
    γ₂.contract =
      (γ₁.contract).mapPerm (swapFixExtend π (freshVertex G.vertices)) := by
  -- Shorthand.
  set s := freshVertex G.vertices with hs_def
  have hs_notmem : s ∉ G.vertices := FeynmanGraph.freshVertex_not_mem _
  -- `γ.contractedVertex = freshVertex G.vertices = s` for any subgraph γ of G.
  have hcv1 : γ₁.contractedVertex = s := rfl
  have hcv2 : γ₂.contractedVertex = s := rfl
  set τ := swapFixExtend π s with hτ_def
  have hτ_s : τ s = s := swapFixExtend_apply_fixed π s
  have hτ_onG : ∀ v ∈ G.vertices, τ v = π v := fun v hv =>
    swapFixExtend_apply_of_not_mem hG s hs_notmem hv
  -- Derive `γ₂.vertices ⊆ G.vertices` (from `vertices_subset`).
  have hγ₁_subset : γ₁.vertices ⊆ G.vertices := γ₁.vertices_subset
  have hτ_on_γ₁ : ∀ v ∈ γ₁.vertices, τ v = π v := fun v hv =>
    hτ_onG v (hγ₁_subset hv)
  -- We aim at the 3-field equality of `FeynmanGraph`s.
  -- Left: γ₂.contract = γ₂.contractWith s.
  -- Right: γ₁.contract.mapPerm τ = (γ₁.contractWith s).mapPerm τ.
  show γ₂.contractWith s =
    (γ₁.contractWith s : FeynmanGraph).mapPerm τ
  apply FeynmanGraph.mk.injEq _ _ _ _ _ _ |>.mpr
  refine ⟨?_, ?_, ?_⟩
  · -- vertices: (G.vertices \ γ₂.vertices) ∪ {s} = ((G.vertices \ γ₁.vertices) ∪ {s}).image τ
    show (G.vertices \ γ₂.vertices) ∪ {s} =
      ((G.vertices \ γ₁.vertices) ∪ {s}).image τ
    rw [Finset.image_union, Finset.image_singleton, hτ_s]
    congr 1
    -- (G.vertices \ γ₂.vertices) = (G.vertices \ γ₁.vertices).image τ
    ext w
    simp only [Finset.mem_sdiff, Finset.mem_image]
    constructor
    · rintro ⟨hwG, hw_notγ₂⟩
      -- w ∈ G.vertices, so w = τ (τ⁻¹ w). But τ agrees with π on G.vertices;
      -- easier: rewrite G.vertices = G.vertices.image τ (τ fixes G) and pick preimage.
      -- First, τ also fixes G as a FeynmanGraph.
      have hGτ : G.mapPerm τ = G := swapFixExtend_mapPerm_eq hGwf hG hs_notmem
      have hVτ : G.vertices.image τ = G.vertices :=
        FeynmanGraph.vertices_image_of_mapPerm_eq hGτ
      rw [← hVτ] at hwG
      rcases Finset.mem_image.mp hwG with ⟨v, hv, rfl⟩
      refine ⟨v, ⟨hv, ?_⟩, rfl⟩
      -- Need v ∉ γ₁.vertices. By hV, γ₂.vertices = γ₁.vertices.image π;
      -- and τ v = π v on G.vertices. So if v ∈ γ₁.vertices then τ v = π v ∈ γ₂.vertices.
      intro hv_γ₁
      apply hw_notγ₂
      rw [hV]
      rw [hτ_on_γ₁ v hv_γ₁]
      exact Finset.mem_image.mpr ⟨v, hv_γ₁, rfl⟩
    · rintro ⟨v, ⟨hvG, hv_notγ₁⟩, rfl⟩
      have hτv_mem : τ v ∈ G.vertices := by
        rw [hτ_onG v hvG]
        rw [← FeynmanGraph.vertices_image_of_mapPerm_eq hG]
        exact Finset.mem_image.mpr ⟨v, hvG, rfl⟩
      refine ⟨hτv_mem, ?_⟩
      -- τ v ∉ γ₂.vertices
      rw [hV, hτ_onG v hvG]
      intro h
      rcases Finset.mem_image.mp h with ⟨v', hv', hπeq⟩
      have : v' = v := π.injective hπeq
      exact hv_notγ₁ (this ▸ hv')
  · -- internalEdges: γ₂.complementEdges.map (retarget γ₂.vertices s)
    --              = ((γ₁.complementEdges.map (retarget γ₁.vertices s)).map (FeynmanEdge.map τ))
    show γ₂.complementEdges.map (FeynmanEdge.retarget γ₂.vertices s) =
      (γ₁.complementEdges.map (FeynmanEdge.retarget γ₁.vertices s)).map
        (FeynmanEdge.map τ)
    -- G.internalEdges is `(FeynmanEdge.map π)`-invariant from hG.
    have hGE : G.internalEdges.map (FeynmanEdge.map π) = G.internalEdges := by
      have : (G.mapPerm π).internalEdges = G.internalEdges := by rw [hG]
      exact this
    -- Key lemma: γ₂.complementEdges = γ₁.complementEdges.map (FeynmanEdge.map π)
    have hcompE : γ₂.complementEdges =
        γ₁.complementEdges.map (FeynmanEdge.map π) := by
      unfold complementEdges
      rw [hE]
      -- Want: G.I - γ₁.I.map π = (G.I - γ₁.I).map π
      -- Rewrite G.I on LHS as G.I.map π via hGE, then apply map_sub_of_injective.
      conv_lhs => rw [← hGE]
      exact (map_sub_of_injective
        (FeynmanGraph.FeynmanEdge_map_injective π)
        γ₁.internalEdges_le).symm
    rw [hcompE]
    rw [Multiset.map_map]
    rw [Multiset.map_map]
    -- Goal: (G.internalEdges - γ₁.internalEdges).map (retarget γ₂.vertices s ∘ FeynmanEdge.map π)
    --     = (G.internalEdges - γ₁.internalEdges).map (FeynmanEdge.map τ ∘ retarget γ₁.vertices s)
    apply Multiset.map_congr rfl
    intro e he
    -- Both sides: need to show retarget (γ₁.vertices.image π) s (e.map π)
    --                        = (retarget γ₁.vertices s e).map τ
    -- e lies in G.internalEdges - γ₁.internalEdges ≤ G.internalEdges, so its endpoints ∈ G.vertices.
    have he_inG : e ∈ G.internalEdges :=
      Multiset.mem_of_le (Multiset.sub_le_self _ _) he
    have hsupp := hGwf.1 e he_inG
    have hsrc_G : e.source ∈ G.vertices := by
      simp [FeynmanEdge.SupportedOn] at hsupp; exact hsupp.1
    have htgt_G : e.target ∈ G.vertices := by
      simp [FeynmanEdge.SupportedOn] at hsupp; exact hsupp.2
    show (FeynmanEdge.retarget γ₂.vertices s) ((FeynmanEdge.map π) e) =
      (FeynmanEdge.map τ) ((FeynmanEdge.retarget γ₁.vertices s) e)
    -- Break into field-wise comparison of FeynmanEdge.
    have hsrc_iff : (e.map π).source ∈ γ₂.vertices ↔ e.source ∈ γ₁.vertices := by
      simp [FeynmanEdge.map_source]
      rw [hV]
      constructor
      · intro h
        rcases Finset.mem_image.mp h with ⟨v, hv, hvπ⟩
        have : v = e.source := π.injective hvπ
        exact this ▸ hv
      · intro h
        exact Finset.mem_image.mpr ⟨e.source, h, rfl⟩
    have htgt_iff : (e.map π).target ∈ γ₂.vertices ↔ e.target ∈ γ₁.vertices := by
      simp [FeynmanEdge.map_target]
      rw [hV]
      constructor
      · intro h
        rcases Finset.mem_image.mp h with ⟨v, hv, hvπ⟩
        have : v = e.target := π.injective hvπ
        exact this ▸ hv
      · intro h
        exact Finset.mem_image.mpr ⟨e.target, h, rfl⟩
    -- Case split on whether e.source ∈ γ₁.vertices and similarly for target.
    cases e with
    | mk src tgt sec =>
      simp only [FeynmanEdge.map, FeynmanEdge.retarget]
      by_cases hsγ : src ∈ γ₁.vertices
      all_goals (by_cases htγ : tgt ∈ γ₁.vertices)
      · -- both in γ₁: both map to star s on both sides
        have hsLHS : (π src ∈ γ₂.vertices) := (hsrc_iff).mpr hsγ
        have htLHS : (π tgt ∈ γ₂.vertices) := (htgt_iff).mpr htγ
        simp [hsLHS, htLHS, hsγ, htγ, hτ_s]
      · -- src ∈ γ₁, tgt ∉ γ₁
        have hsLHS : (π src ∈ γ₂.vertices) := (hsrc_iff).mpr hsγ
        have htLHS : (π tgt ∉ γ₂.vertices) := fun h => htγ ((htgt_iff).mp h)
        simp [hsLHS, htLHS, hsγ, htγ, hτ_s]
        -- Now need: π tgt = τ tgt.
        -- tgt ∈ G.vertices (from hsupp), so τ tgt = π tgt.
        exact (hτ_onG tgt htgt_G).symm
      · -- src ∉ γ₁, tgt ∈ γ₁
        have hsLHS : (π src ∉ γ₂.vertices) := fun h => hsγ ((hsrc_iff).mp h)
        have htLHS : (π tgt ∈ γ₂.vertices) := (htgt_iff).mpr htγ
        simp [hsLHS, htLHS, hsγ, htγ, hτ_s]
        exact (hτ_onG src hsrc_G).symm
      · -- neither in γ₁
        have hsLHS : (π src ∉ γ₂.vertices) := fun h => hsγ ((hsrc_iff).mp h)
        have htLHS : (π tgt ∉ γ₂.vertices) := fun h => htγ ((htgt_iff).mp h)
        simp [hsLHS, htLHS, hsγ, htγ]
        refine ⟨?_, ?_⟩
        · exact (hτ_onG src hsrc_G).symm
        · exact (hτ_onG tgt htgt_G).symm
  · -- externalLegs: similar, even simpler (only attachedTo).
    show G.externalLegs.map (ExternalLeg.retarget γ₂.vertices s) =
      (G.externalLegs.map (ExternalLeg.retarget γ₁.vertices s)).map
        (ExternalLeg.map τ)
    -- Likewise: G.externalLegs = G.externalLegs.map (ExternalLeg.map π) by hG.
    have hGX : G.externalLegs.map (ExternalLeg.map π) = G.externalLegs := by
      have : (G.mapPerm π).externalLegs = G.externalLegs := by rw [hG]
      exact this
    -- Rewrite LHS's `G.externalLegs` (inside the outer `retarget` map) via `hGX.symm`.
    conv_lhs => rw [← hGX]
    rw [Multiset.map_map, Multiset.map_map]
    apply Multiset.map_congr rfl
    intro ℓ hℓ_mapped
    -- ℓ ∈ G.externalLegs.
    have hsupp := hGwf.2 ℓ hℓ_mapped
    have hatt_G : ℓ.attachedTo ∈ G.vertices := by
      simp [ExternalLeg.SupportedOn] at hsupp; exact hsupp
    show (ExternalLeg.retarget γ₂.vertices s) ((ExternalLeg.map π) ℓ) =
      (ExternalLeg.map τ) ((ExternalLeg.retarget γ₁.vertices s) ℓ)
    have hatt_iff :
        (ℓ.map π).attachedTo ∈ γ₂.vertices ↔ ℓ.attachedTo ∈ γ₁.vertices := by
      simp [ExternalLeg.map]
      rw [hV]
      constructor
      · intro h
        rcases Finset.mem_image.mp h with ⟨v, hv, hvπ⟩
        have : v = ℓ.attachedTo := π.injective hvπ
        exact this ▸ hv
      · intro h
        exact Finset.mem_image.mpr ⟨ℓ.attachedTo, h, rfl⟩
    cases ℓ with
    | mk att sec =>
      simp only [ExternalLeg.map, ExternalLeg.retarget]
      by_cases hattγ : att ∈ γ₁.vertices
      · have hLHS : π att ∈ γ₂.vertices := (hatt_iff).mpr hattγ
        simp [hLHS, hattγ, hτ_s]
      · have hLHS : π att ∉ γ₂.vertices := fun h => hattγ ((hatt_iff).mp h)
        simp [hLHS, hattγ]
        exact (hτ_onG att hatt_G).symm

/--
**H2.1** — `contract` is well-defined on subgraph iso-classes:
subgraph-equivalent `γ₁`, `γ₂` produce graph-isomorphic contractions.

This is the `FeynmanGraph.IsIso` form used to feed into `Quotient.lift`
for the class-level `contract` (H2.2).
-/
theorem IsIso.contract_isIso
    {G : FeynmanGraph} (hGwf : G.WellFormed)
    {γ₁ γ₂ : FeynmanSubgraph G} (hIso : γ₁.IsIso γ₂) :
    γ₁.contract.IsIso γ₂.contract := by
  rcases hIso with ⟨π, hG, hV, hE, hX⟩
  refine ⟨swapFixExtend π (FeynmanGraph.freshVertex G.vertices), ?_⟩
  exact contract_mapPerm_of_IsIso hGwf hG hV hE hX

/--
**H2.1 corollary** — At the class level, `γ.contract.toClass` is the
same `FeynmanGraphClass` for equivalent subgraphs.
-/
theorem toClass_contract_of_IsIso
    {G : FeynmanGraph} (hGwf : G.WellFormed)
    {γ₁ γ₂ : FeynmanSubgraph G} (hIso : γ₁.IsIso γ₂) :
    γ₁.contract.toClass = γ₂.contract.toClass := by
  apply Quotient.sound
  exact IsIso.contract_isIso hGwf hIso

end FeynmanSubgraph

/-! ### H2.2 — Class-level `contract` via `Quotient.lift` -/

namespace FeynmanSubgraphClass

/--
**H2.2** — Contract a subgraph *class* to a `FeynmanGraphClass`. The
ambient `G` and its well-formedness witness `hGwf` are carried as
parameters, consistent with Path B (ambient-family).

`Quotient.lift` discharges the well-definedness obligation through
`FeynmanSubgraph.toClass_contract_of_IsIso` (H2.1 corollary).
-/
def contract {G : FeynmanGraph} (hGwf : G.WellFormed) :
    FeynmanSubgraphClass G → FeynmanGraphClass :=
  Quotient.lift (fun γ : FeynmanSubgraph G => γ.contract.toClass)
    (fun _ _ h => FeynmanSubgraph.toClass_contract_of_IsIso hGwf h)

@[simp] theorem contract_toSubgraphClass
    {G : FeynmanGraph} (hGwf : G.WellFormed)
    (γ : FeynmanSubgraph G) :
    contract hGwf γ.toSubgraphClass = γ.contract.toClass := rfl

/-! #### H2.3 — Class-level `internalEdgeCount` decreases under `contract`

`FeynmanGraphClass.internalEdgeCount` is already isomorphism-invariant
(see `GraphIsomorphism.lean`). We expose the strict-decrease witness
at the class level: contracting a class-level subgraph (via H2.2)
reduces `internalEdgeCount`, provided the underlying subgraph has at
least one internal edge (the natural Hopf-side condition).
-/

theorem internalEdgeCount_contract_lt
    {G : FeynmanGraph} (hGwf : G.WellFormed) (γ : FeynmanSubgraph G)
    (hEdges : 0 < γ.internalEdges.card) :
    (contract hGwf γ.toSubgraphClass).internalEdgeCount <
      G.toClass.internalEdgeCount := by
  -- Reduce to the Sprint A fact `internalEdgeCount_contract` + `card_sub`.
  show (γ.contract.toClass : FeynmanGraphClass).internalEdgeCount <
    G.toClass.internalEdgeCount
  -- FeynmanGraphClass.internalEdgeCount at a class is the underlying value.
  show γ.contract.internalEdgeCount < G.internalEdgeCount
  rw [FeynmanSubgraph.internalEdgeCount_contract]
  have hle : γ.internalEdges ≤ G.internalEdges := γ.internalEdges_le
  rw [Multiset.card_sub hle]
  have hCardLe : γ.internalEdges.card ≤ G.internalEdges.card :=
    Multiset.card_le_card hle
  unfold FeynmanGraph.internalEdgeCount
  omega

end FeynmanSubgraphClass

/-! ### H2.5 — Class-level `IsConnectedDivergent` on `FeynmanSubgraphClass`

The Connes–Kreimer coproduct sums over *proper connected divergent*
subgraphs of `Γ`. Sprint B' lifted `contract` to `FeynmanSubgraphClass`
(H2.2); here we lift the index-set predicate
`IsConnectedDivergent` along the same `Quotient` carrier.

**Path-Sub strategy (2026-04-24):** delegate to the existing
`FeynmanSubgraph.IsConnectedDivergent` definition (which is a
conjunction of `IsConnected`, `IsOnePI`, `IsDivergent` on
`FeynmanSubgraph G`). Permutation invariance of each of the three
conjuncts is supplied by Sprint A + `IsPermInvariantDivergence`.

The key technical bridge is
`mapPerm_toFeynmanGraph` — the underlying `FeynmanGraph` commutes with
`mapPerm` — which lets us quote the Sprint A permutation-invariance
lemmas (`mapPerm_isSupportConnected_iff`, `mapPerm_isOnePI_iff`) on the
`toFeynmanGraph` projection.
-/

namespace FeynmanSubgraph

variable {G : FeynmanGraph}

/-- The underlying `FeynmanGraph` of a permuted subgraph equals the
permuted underlying graph. Field-wise `rfl` after unfolding. -/
@[simp] theorem mapPerm_toFeynmanGraph (π : Equiv.Perm VertexId)
    (γ : FeynmanSubgraph G) :
    (γ.mapPerm π).toFeynmanGraph = γ.toFeynmanGraph.mapPerm π := rfl

/-- Under the Path-B iso relation on `FeynmanSubgraph G`, the
underlying `FeynmanGraph` of `γ₂` is obtained from that of `γ₁` by the
witness permutation `π` (as raw `FeynmanGraph`s). -/
theorem toFeynmanGraph_eq_mapPerm_of_IsIso
    {γ₁ γ₂ : FeynmanSubgraph G} (h : γ₁.IsIso γ₂) :
    ∃ π : Equiv.Perm VertexId,
      γ₂.toFeynmanGraph = γ₁.toFeynmanGraph.mapPerm π := by
  rcases h with ⟨π, _hG, hV, hI, hE⟩
  refine ⟨π, ?_⟩
  apply FeynmanGraph.mk.injEq _ _ _ _ _ _ |>.mpr
  refine ⟨?_, ?_, ?_⟩
  · show γ₂.vertices = γ₁.vertices.image π; exact hV
  · show γ₂.internalEdges = γ₁.internalEdges.map (FeynmanEdge.map π); exact hI
  · show γ₂.externalLegs = γ₁.externalLegs.map (ExternalLeg.map π); exact hE

/-- `IsConnected` is invariant under the Path-B iso relation. -/
theorem IsIso.isConnected_iff
    {γ₁ γ₂ : FeynmanSubgraph G} (h : γ₁.IsIso γ₂) :
    γ₁.IsConnected ↔ γ₂.IsConnected := by
  obtain ⟨π, hEq⟩ := toFeynmanGraph_eq_mapPerm_of_IsIso h
  unfold IsConnected
  rw [hEq, FeynmanGraph.mapPerm_isSupportConnected_iff]

/-- `IsOnePI` is invariant under the Path-B iso relation. -/
theorem IsIso.isOnePI_iff
    {γ₁ γ₂ : FeynmanSubgraph G} (h : γ₁.IsIso γ₂) :
    γ₁.IsOnePI ↔ γ₂.IsOnePI := by
  obtain ⟨π, hEq⟩ := toFeynmanGraph_eq_mapPerm_of_IsIso h
  unfold IsOnePI
  rw [hEq, FeynmanGraph.mapPerm_isOnePI_iff]

end FeynmanSubgraph

/-! #### Iso-invariant divergence typeclass

`IsPermInvariantDivergence` from Sprint A is set up for the
cross-ambient transport `γ : FeynmanSubgraph G ↦ γ.mapPerm π :
FeynmanSubgraph (G.mapPerm π)` and requires both a `DivergenceMeasure G`
and a `DivergenceMeasure (G.mapPerm π)` instance. The H2.5 use case is
the *intra-ambient* case: `γ₁, γ₂ : FeynmanSubgraph G` with a witness
`G.mapPerm π = G`. Rather than forcing the Sprint A typeclass to
synthesise the ambient-collapsed instance (which requires
`hG ▸`-transport of instances that `subst` cannot discharge because
`G.mapPerm π = G` has `G` in the LHS), we add the natural intra-ambient
counterpart.

A concrete `DivergenceMeasure` satisfying `IsPermInvariantDivergence`
implies `IsIsoInvariantDivergence` by a separate bridge lemma
(deferred — not needed in Sprint C).
-/

/--
Divergence measures that are invariant under the Path-B subgraph-iso
relation on `FeynmanSubgraph G` (i.e., subgraphs of the same ambient
`G` related by a `G`-fixing vertex permutation have equal divergence
degree).

This is the intra-ambient counterpart of `IsPermInvariantDivergence`;
the two are logically compatible (the concrete MSSM-style measures
satisfy both), but H2.5 needs this formulation because the Path-B iso
relation stays inside one `FeynmanSubgraph G` type.
-/
class IsIsoInvariantDivergence (G : FeynmanGraph) [DivergenceMeasure G] :
    Prop where
  degree_iso :
    ∀ {γ₁ γ₂ : FeynmanSubgraph G}, γ₁.IsIso γ₂ →
      γ₁.divergenceDegree = γ₂.divergenceDegree

namespace FeynmanSubgraph

variable {G : FeynmanGraph}

/-- `IsDivergent` is invariant under the Path-B iso relation, given
`IsIsoInvariantDivergence G`. -/
theorem IsIso.isDivergent_iff
    [DivergenceMeasure G] [IsIsoInvariantDivergence G]
    {γ₁ γ₂ : FeynmanSubgraph G} (h : γ₁.IsIso γ₂) :
    γ₁.IsDivergent ↔ γ₂.IsDivergent := by
  unfold IsDivergent
  rw [IsIsoInvariantDivergence.degree_iso h]

/-- `IsConnectedDivergent` is invariant under the Path-B iso relation. -/
theorem IsIso.isConnectedDivergent_iff
    [DivergenceMeasure G] [IsIsoInvariantDivergence G]
    {γ₁ γ₂ : FeynmanSubgraph G} (h : γ₁.IsIso γ₂) :
    γ₁.IsConnectedDivergent ↔ γ₂.IsConnectedDivergent := by
  unfold IsConnectedDivergent
  rw [h.isConnected_iff, h.isOnePI_iff, h.isDivergent_iff]

end FeynmanSubgraph

/-! #### H2.5 — class-level predicate via `Quotient.lift`

The predicate lifts mechanically now that `IsIso.isConnectedDivergent_iff`
discharges the well-definedness obligation.
-/

namespace FeynmanSubgraphClass

variable {G : FeynmanGraph}

/--
**H2.5** — `IsConnectedDivergent` at the subgraph-class level. A
`FeynmanSubgraphClass G` is connected-divergent iff any (hence every)
representative is.
-/
def IsConnectedDivergent
    [DivergenceMeasure G] [IsIsoInvariantDivergence G] :
    FeynmanSubgraphClass G → Prop :=
  Quotient.lift FeynmanSubgraph.IsConnectedDivergent
    (fun _ _ h => propext (FeynmanSubgraph.IsIso.isConnectedDivergent_iff h))

@[simp] theorem isConnectedDivergent_toSubgraphClass
    [DivergenceMeasure G] [IsIsoInvariantDivergence G]
    (γ : FeynmanSubgraph G) :
    IsConnectedDivergent γ.toSubgraphClass ↔ γ.IsConnectedDivergent := Iff.rfl

end FeynmanSubgraphClass

end GaugeGeometry.QFT.Combinatorial
