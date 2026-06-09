import GaugeGeometry.QFT.HopfAlgebra.ResolvedCoproduct

/-!
# Canonical resolved payload model (Track R-4-full, Phase 6c)

The non-vacuity capstone: a *canonical* construction of resolved witnesses by the
constant-id lift `ofFlat…` (decorate every flat edge/leg with `edgeId/legId = ⟨0⟩`).
Because the coproduct/coassoc transfer (Phases 2–5) never uses `EdgeIdsUnique`, the
constant-id lift suffices and is fully canonical (no choice): a flat subgraph lifts
by a plain `Multiset.map`, and `forget` round-trips definitionally up to
`Multiset.map id = id`.

Phase 6c builds, per generator, a `ResolvedHopfPayload`, hence a
`ResolvedHopfPayloadFamily` — so the resolved coproduct of Phase 4c is **inhabited**
for every generator.
-/

set_option linter.unusedSectionVars false

namespace GaugeGeometry.QFT.Combinatorial

variable {Gf : FeynmanGraph}

/-- Constant-id lift of a flat edge. -/
def ofFlatEdge (e : FeynmanEdge) : ResolvedFeynmanEdge :=
  { edgeId := ⟨0⟩, source := e.source, target := e.target, sector := e.sector }

/-- Constant-id lift of a flat external leg. -/
def ofFlatLeg (ℓ : ExternalLeg) : ResolvedExternalLeg :=
  { legId := ⟨0⟩, attachedTo := ℓ.attachedTo, sector := ℓ.sector }

@[simp] theorem forget_ofFlatEdge (e : FeynmanEdge) : (ofFlatEdge e).forget = e := rfl
@[simp] theorem forget_ofFlatLeg (ℓ : ExternalLeg) : (ofFlatLeg ℓ).forget = ℓ := rfl

theorem forget_comp_ofFlatEdge : ResolvedFeynmanEdge.forget ∘ ofFlatEdge = id := rfl
theorem forget_comp_ofFlatLeg : ResolvedExternalLeg.forget ∘ ofFlatLeg = id := rfl

/-- Constant-id lift of a flat graph. -/
def ofFlatGraph (Gf : FeynmanGraph) : ResolvedFeynmanGraph :=
  { vertices := Gf.vertices
    internalEdges := Gf.internalEdges.map ofFlatEdge
    externalLegs := Gf.externalLegs.map ofFlatLeg }

@[simp] theorem ofFlatGraph_vertices (Gf : FeynmanGraph) :
    (ofFlatGraph Gf).vertices = Gf.vertices := rfl
@[simp] theorem ofFlatGraph_internalEdges (Gf : FeynmanGraph) :
    (ofFlatGraph Gf).internalEdges = Gf.internalEdges.map ofFlatEdge := rfl
@[simp] theorem ofFlatGraph_externalLegs (Gf : FeynmanGraph) :
    (ofFlatGraph Gf).externalLegs = Gf.externalLegs.map ofFlatLeg := rfl

/-- `forget` round-trips on the canonical graph lift. -/
theorem forget_ofFlatGraph (Gf : FeynmanGraph) : (ofFlatGraph Gf).forget = Gf := by
  show ResolvedFeynmanGraph.forget _ = _
  unfold ResolvedFeynmanGraph.forget ofFlatGraph
  have hi : (Gf.internalEdges.map ofFlatEdge).map ResolvedFeynmanEdge.forget = Gf.internalEdges := by
    rw [Multiset.map_map, forget_comp_ofFlatEdge, Multiset.map_id]
  have hl : (Gf.externalLegs.map ofFlatLeg).map ResolvedExternalLeg.forget = Gf.externalLegs := by
    rw [Multiset.map_map, forget_comp_ofFlatLeg, Multiset.map_id]
  rw [hi, hl]

/-- Constant-id lift of a flat subgraph. -/
def ofFlatSubgraph (γ : FeynmanSubgraph Gf) : ResolvedFeynmanSubgraph (ofFlatGraph Gf) where
  vertices := γ.vertices
  internalEdges := γ.internalEdges.map ofFlatEdge
  externalLegs := γ.externalLegs.map ofFlatLeg
  vertices_subset := γ.vertices_subset
  internalEdges_le := Multiset.map_le_map γ.internalEdges_le
  externalLegs_le := Multiset.map_le_map γ.externalLegs_le
  edges_supported := by
    intro e' he'
    obtain ⟨e, he, rfl⟩ := Multiset.mem_map.mp he'
    simpa [ofFlatEdge, FeynmanEdge.SupportedOn] using γ.edges_supported e he
  legs_supported := by
    intro ℓ' hℓ'
    obtain ⟨ℓ, hℓ, rfl⟩ := Multiset.mem_map.mp hℓ'
    simpa [ofFlatLeg, ExternalLeg.SupportedOn] using γ.legs_supported ℓ hℓ

/-- Carrier-level `forget` round-trip for the subgraph lift (the carrier fields are
graph-independent types, so these typecheck without graph transport). -/
@[simp] theorem forget_ofFlatSubgraph_vertices (γ : FeynmanSubgraph Gf) :
    (ofFlatSubgraph γ).forget.vertices = γ.vertices := rfl

@[simp] theorem forget_ofFlatSubgraph_internalEdges (γ : FeynmanSubgraph Gf) :
    (ofFlatSubgraph γ).forget.internalEdges = γ.internalEdges := by
  show (γ.internalEdges.map ofFlatEdge).map ResolvedFeynmanEdge.forget = γ.internalEdges
  rw [Multiset.map_map, forget_comp_ofFlatEdge, Multiset.map_id]

@[simp] theorem forget_ofFlatSubgraph_externalLegs (γ : FeynmanSubgraph Gf) :
    (ofFlatSubgraph γ).forget.externalLegs = γ.externalLegs := by
  show (γ.externalLegs.map ofFlatLeg).map ResolvedExternalLeg.forget = γ.externalLegs
  rw [Multiset.map_map, forget_comp_ofFlatLeg, Multiset.map_id]

/-! ### Phase 6c-2 — connected-divergence transfer for the subgraph lift

`IsConnected`/`IsOnePI` depend only on `toFeynmanGraph` (carrier), so transfer by
rewriting the carrier-graph equality.  `IsDivergent` depends on the ambient
`DivergenceMeasure`; it transfers via `IsAmbientInvariantDivergence` (degree of a
subgraph equals the degree of the self-subgraph of its own intrinsic graph). -/

variable [∀ H : FeynmanGraph, DivergenceMeasure H]
         [∀ H : FeynmanGraph, IsPermInvariantDivergence H]
         [∀ H : FeynmanGraph, IsIsoInvariantDivergence H]
         [∀ H : FeynmanGraph, Fintype (FeynmanSubgraph H)]
         [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
         [IsDivergencePreservedByAdmissibleForestContract]

/-- The forgotten subgraph lift has the same intrinsic graph as the original
(carrier-level, no graph transport). -/
theorem forget_ofFlatSubgraph_toFeynmanGraph (δ : FeynmanSubgraph Gf) :
    (ofFlatSubgraph δ).forget.toFeynmanGraph = δ.toFeynmanGraph := by
  simp only [FeynmanSubgraph.toFeynmanGraph, forget_ofFlatSubgraph_vertices,
    forget_ofFlatSubgraph_internalEdges, forget_ofFlatSubgraph_externalLegs]

theorem forget_ofFlatSubgraph_isConnected (δ : FeynmanSubgraph Gf) :
    (ofFlatSubgraph δ).forget.IsConnected ↔ δ.IsConnected := by
  unfold FeynmanSubgraph.IsConnected
  rw [forget_ofFlatSubgraph_toFeynmanGraph]

theorem forget_ofFlatSubgraph_isOnePI (δ : FeynmanSubgraph Gf) :
    (ofFlatSubgraph δ).forget.IsOnePI ↔ δ.IsOnePI := by
  unfold FeynmanSubgraph.IsOnePI
  rw [forget_ofFlatSubgraph_toFeynmanGraph]

/-- Degree of a self-subgraph depends only on the (equal) ambient graph. -/
private theorem degree_self_eq_of_graph_eq {g₁ g₂ : FeynmanGraph} (h : g₁ = g₂)
    (wf₁ : g₁.WellFormed) (wf₂ : g₂.WellFormed) :
    DivergenceMeasure.degree (FeynmanSubgraph.self g₁ wf₁) =
      DivergenceMeasure.degree (FeynmanSubgraph.self g₂ wf₂) := by
  subst h; rfl

/-- The divergence degree is preserved by the subgraph lift, via
`IsAmbientInvariantDivergence` (both equal the degree of the self-subgraph of the
common intrinsic graph). -/
theorem forget_ofFlatSubgraph_degree (δ : FeynmanSubgraph Gf) :
    DivergenceMeasure.degree ((ofFlatSubgraph δ).forget) = DivergenceMeasure.degree δ := by
  rw [← IsAmbientInvariantDivergence.degree_self_eq ((ofFlatSubgraph δ).forget),
      ← IsAmbientInvariantDivergence.degree_self_eq δ]
  exact degree_self_eq_of_graph_eq (forget_ofFlatSubgraph_toFeynmanGraph δ) _ _

/-- **CD transfer (Phase 6c-2 headline).**  A connected-divergent flat subgraph
lifts to a connected-divergent resolved subgraph (after forgetting).  This is the
field needed for `ofFlatForest.isConnectedDivergent`. -/
theorem forget_ofFlatSubgraph_isConnectedDivergent {δ : FeynmanSubgraph Gf}
    (hδ : δ.IsConnectedDivergent) :
    (ofFlatSubgraph δ).forget.IsConnectedDivergent := by
  obtain ⟨hc, ho, hd⟩ := hδ
  refine ⟨(forget_ofFlatSubgraph_isConnected δ).mpr hc,
          (forget_ofFlatSubgraph_isOnePI δ).mpr ho, ?_⟩
  have hd' : (0 : Int) ≤ DivergenceMeasure.degree δ := hd
  show (0 : Int) ≤ DivergenceMeasure.degree ((ofFlatSubgraph δ).forget)
  rw [forget_ofFlatSubgraph_degree]; exact hd'

/-! ### Phase 6c-3 — canonical payload family

DecidableEq for resolved subgraphs (for `Finset.image`), the forest lift, the
proper-forest transfer, the canonical cover, and the inhabited payload family. -/

/-- Resolved subgraphs are compared by their carrier fields (proof fields are
proof-irrelevant), mirroring the flat `FeynmanSubgraph` instance. -/
instance (G : ResolvedFeynmanGraph) : DecidableEq (ResolvedFeynmanSubgraph G) := by
  classical
  intro γ₁ γ₂
  by_cases hV : γ₁.vertices = γ₂.vertices
  · by_cases hI : γ₁.internalEdges = γ₂.internalEdges
    · by_cases hE : γ₁.externalLegs = γ₂.externalLegs
      · refine isTrue ?_
        cases γ₁; cases γ₂; cases hV; cases hI; cases hE; rfl
      · exact isFalse (fun h => hE (by rw [h]))
    · exact isFalse (fun h => hI (by rw [h]))
  · exact isFalse (fun h => hV (by rw [h]))

/-- `ofFlatEdge` / `ofFlatLeg` are injective (they only add a constant id). -/
theorem ofFlatEdge_injective : Function.Injective ofFlatEdge := by
  intro e₁ e₂ h
  have hs : e₁.source = e₂.source := congrArg ResolvedFeynmanEdge.source h
  have ht : e₁.target = e₂.target := congrArg ResolvedFeynmanEdge.target h
  have hsec : e₁.sector = e₂.sector := congrArg ResolvedFeynmanEdge.sector h
  cases e₁; cases e₂; simp_all

theorem ofFlatLeg_injective : Function.Injective ofFlatLeg := by
  intro ℓ₁ ℓ₂ h
  have ha : ℓ₁.attachedTo = ℓ₂.attachedTo := congrArg ResolvedExternalLeg.attachedTo h
  have hsec : ℓ₁.sector = ℓ₂.sector := congrArg ResolvedExternalLeg.sector h
  cases ℓ₁; cases ℓ₂; simp_all

/-- `ofFlatSubgraph` is injective (carrier-wise; `ofFlatEdge`/`ofFlatLeg` injective). -/
theorem ofFlatSubgraph_injective : Function.Injective (ofFlatSubgraph (Gf := Gf)) := by
  intro δ₁ δ₂ h
  have hv : δ₁.vertices = δ₂.vertices := congrArg ResolvedFeynmanSubgraph.vertices h
  have hi : δ₁.internalEdges = δ₂.internalEdges :=
    Multiset.map_injective ofFlatEdge_injective (congrArg ResolvedFeynmanSubgraph.internalEdges h)
  have he : δ₁.externalLegs = δ₂.externalLegs :=
    Multiset.map_injective ofFlatLeg_injective (congrArg ResolvedFeynmanSubgraph.externalLegs h)
  cases δ₁; cases δ₂; cases hv; cases hi; cases he; rfl

/-- The constant-id lift of a flat (pairwise-disjoint) admissible forest. -/
noncomputable def ofFlatForest (A : AdmissibleSubgraph Gf) (hDisj : A.IsPairwiseDisjoint) :
    ResolvedAdmissibleSubgraph (ofFlatGraph Gf) where
  elements := A.elements.image ofFlatSubgraph
  isConnectedDivergent := by
    intro γ hγ
    obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.mp hγ
    exact forget_ofFlatSubgraph_isConnectedDivergent (A.isConnectedDivergent_of_mem hδ)
  pairwiseDisjoint := by
    intro γ₁ h₁ γ₂ h₂ hne
    obtain ⟨δ₁, hδ₁, rfl⟩ := Finset.mem_image.mp h₁
    obtain ⟨δ₂, hδ₂, rfl⟩ := Finset.mem_image.mp h₂
    exact hDisj hδ₁ hδ₂ (fun h => hne (by rw [h]))

@[simp] theorem ofFlatForest_elements (A : AdmissibleSubgraph Gf) (hDisj : A.IsPairwiseDisjoint) :
    (ofFlatForest A hDisj).elements = A.elements.image ofFlatSubgraph := rfl

/-- `Multiset.map ofFlatEdge` commutes with a `Finset.sum` of edge multisets. -/
private theorem map_ofFlatEdge_finset_sum (s : Finset (FeynmanSubgraph Gf)) :
    (∑ δ ∈ s, δ.internalEdges).map ofFlatEdge = ∑ δ ∈ s, δ.internalEdges.map ofFlatEdge := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert δ s hδs ih => rw [Finset.sum_insert hδs, Finset.sum_insert hδs, Multiset.map_add, ih]

/-- The aggregate internal edges of the forest lift are the `ofFlatEdge`-image of
the flat forest's internal edges. -/
theorem ofFlatForest_internalEdges_eq (A : AdmissibleSubgraph Gf) (hDisj : A.IsPairwiseDisjoint) :
    (ofFlatForest A hDisj).internalEdges = A.internalEdges.map ofFlatEdge := by
  show (∑ γ ∈ (ofFlatForest A hDisj).elements, γ.internalEdges) = A.internalEdges.map ofFlatEdge
  rw [ofFlatForest_elements,
    Finset.sum_image (fun δ₁ _ δ₂ _ h => ofFlatSubgraph_injective h)]
  conv_rhs => rw [show A.internalEdges = ∑ δ ∈ A.elements, δ.internalEdges from rfl,
    map_ofFlatEdge_finset_sum]
  exact Finset.sum_congr rfl (fun δ _ => rfl)

/-- **Proper-forest transfer.**  The lift of a flat proper forest is a resolved
proper forest.  Each of the five `IsProperForest` conditions transfers from the
flat proper-index membership (nonemptiness/positive-edges via carrier round-trips;
complement positivity via `internalEdges_le` + cardinality). -/
theorem ofFlatForest_isProperForest {g : HopfGen}
    {A : AdmissibleSubgraph (repG g).toFeynmanGraph}
    (hA : A ∈ forestCoproductProperForestIndex g) (hDisj : A.IsPairwiseDisjoint) :
    (ofFlatForest A hDisj).IsProperForest := by
  rw [mem_forestCoproductProperForestIndex] at hA
  obtain ⟨hpd, hcompl⟩ := hA
  rw [FeynmanGraph.mem_properDisjointAdmissibleDivergentSubgraphs] at hpd
  obtain ⟨hnd, hhnc, hiec, hhpiec⟩ := hpd
  rw [FeynmanGraph.mem_nonemptyDisjointAdmissibleDivergentSubgraphs] at hnd
  obtain ⟨_, hne⟩ := hnd
  refine ⟨hne.image _, ?_, ?_, ?_, ?_⟩
  · intro γ hγ
    obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.mp hγ
    have hδne := hhnc δ hδ
    simpa [ResolvedFeynmanSubgraph.IsNonempty, ResolvedFeynmanSubgraph.vertexCount,
      FeynmanSubgraph.IsNonempty, FeynmanSubgraph.vertexCount] using hδne
  · rw [ofFlatForest_internalEdges_eq, Multiset.card_map]; exact hiec
  · intro γ hγ
    obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.mp hγ
    have := hhpiec δ hδ
    rwa [show (ofFlatSubgraph δ).internalEdges = δ.internalEdges.map ofFlatEdge from rfl,
      Multiset.card_map]
  · have hle : A.internalEdges ≤ (repG g).toFeynmanGraph.internalEdges :=
      admissibleSubgraph_internalEdges_le_of_pairwise A hDisj
    have hcard : (ofFlatForest A hDisj).complementEdges.card = A.complementEdges.card := by
      show ((ofFlatGraph (repG g).toFeynmanGraph).internalEdges
          - (ofFlatForest A hDisj).internalEdges).card
          = ((repG g).toFeynmanGraph.internalEdges - A.internalEdges).card
      rw [ofFlatForest_internalEdges_eq, ofFlatGraph_internalEdges,
        Multiset.card_sub (Multiset.map_le_map hle), Multiset.card_sub hle,
        Multiset.card_map, Multiset.card_map]
    rw [hcard]; exact hcompl

/-! ### Phase 6c-3 — lift over `G.forget` (transport-free cover)

To build the cover without graph transport, lift subgraphs/forests of
`(ofFlatGraph Gf).forget` itself (the graph the forgetful map lands in), so the
round-trip `forget ∘ lift = id` is a *same-type* equality. -/

/-- Lift a subgraph of `(ofFlatGraph Gf).forget` to a resolved subgraph of
`ofFlatGraph Gf` (decorate edges/legs with id `⟨0⟩`). -/
def liftFromForgetSubgraph (γf : FeynmanSubgraph (ofFlatGraph Gf).forget) :
    ResolvedFeynmanSubgraph (ofFlatGraph Gf) where
  vertices := γf.vertices
  internalEdges := γf.internalEdges.map ofFlatEdge
  externalLegs := γf.externalLegs.map ofFlatLeg
  vertices_subset := γf.vertices_subset
  internalEdges_le := by
    have h : γf.internalEdges ≤ Gf.internalEdges := by
      have hle := γf.internalEdges_le
      rwa [congrArg FeynmanGraph.internalEdges (forget_ofFlatGraph Gf)] at hle
    rw [ofFlatGraph_internalEdges]; exact Multiset.map_le_map h
  externalLegs_le := by
    have h : γf.externalLegs ≤ Gf.externalLegs := by
      have hle := γf.externalLegs_le
      rwa [congrArg FeynmanGraph.externalLegs (forget_ofFlatGraph Gf)] at hle
    rw [ofFlatGraph_externalLegs]; exact Multiset.map_le_map h
  edges_supported := by
    intro e' he'
    obtain ⟨e, he, rfl⟩ := Multiset.mem_map.mp he'
    simpa [ofFlatEdge, FeynmanEdge.SupportedOn] using γf.edges_supported e he
  legs_supported := by
    intro ℓ' hℓ'
    obtain ⟨ℓ, hℓ, rfl⟩ := Multiset.mem_map.mp hℓ'
    simpa [ofFlatLeg, ExternalLeg.SupportedOn] using γf.legs_supported ℓ hℓ

/-- Extensionality for flat subgraphs (carrier fields determine the subgraph). -/
private theorem feynmanSubgraph_ext {G : FeynmanGraph} {γ₁ γ₂ : FeynmanSubgraph G}
    (hv : γ₁.vertices = γ₂.vertices) (hi : γ₁.internalEdges = γ₂.internalEdges)
    (he : γ₁.externalLegs = γ₂.externalLegs) : γ₁ = γ₂ := by
  cases γ₁; cases γ₂; cases hv; cases hi; cases he; rfl

/-- The lift round-trips: forgetting recovers the original subgraph (same type,
no transport). -/
@[simp] theorem forget_liftFromForgetSubgraph
    (γf : FeynmanSubgraph (ofFlatGraph Gf).forget) :
    (liftFromForgetSubgraph γf).forget = γf := by
  refine feynmanSubgraph_ext rfl ?_ ?_
  · show (γf.internalEdges.map ofFlatEdge).map ResolvedFeynmanEdge.forget = γf.internalEdges
    rw [Multiset.map_map, forget_comp_ofFlatEdge, Multiset.map_id]
  · show (γf.externalLegs.map ofFlatLeg).map ResolvedExternalLeg.forget = γf.externalLegs
    rw [Multiset.map_map, forget_comp_ofFlatLeg, Multiset.map_id]

theorem liftFromForgetSubgraph_injective :
    Function.Injective (liftFromForgetSubgraph (Gf := Gf)) := by
  intro γ₁ γ₂ h
  have := congrArg (·.forget) h
  simpa [forget_liftFromForgetSubgraph] using this

/-- Extensionality for flat admissible subgraphs (determined by `forest.elements`). -/
private theorem admissibleSubgraph_ext {G : FeynmanGraph} [DivergenceMeasure G]
    {A₁ A₂ : AdmissibleSubgraph G} (h : A₁.elements = A₂.elements) : A₁ = A₂ := by
  obtain ⟨⟨e₁, d₁, nd₁⟩, cd₁⟩ := A₁
  obtain ⟨⟨e₂, d₂, nd₂⟩, cd₂⟩ := A₂
  cases h; rfl

/-- The lift of a pairwise-disjoint forest of `(ofFlatGraph Gf).forget` to a
resolved forest of `ofFlatGraph Gf` (transport-free: same forgetful ambient). -/
noncomputable def ofForgetForest (Af : AdmissibleSubgraph (ofFlatGraph Gf).forget)
    (hDisj : Af.IsPairwiseDisjoint) : ResolvedAdmissibleSubgraph (ofFlatGraph Gf) where
  elements := Af.elements.image liftFromForgetSubgraph
  isConnectedDivergent := by
    intro γ hγ
    obtain ⟨δf, hδf, rfl⟩ := Finset.mem_image.mp hγ
    rw [forget_liftFromForgetSubgraph]
    exact Af.isConnectedDivergent_of_mem hδf
  pairwiseDisjoint := by
    intro γ₁ h₁ γ₂ h₂ hne
    obtain ⟨δf₁, hδf₁, rfl⟩ := Finset.mem_image.mp h₁
    obtain ⟨δf₂, hδf₂, rfl⟩ := Finset.mem_image.mp h₂
    exact hDisj hδf₁ hδf₂ (fun h => hne (by rw [h]))

@[simp] theorem ofForgetForest_elements (Af : AdmissibleSubgraph (ofFlatGraph Gf).forget)
    (hDisj : Af.IsPairwiseDisjoint) :
    (ofForgetForest Af hDisj).elements = Af.elements.image liftFromForgetSubgraph := rfl

/-- The forest lift round-trips: forgetting recovers the original forest (same
forgetful ambient, no transport). -/
theorem forget_ofForgetForest (Af : AdmissibleSubgraph (ofFlatGraph Gf).forget)
    (hDisj : Af.IsPairwiseDisjoint) : (ofForgetForest Af hDisj).forget = Af := by
  apply admissibleSubgraph_ext
  rw [ResolvedAdmissibleSubgraph.forget_elements, ofForgetForest_elements,
    Finset.image_image,
    show (ResolvedFeynmanSubgraph.forget ∘ liftFromForgetSubgraph (Gf := Gf))
      = id from funext (fun γf => forget_liftFromForgetSubgraph γf),
    Finset.image_id]

/-- Aggregate internal edges of the forget-forest lift. -/
theorem ofForgetForest_internalEdges_eq (Af : AdmissibleSubgraph (ofFlatGraph Gf).forget)
    (hDisj : Af.IsPairwiseDisjoint) :
    (ofForgetForest Af hDisj).internalEdges = Af.internalEdges.map ofFlatEdge := by
  show (∑ γ ∈ (ofForgetForest Af hDisj).elements, γ.internalEdges) = Af.internalEdges.map ofFlatEdge
  rw [ofForgetForest_elements,
    Finset.sum_image (fun δ₁ _ δ₂ _ h => liftFromForgetSubgraph_injective h)]
  conv_rhs => rw [show Af.internalEdges = ∑ δ ∈ Af.elements, δ.internalEdges from rfl,
    map_ofFlatEdge_finset_sum]
  exact Finset.sum_congr rfl (fun δ _ => rfl)

/-- A flat proper forest of `(ofFlatGraph Gf).forget` lifts to a resolved proper
forest (transport-free; same forgetful ambient). -/
theorem ofForgetForest_isProperForest (Af : AdmissibleSubgraph (ofFlatGraph Gf).forget)
    (hAf : Af ∈ ((ofFlatGraph Gf).forget.properDisjointAdmissibleDivergentSubgraphs).filter
      (fun A => 0 < A.complementEdges.card))
    (hDisj : Af.IsPairwiseDisjoint) :
    (ofForgetForest Af hDisj).IsProperForest := by
  rw [Finset.mem_filter] at hAf
  obtain ⟨hpd, hcompl⟩ := hAf
  rw [FeynmanGraph.mem_properDisjointAdmissibleDivergentSubgraphs] at hpd
  obtain ⟨hnd, hhnc, hiec, hhpiec⟩ := hpd
  rw [FeynmanGraph.mem_nonemptyDisjointAdmissibleDivergentSubgraphs] at hnd
  obtain ⟨_, hne⟩ := hnd
  refine ⟨hne.image _, ?_, ?_, ?_, ?_⟩
  · intro γ hγ
    obtain ⟨δf, hδf, rfl⟩ := Finset.mem_image.mp hγ
    simpa [ResolvedFeynmanSubgraph.IsNonempty, ResolvedFeynmanSubgraph.vertexCount,
      FeynmanSubgraph.IsNonempty, FeynmanSubgraph.vertexCount] using hhnc δf hδf
  · rw [ofForgetForest_internalEdges_eq, Multiset.card_map]; exact hiec
  · intro γ hγ
    obtain ⟨δf, hδf, rfl⟩ := Finset.mem_image.mp hγ
    have := hhpiec δf hδf
    rwa [show (liftFromForgetSubgraph δf).internalEdges = δf.internalEdges.map ofFlatEdge from rfl,
      Multiset.card_map]
  · have hle' : Af.internalEdges ≤ Gf.internalEdges := by
      have hle := admissibleSubgraph_internalEdges_le_of_pairwise Af hDisj
      rwa [congrArg FeynmanGraph.internalEdges (forget_ofFlatGraph Gf)] at hle
    have hcard : (ofForgetForest Af hDisj).complementEdges.card = Af.complementEdges.card := by
      show ((ofFlatGraph Gf).internalEdges - (ofForgetForest Af hDisj).internalEdges).card
          = ((ofFlatGraph Gf).forget.internalEdges - Af.internalEdges).card
      rw [ofForgetForest_internalEdges_eq, ofFlatGraph_internalEdges,
        congrArg FeynmanGraph.internalEdges (forget_ofFlatGraph Gf),
        Multiset.card_sub (Multiset.map_le_map hle'), Multiset.card_sub hle',
        Multiset.card_map, Multiset.card_map]
    rw [hcard]; exact hcompl

end GaugeGeometry.QFT.Combinatorial
