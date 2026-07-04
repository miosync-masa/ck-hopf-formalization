import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestBlockMapCombiner

/-!
# R-6c-body-102 — codomain forest-image classifier: `isForestImage` fixed to the star-touch predicate

Hundred-and-second genuine-body step, pinning down body-101's arbitrary `isForestImage` to a CONCRETE
predicate: a quotient forest `B` is a forest-image iff some component of `B` touches the outer forest's star
carrier.  This is the resolved port of the flat discriminator `forestQuotientForestSigma_isForestByStar`
(`Coassoc` 14810).  With the codomain classification fixed, every `maps_to` becomes a concrete "this `B` is in
the mixed / forest class" claim.

## The classifier (resolved port of flat `isForestByStar`)

`resolvedIsForestImage A B := ∃ δ ∈ B.elements, ¬ Disjoint δ.vertices (A.starVertices (starOf G A))`.  A
quotient forest `B` (of the graph `A.contractWithStars`) is a forest-image exactly when one of its components
`δ` touches a star vertex of `A` (a vertex where an `A`-component was contracted).  Geometrically:

* FOREST-carrying images DO touch a star — a promoted sub-forest lives against the contraction locus (flat
  `forestQuotientForestSigma_isForestByStar_of_forest`, 14823);
* MIXED-boundary images do NOT — the right-selected whole components sit in the ambient complement `G.vertices \
  A.vertices`, away from the stars (flat `forestQuotientForestSigma_not_isForestByStar_of_mixed`, 14838).

`A.starVertices (starOf G A)` is the resolved star carrier (`mem_starVertices : v ∈ A.starVertices starOf ↔ ∃
γ ∈ A.elements, starOf γ = v`); `(A.contractWithStars starOf).vertices = (G.vertices \ A.vertices) ∪
A.starVertices starOf` — so a component either meets the stars (forest) or lives in the complement (mixed).

## Fixing the hitbox

`ResolvedForestBlockConcreteMapData` is body-101's combined map data with `isForestImage` REMOVED — baked in as
`resolvedIsForestImage` throughout the codomain carriers (`mixedCodFinset` / `forestCarryingCodFinset` now filter
by the concrete star-touch predicate).  `.toForestBlockMapData` supplies `isForestImage := resolvedIsForestImage`
to recover body-101's data; `.coassoc_gen` chains body-101/98/…/88.  The two direction lemmas (forest images
touch a star, mixed don't) are NOT proved here — they need the maps, so they surface as `maps_to` obligations on
the concrete predicate (the resolved analogues of flat `_of_forest` / `_not…_of_mixed`).

Per the HALT: the predicate is chosen (concrete star-touch, flat `isForestByStar`) and connected to body-101;
no map laws are proved; the classifier's direction lemmas remain as the maps' concrete `maps_to`; no star
allocation detail.

Landed:

* `resolvedIsForestImage` — the concrete codomain classifier (star-touch);
* `ResolvedForestBlockConcreteMapData D` — body-101's map data with `isForestImage` fixed;
* `.toForestBlockMapData` / `.coassoc_gen` — to body-101/98/96/95/94/93/92/91/90/88.

No facade, no flat term, no `forgetHopf`.
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
set_option linter.unusedVariables false

/-- **R-6c-body-102 — the concrete forest-image classifier** (resolved port of flat `isForestByStar`).  A
quotient forest `B` is a forest-image iff some component `δ` of `B` touches the star carrier of `A`. -/
def resolvedIsForestImage {G : ResolvedFeynmanGraph}
    (A : {A : ResolvedAdmissibleSubgraph G // A ∈ D.carrier G})
    (B : (D.supply (A.1.contractWithStars (D.starOf G A.1))).ForestIdx) : Prop :=
  ∃ δ ∈ B.1.elements, ¬ Disjoint δ.vertices (A.1.starVertices (D.starOf G A.1))

/-- **R-6c-body-102 — the concrete-classifier map data.**  Body-101's combined map data with `isForestImage`
fixed to `resolvedIsForestImage` (the codomain carriers filter by the concrete star-touch predicate). -/
structure ResolvedForestBlockConcreteMapData (D : ResolvedCoproductProperForestData) where
  -- MIXED map
  /-- The mixed-boundary map `(A', p) ↦ (A, B)`. -/
  mixedToFun : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G),
    q ∈ mixedDomFinset G → ForestBlockCodType D G
  /-- The mixed inverse. -/
  mixedInvFun : ∀ (G : ResolvedFeynmanGraph) (r : ForestBlockCodType D G),
    r ∈ mixedCodFinset (D := D) (fun {G} A B => resolvedIsForestImage A B) G → ForestBlockDomType D G
  /-- `mixedToFun` lands in the mixed codomain. -/
  mixedToFun_mem : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G) (hq : q ∈ mixedDomFinset G),
    mixedToFun G q hq ∈ mixedCodFinset (D := D) (fun {G} A B => resolvedIsForestImage A B) G
  /-- `mixedInvFun` lands in the mixed domain. -/
  mixedInvFun_mem : ∀ (G : ResolvedFeynmanGraph) (r : ForestBlockCodType D G)
    (hr : r ∈ mixedCodFinset (D := D) (fun {G} A B => resolvedIsForestImage A B) G),
    mixedInvFun G r hr ∈ mixedDomFinset G
  /-- `mixedInvFun ∘ mixedToFun = id`. -/
  mixedLeft_inv : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G) (hq : q ∈ mixedDomFinset G),
    mixedInvFun G (mixedToFun G q hq) (mixedToFun_mem G q hq) = q
  /-- `mixedToFun ∘ mixedInvFun = id`. -/
  mixedRight_inv : ∀ (G : ResolvedFeynmanGraph) (r : ForestBlockCodType D G)
    (hr : r ∈ mixedCodFinset (D := D) (fun {G} A B => resolvedIsForestImage A B) G),
    mixedToFun G (mixedInvFun G r hr) (mixedInvFun_mem G r hr) = r
  /-- Mixed geometric identity: left-factor product = target outer's left term. -/
  mixed_left_eq : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G) (hq : q ∈ mixedDomFinset G),
    (∏ γ ∈ (q.1.1.elements.attach).attach,
        localLeftFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2))
      = (D.supply G).leftTerm (mixedToFun G q hq).1
  /-- Mixed geometric identity: right-factor product = quotient forest's left term. -/
  mixed_right_eq : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G) (hq : q ∈ mixedDomFinset G),
    (∏ γ ∈ (q.1.1.elements.attach).attach,
        localRightFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2))
      = (D.supply ((mixedToFun G q hq).1.1.contractWithStars (D.starOf G (mixedToFun G q hq).1.1))).leftTerm
          (mixedToFun G q hq).2
  /-- Mixed geometric identity: source quotient right term = quotient forest's right term. -/
  mixed_quot_eq : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G) (hq : q ∈ mixedDomFinset G),
    (D.supply G).rightTerm q.1
      = (D.supply ((mixedToFun G q hq).1.1.contractWithStars (D.starOf G (mixedToFun G q hq).1.1))).rightTerm
          (mixedToFun G q hq).2
  -- FOREST map
  /-- The forest-carrying map `(A', p) ↦ (A, B)`. -/
  forestToFun : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G),
    q ∈ forestCarryingDomFinset G → ForestBlockCodType D G
  /-- The forest inverse. -/
  forestInvFun : ∀ (G : ResolvedFeynmanGraph) (r : ForestBlockCodType D G),
    r ∈ forestCarryingCodFinset (D := D) (fun {G} A B => resolvedIsForestImage A B) G → ForestBlockDomType D G
  /-- `forestToFun` lands in the forest-image codomain. -/
  forestToFun_mem : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G)
    (hq : q ∈ forestCarryingDomFinset G),
    forestToFun G q hq ∈ forestCarryingCodFinset (D := D) (fun {G} A B => resolvedIsForestImage A B) G
  /-- `forestInvFun` lands in the forest-carrying domain. -/
  forestInvFun_mem : ∀ (G : ResolvedFeynmanGraph) (r : ForestBlockCodType D G)
    (hr : r ∈ forestCarryingCodFinset (D := D) (fun {G} A B => resolvedIsForestImage A B) G),
    forestInvFun G r hr ∈ forestCarryingDomFinset G
  /-- `forestInvFun ∘ forestToFun = id`. -/
  forestLeft_inv : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G)
    (hq : q ∈ forestCarryingDomFinset G),
    forestInvFun G (forestToFun G q hq) (forestToFun_mem G q hq) = q
  /-- `forestToFun ∘ forestInvFun = id`. -/
  forestRight_inv : ∀ (G : ResolvedFeynmanGraph) (r : ForestBlockCodType D G)
    (hr : r ∈ forestCarryingCodFinset (D := D) (fun {G} A B => resolvedIsForestImage A B) G),
    forestToFun G (forestInvFun G r hr) (forestInvFun_mem G r hr) = r
  /-- Forest geometric identity: left-factor product = target outer's left term. -/
  forest_left_eq : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G)
    (hq : q ∈ forestCarryingDomFinset G),
    (∏ γ ∈ (q.1.1.elements.attach).attach,
        localLeftFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2))
      = (D.supply G).leftTerm (forestToFun G q hq).1
  /-- Forest geometric identity: right-factor product = quotient forest's left term. -/
  forest_right_eq : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G)
    (hq : q ∈ forestCarryingDomFinset G),
    (∏ γ ∈ (q.1.1.elements.attach).attach,
        localRightFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2))
      = (D.supply ((forestToFun G q hq).1.1.contractWithStars (D.starOf G (forestToFun G q hq).1.1))).leftTerm
          (forestToFun G q hq).2
  /-- Forest geometric identity: source quotient right term = quotient forest's right term. -/
  forest_quotient_eq : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G)
    (hq : q ∈ forestCarryingDomFinset G),
    (D.supply G).rightTerm q.1
      = (D.supply ((forestToFun G q hq).1.1.contractWithStars (D.starOf G (forestToFun G q hq).1.1))).rightTerm
          (forestToFun G q hq).2
  -- shared
  /-- Every carrier forest is a proper forest (body-96; gives `outer_nonempty`). -/
  carrier_isProperForest : ∀ (G : ResolvedFeynmanGraph) (A : ResolvedAdmissibleSubgraph G),
    A ∈ D.carrier G → A.IsProperForest
  /-- A representative graph for each generator. -/
  rep : ResolvedHopfGen → ResolvedFeynmanGraph
  /-- The representative is connected-divergent. -/
  repCD : ∀ x : ResolvedHopfGen, (rep x).forget.toClass.IsConnectedDivergent
  /-- The representative's generator IS `x`. -/
  rep_gen : ∀ x : ResolvedHopfGen, x = (rep x).toResolvedHopfGen (repCD x)

/-- **R-6c-body-102 — body-101's map data from the concrete classifier** (`isForestImage :=
resolvedIsForestImage`). -/
def ResolvedForestBlockConcreteMapData.toForestBlockMapData
    (S : ResolvedForestBlockConcreteMapData D) : ResolvedForestBlockMapData D where
  isForestImage := fun {G} A B => resolvedIsForestImage A B
  mixedToFun := S.mixedToFun
  mixedInvFun := S.mixedInvFun
  mixedToFun_mem := S.mixedToFun_mem
  mixedInvFun_mem := S.mixedInvFun_mem
  mixedLeft_inv := S.mixedLeft_inv
  mixedRight_inv := S.mixedRight_inv
  mixed_left_eq := S.mixed_left_eq
  mixed_right_eq := S.mixed_right_eq
  mixed_quot_eq := S.mixed_quot_eq
  forestToFun := S.forestToFun
  forestInvFun := S.forestInvFun
  forestToFun_mem := S.forestToFun_mem
  forestInvFun_mem := S.forestInvFun_mem
  forestLeft_inv := S.forestLeft_inv
  forestRight_inv := S.forestRight_inv
  forest_left_eq := S.forest_left_eq
  forest_right_eq := S.forest_right_eq
  forest_quotient_eq := S.forest_quotient_eq
  carrier_isProperForest := S.carrier_isProperForest
  rep := S.rep
  repCD := S.repCD
  rep_gen := S.rep_gen

/-- **R-6c-body-102 — `coassoc_gen` from the concrete classifier** (via body-101/98/…/88). -/
theorem ResolvedForestBlockConcreteMapData.coassoc_gen
    (S : ResolvedForestBlockConcreteMapData D) (x : ResolvedHopfGen) :
    D.coassocLeft (MvPolynomial.X x) = D.coassocRight (MvPolynomial.X x) :=
  S.toForestBlockMapData.coassoc_gen x

end GaugeGeometry.QFT.Combinatorial
