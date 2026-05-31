import GaugeGeometry.QFT.HopfAlgebra.RecursionMeasure
import GaugeGeometry.QFT.Combinatorial.GraphIsomorphism
import GaugeGeometry.QFT.Combinatorial.Permutation

/-!
# Quotient lift: connected-graph predicate at the isomorphism-class level

Sprint B' lifts `IsSupportConnected` from `FeynmanGraph` to
`FeynmanGraphClass` (= `Quotient FeynmanGraph.isoSetoid`). The
permutation-invariance of `IsSupportConnected` is supplied by Sprint A
(`Permutation.lean:321`, `mapPerm_isSupportConnected_iff`), so the
`Quotient.lift` is mechanical.

This is the H1.WF.5 + H2.5 (`IsSupportConnected` portion only)
fragment of the design note. The stronger predicate
`IsConnectedDivergent` is class-lifted in Sprint C alongside the
`HopfH` strict artifact (Plan-D Hybrid).

## Tag map (HOPF_DECOMPOSITION.md)

* `[Algebra]` `FeynmanGraphClass.IsSupportConnected` — class-level predicate (well-defined via `IsIso` invariance)
* `[Algebra]` `ConnectedFeynmanGraphClass` — H1.WF.5 carrier
-/

namespace GaugeGeometry.QFT.Combinatorial

/-! ### Class-level `IsSupportConnected` predicate -/

namespace FeynmanGraphClass

/--
**H2.5 fragment** — `IsSupportConnected` lifts to `FeynmanGraphClass`
because it is invariant under vertex permutations (Sprint A's
`mapPerm_isSupportConnected_iff`).
-/
def IsSupportConnected : FeynmanGraphClass → Prop :=
  Quotient.lift FeynmanGraph.IsSupportConnected
    (fun G₁ G₂ ⟨π, hπ⟩ => by
      -- `hπ : G₂ = G₁.mapPerm π`. We want `G₁.IsSupportConnected ↔ G₂.IsSupportConnected`.
      subst hπ
      exact propext (FeynmanGraph.mapPerm_isSupportConnected_iff π G₁).symm)

@[simp] theorem isSupportConnected_toClass (G : FeynmanGraph) :
    IsSupportConnected G.toClass ↔ G.IsSupportConnected := Iff.rfl

end FeynmanGraphClass

/-! ### `ConnectedFeynmanGraphClass` (H1.WF.5)

The subtype of `FeynmanGraphClass` carrying a witness of
class-level support-connectedness. This is the natural target for
lifting `coproductGen`/`antipodeGen` from `ConnectedFeynmanGraph` to
isomorphism classes.

Since this is a subtype of a `Quotient`, no fresh `Setoid` is needed:
the equivalence is inherited from `FeynmanGraph.isoSetoid` via the
underlying class.
-/

/--
**H1.WF.5** — Subtype of `FeynmanGraphClass` carrying the
class-level connectedness witness.
-/
def ConnectedFeynmanGraphClass : Type :=
  { c : FeynmanGraphClass // c.IsSupportConnected }

namespace ConnectedFeynmanGraphClass

/-- Build a `ConnectedFeynmanGraphClass` from a `ConnectedFeynmanGraph`. -/
def ofConnected (G : ConnectedFeynmanGraph) : ConnectedFeynmanGraphClass :=
  ⟨G.toFeynmanGraph.toClass,
    -- The class-level predicate evaluates to the underlying-graph
    -- predicate via `isSupportConnected_toClass`.
    (FeynmanGraphClass.isSupportConnected_toClass _).mpr G.isSupportConnected⟩

@[simp] theorem ofConnected_val (G : ConnectedFeynmanGraph) :
    (ofConnected G).val = G.toFeynmanGraph.toClass := rfl

/-! #### Recursion measure at the class level (H1.WF.5)

`FeynmanGraphClass.internalEdgeCount` is already `IsIso`-invariant
(Sprint A `GraphIsomorphism.lean`), so pulling the Sprint B' Nat
measure `edgeMeasure` up to the class carrier is immediate.

The recursion in H4.3 / H6.1 will ultimately invoke
`edgeRecursion` at the class level once the class-level `contract`
(H2.2) is composed with the subtype carrier.
-/

/-- Class-level recursion measure: underlying graph's `internalEdgeCount`,
passed through the subtype. -/
@[reducible] def edgeMeasure (G : ConnectedFeynmanGraphClass) : Nat :=
  G.val.internalEdgeCount

@[simp] theorem edgeMeasure_ofConnected (G : ConnectedFeynmanGraph) :
    (ofConnected G).edgeMeasure = G.toFeynmanGraph.internalEdgeCount := rfl

/-- **H1.WF.5** — Well-founded relation on `ConnectedFeynmanGraphClass`
via `edgeMeasure : Nat`. Exactly mirrors the subtype-level
`graphEdgeWFRel` from `RecursionMeasure.lean`. -/
@[reducible] def graphEdgeWFRel :
    WellFoundedRelation ConnectedFeynmanGraphClass :=
  invImage edgeMeasure Nat.lt_wfRel

instance : WellFoundedRelation ConnectedFeynmanGraphClass := graphEdgeWFRel

end ConnectedFeynmanGraphClass

end GaugeGeometry.QFT.Combinatorial
