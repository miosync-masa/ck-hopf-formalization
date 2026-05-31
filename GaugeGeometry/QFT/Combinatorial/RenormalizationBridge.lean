import GaugeGeometry.QFT.Combinatorial.WickExpansion
import GaugeGeometry.QFT.Combinatorial.OneLoopGraphs
import GaugeGeometry.QFT.Representation.GaugeProduct
import GaugeGeometry.QFT.Representation.CasimirData
import GaugeGeometry.QFT.Representation.DynkinIndex
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Rat.Defs

namespace GaugeGeometry.QFT.Combinatorial

/--
A minimal counterterm placeholder attached to a combinatorial Feynman graph.

Version 1 does not yet encode subtraction schemes or Hopf-algebra structure.
It only records:
- the underlying graph,
- a loop order label,
- whether a counterterm is present.
-/
structure CountertermData where
  graph : FeynmanGraph
  loopOrder : Nat
  hasCounterterm : Bool

namespace CountertermData

/--
A counterterm datum is one-loop if its loop-order label is `1`.
-/
def IsOneLoop (C : CountertermData) : Prop :=
  C.loopOrder = 1

@[simp] theorem isOneLoop_def (C : CountertermData) :
    C.IsOneLoop = (C.loopOrder = 1) := by
  rfl

/--
A trivial counterterm datum with no counterterm inserted.
-/
def trivial (G : FeynmanGraph) : CountertermData where
  graph := G
  loopOrder := 0
  hasCounterterm := false

@[simp] theorem trivial_graph (G : FeynmanGraph) :
    (trivial G).graph = G := by
  rfl

@[simp] theorem trivial_loopOrder (G : FeynmanGraph) :
    (trivial G).loopOrder = 0 := by
  rfl

@[simp] theorem trivial_hasCounterterm (G : FeynmanGraph) :
    (trivial G).hasCounterterm = false := by
  rfl

@[simp] theorem trivial_not_oneLoop (G : FeynmanGraph) :
    ¬ (trivial G).IsOneLoop := by
  simp [CountertermData.IsOneLoop]

@[simp] theorem CountertermData_eta (C : CountertermData) :
    CountertermData.mk C.graph C.loopOrder C.hasCounterterm = C := by
  cases C
  rfl

end CountertermData

namespace WickExpansionTerm

/--
A Wick expansion term is renormalization-ready if it is well formed.

Version 1 keeps this intentionally minimal: the bridge starts from a
well-formed combinatorial object before adding subtraction data.
-/
def IsRenormalizationReady (T : WickExpansionTerm) : Prop :=
  T.WellFormed

@[simp] theorem isRenormalizationReady_def (T : WickExpansionTerm) :
    T.IsRenormalizationReady = T.WellFormed := by
  rfl

/--
A Wick expansion term is one-loop renormalization-ready if
its graph is well formed, one-loop, and the contraction is complete.
-/
def IsOneLoopRenormalizationReady (T : WickExpansionTerm) : Prop :=
  T.WellFormed ∧ T.graph.IsOneLoop

@[simp] theorem isOneLoopRenormalizationReady_def (T : WickExpansionTerm) :
    T.IsOneLoopRenormalizationReady = (T.WellFormed ∧ T.graph.IsOneLoop) := by
  rfl

theorem emptyVacuumTerm_isRenormalizationReady :
    emptyVacuumTerm.IsRenormalizationReady := by
  exact emptyVacuumTerm_wellFormed

theorem oneLoopTadpoleVacuumTerm_isRenormalizationReady :
    oneLoopTadpoleVacuumTerm.IsRenormalizationReady := by
  exact oneLoopTadpoleVacuumTerm_wellFormed

theorem oneLoopTadpoleVacuumTerm_isOneLoopRenormalizationReady :
    oneLoopTadpoleVacuumTerm.IsOneLoopRenormalizationReady := by
  constructor
  · exact oneLoopTadpoleVacuumTerm_wellFormed
  · exact oneLoopTadpole_isOneLoop

end WickExpansionTerm

/--
Attach minimal counterterm data to a Wick expansion term.

This is the first bridge from Wick expansion objects to renormalization data.
-/
def attachCountertermData
    (T : WickExpansionTerm) (loopOrder : Nat) (hasCounterterm : Bool) :
    CountertermData where
  graph := T.graph
  loopOrder := loopOrder
  hasCounterterm := hasCounterterm

@[simp] theorem attachCountertermData_graph
    (T : WickExpansionTerm) (loopOrder : Nat) (hasCounterterm : Bool) :
    (attachCountertermData T loopOrder hasCounterterm).graph = T.graph := by
  rfl

@[simp] theorem attachCountertermData_loopOrder
    (T : WickExpansionTerm) (loopOrder : Nat) (hasCounterterm : Bool) :
    (attachCountertermData T loopOrder hasCounterterm).loopOrder = loopOrder := by
  rfl

@[simp] theorem attachCountertermData_hasCounterterm
    (T : WickExpansionTerm) (loopOrder : Nat) (hasCounterterm : Bool) :
    (attachCountertermData T loopOrder hasCounterterm).hasCounterterm = hasCounterterm := by
  rfl

/--
Canonical one-loop counterterm datum built from a one-loop Wick expansion term.
-/
def oneLoopCountertermData (T : WickExpansionTerm) : CountertermData :=
  attachCountertermData T 1 true

@[simp] theorem oneLoopCountertermData_isOneLoop
    (T : WickExpansionTerm) :
    (oneLoopCountertermData T).IsOneLoop := by
  simp [oneLoopCountertermData, CountertermData.IsOneLoop]

@[simp] theorem oneLoopCountertermData_hasCounterterm
    (T : WickExpansionTerm) :
    (oneLoopCountertermData T).hasCounterterm = true := by
  rfl

/--
If a Wick expansion term is one-loop renormalization-ready, then the canonical
attached counterterm datum is one-loop.
-/
theorem oneLoop_ready_implies_counterterm_oneLoop
    (T : WickExpansionTerm)
    (_hT : T.IsOneLoopRenormalizationReady) :
    (oneLoopCountertermData T).IsOneLoop := by
  simp [oneLoopCountertermData, CountertermData.IsOneLoop]

/--
The canonical one-loop tadpole vacuum term produces a one-loop counterterm datum.
-/
theorem oneLoopTadpole_counterterm_isOneLoop :
    (oneLoopCountertermData oneLoopTadpoleVacuumTerm).IsOneLoop := by
  simp [oneLoopCountertermData, CountertermData.IsOneLoop]

/--
The canonical one-loop tadpole vacuum term produces a counterterm datum
whose underlying graph is the one-loop tadpole.
-/
theorem oneLoopTadpole_counterterm_graph :
    (oneLoopCountertermData oneLoopTadpoleVacuumTerm).graph = oneLoopTadpole := by
  simp [oneLoopCountertermData, attachCountertermData]

/-!
### Combinatorial → Representation bridge (2-B)

This section provides the *type-level* bridge from sector-indexed combinatorial
statistics of a `FeynmanGraph` (edge/leg counts by `GaugeSector`) to the
rational quantities supplied by the representation layer
(`CasimirData`, `DynkinIndexData`, `BetaCoefficients`).

The goal here is to fix the **interface shape**, not the concrete values.
Concrete instances — e.g. the MSSM one — are expected to be supplied later,
either in `Representation/BetaCoefficients.lean` as Stage 2/3 assembly, or,
where strictly unavoidable, as external declarations in `Axioms/`.

Design notes:
* We index everything through `GaugeSector` (from `Core.Sector`), not `GaugeIndex`,
  since the combinatorial side only carries `GaugeSector` labels on edges/legs.
  The two are interconvertible via `indexOfSector` / `sectorOfIndex` in
  `Representation.GaugeProduct`.
* Nothing here commits to boson/fermion separation or vertex coupling weights:
  those are absorbed into the `ℚ`-valued coefficients of the representation-
  layer data structures.
-/

open Representation

/--
Rational statistic supplied by a `FeynmanGraph` to the representation layer:
given a `FeynmanGraph`, return a `ℚ`-valued function of `GaugeSector`.

The three canonical use cases are:
* `(G.internalEdgeCountBy s : ℚ)` — internal-edge count per sector,
* `(G.externalLegCountBy s : ℚ)` — external-leg count per sector,
* any `ℚ`-linear combination of the above, possibly weighted by
  representation-layer data such as `CasimirData`.
-/
abbrev SectorStatistic :=
  FeynmanGraph → GaugeGeometry.Core.GaugeSector → ℚ

/--
Canonical combinatorial statistic: internal-edge count per sector, cast to `ℚ`.
-/
def internalEdgeStatistic : SectorStatistic :=
  fun G s => (G.internalEdgeCountBy s : ℚ)

/--
Canonical combinatorial statistic: external-leg count per sector, cast to `ℚ`.
-/
def externalLegStatistic : SectorStatistic :=
  fun G s => (G.externalLegCountBy s : ℚ)

/--
A `CombinatorialBridge` fixes how combinatorial, sector-indexed data from a
`FeynmanGraph` is combined with representation-layer data
(`CasimirData`, `DynkinIndexData`) to yield a `GaugeIndex`-indexed rational
contribution.

This is a *type-level* bridge: concrete bridges (the MSSM one-loop bridge,
threshold-style bridges, etc.) are provided as `instance`s later. The Version 1
goal of this structure is to give the combinatorial and representation layers
a shared interface point without committing to specific coefficient choices.
-/
structure CombinatorialBridge where
  /-- Raw combinatorial statistic extracted from a graph. -/
  statistic : SectorStatistic
  /--
  Representation-theoretic weight per gauge index: e.g. the Casimir or
  Dynkin-index contribution that multiplies `statistic`.
  -/
  repWeight : GaugeIndex → ℚ

namespace CombinatorialBridge

/--
The contribution of a bridge to a single gauge index on a graph:
`repWeight i * statistic G (sectorOfIndex i)`.
-/
def contributionAt (B : CombinatorialBridge) (G : FeynmanGraph)
    (i : GaugeIndex) : ℚ :=
  B.repWeight i * B.statistic G (sectorOfIndex i)

/--
Contribution per gauge index, as a `BetaCoefficients`-shaped function
(`GaugeIndex → ℚ`), for a fixed graph `G`.
-/
def contribution (B : CombinatorialBridge) (G : FeynmanGraph) :
    GaugeIndex → ℚ :=
  fun i => B.contributionAt G i

@[simp] theorem contribution_apply (B : CombinatorialBridge) (G : FeynmanGraph)
    (i : GaugeIndex) :
    B.contribution G i = B.repWeight i * B.statistic G (sectorOfIndex i) := by
  rfl

/--
Bridge whose rep-weight is the `AdjointCasimirData`-derived rational at each
gauge index. Combined with `internalEdgeStatistic`, this will later carry the
gauge-boson self-energy contribution to `b_i`.
-/
def ofAdjointCasimir (c : AdjointCasimirData) (stat : SectorStatistic) :
    CombinatorialBridge where
  statistic := stat
  repWeight := c.atIndex

/--
Bridge whose rep-weight is the `MatterCasimirData`-derived rational at each
gauge index. Combined with `internalEdgeStatistic`, this will later carry the
matter-loop contribution to `b_i`.
-/
def ofMatterCasimir (c : MatterCasimirData) (stat : SectorStatistic) :
    CombinatorialBridge where
  statistic := stat
  repWeight := c.atIndex

/--
Bridge whose rep-weight is the `DynkinIndexData`-derived rational at each
gauge index. This is the shape used for Dynkin-index–based assembly of `b_i`.
-/
def ofDynkinIndex (d : DynkinIndexData) (stat : SectorStatistic) :
    CombinatorialBridge where
  statistic := stat
  repWeight := d.atIndex

end CombinatorialBridge

end GaugeGeometry.QFT.Combinatorial
