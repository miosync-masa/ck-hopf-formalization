import GaugeGeometry.QFT.Combinatorial.FeynmanGraphs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Tactic

namespace GaugeGeometry.QFT.Combinatorial

namespace FeynmanGraph

/--
Minimal combinatorial 1-loop condition.

Version 1 uses the standard connected 1-loop counting pattern
as a structural predicate:
- the number of internal edges equals the number of vertices,
- and the graph is nonempty.
-/
def IsOneLoop (G : FeynmanGraph) : Prop :=
  G.internalEdgeCount = G.vertexCount ∧ 0 < G.vertexCount

@[simp] theorem isOneLoop_def (G : FeynmanGraph) :
    G.IsOneLoop = (G.internalEdgeCount = G.vertexCount ∧ 0 < G.vertexCount) := by
  rfl

/--
A graph with no external legs.
-/
def IsVacuumLike (G : FeynmanGraph) : Prop :=
  G.externalLegCount = 0

@[simp] theorem isVacuumLike_def (G : FeynmanGraph) :
    G.IsVacuumLike = (G.externalLegCount = 0) := by
  rfl

@[simp] theorem emptyGraph_not_isOneLoop :
    ¬ emptyGraph.IsOneLoop := by
  simp [FeynmanGraph.IsOneLoop]

@[simp] theorem emptyGraph_isVacuumLike :
    emptyGraph.IsVacuumLike := by
  simp [FeynmanGraph.IsVacuumLike]

end FeynmanGraph

/--
A canonical self-loop internal edge based at vertex `0`.
This serves as the simplest combinatorial 1-loop example.
-/
def tadpoleEdge : FeynmanEdge where
  source := 0
  target := 0
  sector := GaugeGeometry.Core.GaugeSector.hypercharge

@[simp] theorem tadpoleEdge_source :
    tadpoleEdge.source = 0 := by
  rfl

@[simp] theorem tadpoleEdge_target :
    tadpoleEdge.target = 0 := by
  rfl

@[simp] theorem tadpoleEdge_isSelfLoop :
    tadpoleEdge.IsSelfLoop := by
  simp [FeynmanEdge.IsSelfLoop, tadpoleEdge]

/--
The simplest one-loop graph:
one vertex and one self-loop internal edge, with no external legs.
-/
def oneLoopTadpole : FeynmanGraph where
  vertices := ({0} : Finset VertexId)
  internalEdges := ({tadpoleEdge} : Multiset FeynmanEdge)
  externalLegs := 0

@[simp] theorem oneLoopTadpole_vertices :
    oneLoopTadpole.vertices = ({0} : Finset VertexId) := by
  rfl

@[simp] theorem oneLoopTadpole_internalEdges :
    oneLoopTadpole.internalEdges = ({tadpoleEdge} : Multiset FeynmanEdge) := by
  rfl

@[simp] theorem oneLoopTadpole_externalLegs :
    oneLoopTadpole.externalLegs = 0 := by
  rfl

@[simp] theorem oneLoopTadpole_vertexCount :
    oneLoopTadpole.vertexCount = 1 := by
  simp [oneLoopTadpole, FeynmanGraph.vertexCount]

@[simp] theorem oneLoopTadpole_internalEdgeCount :
    oneLoopTadpole.internalEdgeCount = 1 := by
  simp [oneLoopTadpole, FeynmanGraph.internalEdgeCount]

@[simp] theorem oneLoopTadpole_externalLegCount :
    oneLoopTadpole.externalLegCount = 0 := by
  simp [oneLoopTadpole, FeynmanGraph.externalLegCount]

theorem tadpoleEdge_supported_on_singleton :
    tadpoleEdge.SupportedOn ({0} : Finset VertexId) := by
  simp [FeynmanEdge.SupportedOn, tadpoleEdge]

theorem oneLoopTadpole_wellFormed :
    oneLoopTadpole.WellFormed := by
  constructor
  · intro e he
    have he' : e = tadpoleEdge := by
      simpa using he
    subst he'
    exact tadpoleEdge_supported_on_singleton
  · intro ℓ hℓ
    simp at hℓ

theorem oneLoopTadpole_isOneLoop :
    oneLoopTadpole.IsOneLoop := by
  simp [FeynmanGraph.IsOneLoop]

theorem oneLoopTadpole_isVacuumLike :
    oneLoopTadpole.IsVacuumLike := by
  simp [FeynmanGraph.IsVacuumLike]

/--
The one-loop tadpole is connected: its sole vertex is trivially reachable
from itself.
-/
theorem oneLoopTadpole_isConnected :
    oneLoopTadpole.IsConnected := by
  intro u v hu hv
  have hu' : u = 0 := by
    have : u ∈ ({0} : Finset VertexId) := by
      simpa [oneLoopTadpole] using hu
    simpa using this
  have hv' : v = 0 := by
    have : v ∈ ({0} : Finset VertexId) := by
      simpa [oneLoopTadpole] using hv
    simpa using this
  subst hu'
  subst hv'
  exact FeynmanGraph.Reachable.refl _ 0

/--
The Euler loop number of the one-loop tadpole equals `1`.
-/
theorem oneLoopTadpole_loopNumber :
    oneLoopTadpole.loopNumber = 1 := by
  simp [FeynmanGraph.loopNumber]

/--
The one-loop tadpole satisfies the strong one-loop predicate.
-/
theorem oneLoopTadpole_isOneLoopStrong :
    oneLoopTadpole.IsOneLoopStrong := by
  refine ⟨oneLoopTadpole_isConnected, ?_, oneLoopTadpole_loopNumber⟩
  simp [oneLoopTadpole, FeynmanGraph.vertexCount]

/--
Strong one-loop implies weak one-loop.
`IsOneLoopStrong` carries `loopNumber = 1`, i.e. `E - V + 1 = 1`, so `E = V`,
and the strong predicate already supplies `0 < V`, which the weak predicate
needs to rule out the empty graph.
-/
theorem FeynmanGraph.IsOneLoopStrong.toIsOneLoop
    {G : FeynmanGraph} (hStrong : G.IsOneLoopStrong) :
    G.IsOneLoop := by
  obtain ⟨_, hV, hL⟩ := hStrong
  refine ⟨?_, hV⟩
  have : (G.internalEdgeCount : Int) - (G.vertexCount : Int) + 1 = 1 := by
    simpa [FeynmanGraph.loopNumber] using hL
  have hEV : (G.internalEdgeCount : Int) = (G.vertexCount : Int) := by
    linarith
  exact_mod_cast hEV

end GaugeGeometry.QFT.Combinatorial
