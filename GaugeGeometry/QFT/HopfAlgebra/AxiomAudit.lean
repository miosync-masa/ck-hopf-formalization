import GaugeGeometry.QFT.HopfAlgebra.StrictGenerators
import GaugeGeometry.QFT.HopfAlgebra.Coproduct
import GaugeGeometry.QFT.HopfAlgebra.ContractionPreservation
import GaugeGeometry.QFT.HopfAlgebra.Antipode
import GaugeGeometry.QFT.HopfAlgebra.HopfAlgebra

/-!
# Axiom audit for Sprint C1 (H3.6–3.9)

The #print axioms commands below are the source-of-truth for what
the Sprint C1 artifacts actually depend on. Expected footprint:
`[propext, Classical.choice, Quot.sound]` only.
-/

namespace GaugeGeometry.QFT.Combinatorial

#print axioms FeynmanSubgraph.IsIso.isConnectedDivergent_iff
#print axioms FeynmanSubgraphClass.IsConnectedDivergent
#print axioms FeynmanGraph.mapPerm_isConnectedDivergent_iff
#print axioms FeynmanGraphClass.IsConnectedDivergent
#print axioms HopfGen
#print axioms HopfH
#print axioms bridge

-- Sprint C2 Phase A artifacts
#print axioms FeynmanSubgraph.isNonempty_of_internalEdges_pos
#print axioms FeynmanGraph.properConnectedDivergentSubgraphs
#print axioms FeynmanSubgraph.toHopfGenTemp
#print axioms FeynmanSubgraph.contractToHopfGenTemp
#print axioms coproductGen
#print axioms coproductGen_eq

-- Sprint C2 Phase B artifacts
#print axioms FeynmanSubgraph.mapPerm_isConnected
#print axioms FeynmanSubgraph.mapPerm_isOnePI
#print axioms FeynmanSubgraph.mapPerm_isConnectedDivergent
#print axioms FeynmanSubgraph.mapPerm_isConnectedDivergent_reverse
#print axioms coproductGen_isomorphism_invariant

-- Sprint C2 Phase C artifacts
#print axioms coproductGenClass
#print axioms coproduct
#print axioms coproduct_X
#print axioms coproduct_one
#print axioms coproduct_mul

-- Sprint D prep: contract preservation lemmas
#print axioms FeynmanSubgraph.asSubOfErase
#print axioms FeynmanSubgraph.contract_eraseInternalEdge_eq
#print axioms FeynmanSubgraph.contract_isOnePI
#print axioms FeynmanSubgraph.contract_isDivergent
#print axioms FeynmanSubgraph.contract_isConnectedDivergent

-- Sprint E artifacts (H6.1, H6.4, H6.5, H6.6a, H6.6b, H6.7 facade, H6.8)
#print axioms repG_internalEdges_card_eq_of_toClass
#print axioms repG_toHopfGen_internalEdges_card_lt_of_mem_forestCoproductProperForestIndex
#print axioms antipodeGen_forest
#print axioms antipode_forest
#print axioms antipode_forest_one
#print axioms antipode_forest_X
#print axioms antipode_forest_mul
#print axioms antipode_forest_toHopfH_admissibleSubgraph
#print axioms antipode_forest_admissibleForestStrictSummandWithCanonicalStars_of_mem
#print axioms mul_antipode_rTensor_coproduct_strict_forest_X
#print axioms mul_antipode_rTensor_coproduct_strict_forest
#print axioms AntipodeStrictForestRightReady
#print axioms instHopfAlgebraStructHopfHStrictForest
#print axioms instHopfAlgebraHopfHStrictForest

end GaugeGeometry.QFT.Combinatorial
