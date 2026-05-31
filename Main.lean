/-
# CK Hopf Formalization — artifact entry point

This file is the entry point for the `ck-hopf-formalization` artifact.  It imports
the top of the dependency chain and `#check`s the headline certificates, so that
`lake build Main` compiles the whole development and confirms the dependency
boundary.

The Lean namespace `GaugeGeometry.QFT…` is intentionally retained (this repository
is extracted from a broader `GaugeGeometry` development); import paths and theorem
names are stable.
-/
import GaugeGeometry.QFT.HopfAlgebra.HopfAlgebra
import GaugeGeometry.QFT.HopfAlgebra.AntipodeConvolution
import GaugeGeometry.QFT.HopfAlgebra.BoundaryResolved
import GaugeGeometry.QFT.HopfAlgebra.AxiomAudit
import GaugeGeometry.QFT.Combinatorial.ResolvedFeynmanGraphs

open GaugeGeometry.QFT.Combinatorial

-- Headline certificate: the conditional `HopfAlgebra ℚ HopfH` follows from exactly
-- the two boundary-semantics facades + the power-counting reflection — no antipode
-- core-identity kernel.
#check @hopfAlgebraHopfH_ofBoundaryFacadesAndReflection_convolution

-- Coassociativity boundary: `CoassocStrictForestH58Ready` from the two facades.
#check @coassocStrictForestH58Ready_ofBoundaryFacadesAndReflection

-- Right antipode axiom via the convolution / local-nilpotency route (★ eliminated).
#check @AntipodeStrictForestRightReady_ofConvolution

def main : IO Unit :=
  IO.println
    "ck-hopf-formalization: conditional `HopfAlgebra ℚ HopfH` is gated on exactly \
     two boundary-semantics facades (both Track-R-resolved) plus the power-counting \
     environment. See the #check certificates above and docs/."
