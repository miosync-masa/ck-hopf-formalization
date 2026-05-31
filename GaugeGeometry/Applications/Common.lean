/-
  Applications/Common.lean

  Shared abbreviations and helpers used by multiple Applications-layer
  files. Kept in a dedicated module to avoid duplicate `abbrev`
  declarations when two sibling Applications files are imported
  together (e.g. `AlphaSPrediction` and `MassRatioDecomposition`
  loaded transitively through `Main.lean`).
-/
import GaugeGeometry.QFT.Representation.GaugeProduct
import GaugeGeometry.QFT.Representation.BetaCoefficients
import GaugeGeometry.QFT.Analytic.RGFlow

namespace GaugeGeometry.Applications

abbrev GaugeIndex := GaugeGeometry.QFT.Representation.GaugeIndex
abbrev BetaCoefficients := GaugeGeometry.QFT.Analytic.BetaCoefficients
abbrev AlphaInvAt := GaugeGeometry.QFT.Analytic.AlphaInvAt

abbrev u1Index := GaugeGeometry.QFT.Representation.u1Index
abbrev su2Index := GaugeGeometry.QFT.Representation.su2Index
abbrev su3Index := GaugeGeometry.QFT.Representation.su3Index

/-- Shared MSSM beta-coefficient handle used across Applications. -/
def mssmBetaCoefficients : BetaCoefficients :=
  fun i => GaugeGeometry.QFT.Representation.betaTriple i

end GaugeGeometry.Applications
