import GaugeGeometry.Core.ObservationData
import Mathlib.Data.Real.Basic

namespace GaugeGeometry.Axioms

open GaugeGeometry.Core

/--
External observational input package.
Version 1 treats PDG data as an observational boundary condition.
-/
axiom pdgObservationData : ObservationData

/--
A measured value has nonnegative uncertainty.
-/
def HasNonnegativeUncertainty (x : MeasuredValue) : Prop :=
  0 ≤ x.uncertainty

/--
A measured value has positive central value.
-/
def HasPositiveCentralValue (x : MeasuredValue) : Prop :=
  0 < x.centralValue

/--
Convenient projections from the PDG input package.
These are noncomputable because they depend on an axiom.
-/
noncomputable def pdgAlphaS : MeasuredValue :=
  pdgObservationData.alphaS

noncomputable def pdgQuarkMass (q : QuarkFlavor) : MeasuredValue :=
  pdgObservationData.quarkMasses.get q

/--
Basic observational regularity assumptions.
-/
axiom pdg_referenceScale_positive :
  0 < pdgObservationData.referenceScale

axiom pdg_alphaS_positive :
  HasPositiveCentralValue pdgAlphaS

axiom pdg_alphaS_uncertainty_nonneg :
  HasNonnegativeUncertainty pdgAlphaS

axiom pdg_quarkMass_positive :
  ∀ q : QuarkFlavor, HasPositiveCentralValue (pdgQuarkMass q)

axiom pdg_quarkMass_uncertainty_nonneg :
  ∀ q : QuarkFlavor, HasNonnegativeUncertainty (pdgQuarkMass q)

@[simp] theorem pdgAlphaS_def :
    pdgAlphaS = pdgObservationData.alphaS := by
  rfl

@[simp] theorem pdgQuarkMass_def (q : QuarkFlavor) :
    pdgQuarkMass q = pdgObservationData.quarkMasses.get q := by
  rfl

@[simp] theorem pdg_alphaS_centralValue_positive :
    0 < pdgAlphaS.centralValue := by
  simpa [HasPositiveCentralValue] using pdg_alphaS_positive

@[simp] theorem pdg_alphaS_uncertainty_nonnegative :
    0 ≤ pdgAlphaS.uncertainty := by
  simpa [HasNonnegativeUncertainty] using pdg_alphaS_uncertainty_nonneg

@[simp] theorem pdg_quarkMass_centralValue_positive (q : QuarkFlavor) :
    0 < (pdgQuarkMass q).centralValue := by
  simpa [HasPositiveCentralValue] using pdg_quarkMass_positive q

@[simp] theorem pdg_quarkMass_uncertainty_nonnegative (q : QuarkFlavor) :
    0 ≤ (pdgQuarkMass q).uncertainty := by
  simpa [HasNonnegativeUncertainty] using pdg_quarkMass_uncertainty_nonneg q

end GaugeGeometry.Axioms
