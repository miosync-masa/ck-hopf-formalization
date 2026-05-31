import GaugeGeometry.Core.ModelSpec
import GaugeGeometry.Core.ObservationData

namespace GaugeGeometry.Core

/--
External inputs combine:
- a theoretical model specification, and
- observational boundary data.

This file is intentionally thin: it does not add new physics,
it only packages the two upstream inputs needed by downstream layers.
-/
structure ExternalInputs where
  modelSpec : ModelSpec
  observationData : ObservationData

/--
Project the reference scale from the observational input.
-/
def ExternalInputs.referenceScale (E : ExternalInputs) : ℝ :=
  E.observationData.referenceScale

/--
Project the measured alpha_s input from the observational input.
-/
def ExternalInputs.alphaS (E : ExternalInputs) : MeasuredValue :=
  E.observationData.alphaS

/--
Project the measured quark-mass inputs from the observational input.
-/
def ExternalInputs.quarkMasses (E : ExternalInputs) : QuarkMassInputs :=
  E.observationData.quarkMasses

/--
Predicate: the packaged model uses the canonical SM/MSSM gauge choice.
-/
def ExternalInputs.hasStandardGaugeChoice (E : ExternalInputs) : Prop :=
  E.modelSpec.hasStandardGaugeChoice

/--
Predicate: the packaged model is Standard Model.
-/
def ExternalInputs.isSM (E : ExternalInputs) : Prop :=
  E.modelSpec.isSM

/--
Predicate: the packaged model is MSSM.
-/
def ExternalInputs.isMSSM (E : ExternalInputs) : Prop :=
  E.modelSpec.isMSSM

@[simp] theorem ExternalInputs.referenceScale_def
    (E : ExternalInputs) :
    E.referenceScale = E.observationData.referenceScale := by
  rfl

@[simp] theorem ExternalInputs.alphaS_def
    (E : ExternalInputs) :
    E.alphaS = E.observationData.alphaS := by
  rfl

@[simp] theorem ExternalInputs.quarkMasses_def
    (E : ExternalInputs) :
    E.quarkMasses = E.observationData.quarkMasses := by
  rfl

@[simp] theorem ExternalInputs.hasStandardGaugeChoice_def
    (E : ExternalInputs) :
    E.hasStandardGaugeChoice = E.modelSpec.hasStandardGaugeChoice := by
  rfl

@[simp] theorem ExternalInputs.isSM_def
    (E : ExternalInputs) :
    E.isSM = E.modelSpec.isSM := by
  rfl

@[simp] theorem ExternalInputs.isMSSM_def
    (E : ExternalInputs) :
    E.isMSSM = E.modelSpec.isMSSM := by
  rfl

/--
Canonical external inputs for the Standard Model,
built from a supplied observational data package.
-/
def standardModelExternalInputs (obs : ObservationData) : ExternalInputs where
  modelSpec := standardModelSpec
  observationData := obs

/--
Canonical external inputs for the MSSM,
built from a supplied observational data package.
-/
def mssmExternalInputs (obs : ObservationData) : ExternalInputs where
  modelSpec := mssmModelSpec
  observationData := obs

@[simp] theorem standardModelExternalInputs_modelSpec
    (obs : ObservationData) :
    (standardModelExternalInputs obs).modelSpec = standardModelSpec := by
  rfl

@[simp] theorem standardModelExternalInputs_observationData
    (obs : ObservationData) :
    (standardModelExternalInputs obs).observationData = obs := by
  rfl

@[simp] theorem mssmExternalInputs_modelSpec
    (obs : ObservationData) :
    (mssmExternalInputs obs).modelSpec = mssmModelSpec := by
  rfl

@[simp] theorem mssmExternalInputs_observationData
    (obs : ObservationData) :
    (mssmExternalInputs obs).observationData = obs := by
  rfl

@[simp] theorem standardModelExternalInputs_isSM
    (obs : ObservationData) :
    (standardModelExternalInputs obs).isSM := by
  simp [ExternalInputs.isSM]

@[simp] theorem mssmExternalInputs_isMSSM
    (obs : ObservationData) :
    (mssmExternalInputs obs).isMSSM := by
  simp [ExternalInputs.isMSSM]

@[simp] theorem standardModelExternalInputs_hasStandardGaugeChoice
    (obs : ObservationData) :
    (standardModelExternalInputs obs).hasStandardGaugeChoice := by
  simp [ExternalInputs.hasStandardGaugeChoice]

@[simp] theorem mssmExternalInputs_hasStandardGaugeChoice
    (obs : ObservationData) :
    (mssmExternalInputs obs).hasStandardGaugeChoice := by
  simp [ExternalInputs.hasStandardGaugeChoice]

@[simp] theorem ExternalInputs_eta (E : ExternalInputs) :
    ExternalInputs.mk E.modelSpec E.observationData = E := by
  cases E
  rfl

end GaugeGeometry.Core
