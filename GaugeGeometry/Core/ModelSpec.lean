import GaugeGeometry.Core.GaugeChoice
import GaugeGeometry.Core.MatterContent

namespace GaugeGeometry.Core

/--
A minimal theoretical model specification.

Version 1 contains only:
- the gauge-sector choice,
- the matter-content choice.

Observational inputs are kept separate and should enter later
through `ExternalInputs.lean`.
-/
structure ModelSpec where
  gaugeChoice : GaugeChoice
  matterContent : MatterContent

/--
Predicate: the model uses the canonical SM/MSSM gauge-sector choice.
-/
def ModelSpec.hasStandardGaugeChoice (M : ModelSpec) : Prop :=
  M.gaugeChoice.isStandardLike

/--
Predicate: the model uses Standard Model matter content.
-/
def ModelSpec.isSM (M : ModelSpec) : Prop :=
  M.matterContent.isSM

/--
Predicate: the model uses MSSM matter content.
-/
def ModelSpec.isMSSM (M : ModelSpec) : Prop :=
  M.matterContent.isMSSM

/--
Canonical Standard Model specification.
-/
def standardModelSpec : ModelSpec where
  gaugeChoice := standardGaugeChoice
  matterContent := standardModel

/--
Canonical MSSM specification.
-/
def mssmModelSpec : ModelSpec where
  gaugeChoice := standardGaugeChoice
  matterContent := mssm

@[simp] theorem standardModelSpec_gaugeChoice :
    standardModelSpec.gaugeChoice = standardGaugeChoice := by
  rfl

@[simp] theorem standardModelSpec_matterContent :
    standardModelSpec.matterContent = standardModel := by
  rfl

@[simp] theorem mssmModelSpec_gaugeChoice :
    mssmModelSpec.gaugeChoice = standardGaugeChoice := by
  rfl

@[simp] theorem mssmModelSpec_matterContent :
    mssmModelSpec.matterContent = mssm := by
  rfl

@[simp] theorem standardModelSpec_hasStandardGaugeChoice :
    standardModelSpec.hasStandardGaugeChoice := by
  simp [ModelSpec.hasStandardGaugeChoice]

@[simp] theorem mssmModelSpec_hasStandardGaugeChoice :
    mssmModelSpec.hasStandardGaugeChoice := by
  simp [ModelSpec.hasStandardGaugeChoice]

@[simp] theorem standardModelSpec_isSM :
    standardModelSpec.isSM := by
  simp [ModelSpec.isSM]

@[simp] theorem mssmModelSpec_isMSSM :
    mssmModelSpec.isMSSM := by
  simp [ModelSpec.isMSSM]

@[simp] theorem standardModelSpec_not_MSSM :
    ¬ standardModelSpec.isMSSM := by
  simp [ModelSpec.isMSSM]

@[simp] theorem mssmModelSpec_not_SM :
    ¬ mssmModelSpec.isSM := by
  simp [ModelSpec.isSM]

@[simp] theorem ModelSpec_eta (M : ModelSpec) :
    ModelSpec.mk M.gaugeChoice M.matterContent = M := by
  cases M
  rfl

end GaugeGeometry.Core
