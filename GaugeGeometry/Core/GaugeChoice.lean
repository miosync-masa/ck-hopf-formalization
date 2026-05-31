import GaugeGeometry.Core.Sector

namespace GaugeGeometry.Core

/--
A minimal gauge-choice record.

Version 1 only records which of the three canonical gauge sectors
are present in the model specification.
This keeps the file neutral and upstream of all QFT layers.
-/
structure GaugeChoice where
  hasHypercharge : Bool
  hasWeak : Bool
  hasColor : Bool

/--
Access the gauge-choice flag by sector label.
-/
def GaugeChoice.hasSector (g : GaugeChoice) : GaugeSector → Bool
  | .hypercharge => g.hasHypercharge
  | .weak        => g.hasWeak
  | .color       => g.hasColor

@[simp] theorem GaugeChoice.hasSector_hypercharge (g : GaugeChoice) :
    g.hasSector .hypercharge = g.hasHypercharge := by
  rfl

@[simp] theorem GaugeChoice.hasSector_weak (g : GaugeChoice) :
    g.hasSector .weak = g.hasWeak := by
  rfl

@[simp] theorem GaugeChoice.hasSector_color (g : GaugeChoice) :
    g.hasSector .color = g.hasColor := by
  rfl

/--
Build a gauge choice from a sector-indexed Boolean function.
-/
def gaugeChoiceOfFn (f : GaugeSector → Bool) : GaugeChoice where
  hasHypercharge := f .hypercharge
  hasWeak := f .weak
  hasColor := f .color

@[simp] theorem gaugeChoiceOfFn_hasSector (f : GaugeSector → Bool) (s : GaugeSector) :
    (gaugeChoiceOfFn f).hasSector s = f s := by
  cases s <;> rfl

/--
Canonical SM/MSSM gauge choice: U(1) × SU(2) × SU(3).
At this level, SM and MSSM share the same gauge-sector selection.
-/
def standardGaugeChoice : GaugeChoice where
  hasHypercharge := true
  hasWeak := true
  hasColor := true

/--
Predicate expressing that all three canonical sectors are present.
-/
def GaugeChoice.isStandardLike (g : GaugeChoice) : Prop :=
  g.hasHypercharge = true ∧ g.hasWeak = true ∧ g.hasColor = true

@[simp] theorem standardGaugeChoice_hasHypercharge :
    standardGaugeChoice.hasHypercharge = true := by
  rfl

@[simp] theorem standardGaugeChoice_hasWeak :
    standardGaugeChoice.hasWeak = true := by
  rfl

@[simp] theorem standardGaugeChoice_hasColor :
    standardGaugeChoice.hasColor = true := by
  rfl

@[simp] theorem standardGaugeChoice_isStandardLike :
    standardGaugeChoice.isStandardLike := by
  constructor
  · rfl
  constructor
  · rfl
  · rfl

@[simp] theorem GaugeChoice_eta (g : GaugeChoice) :
    GaugeChoice.mk g.hasHypercharge g.hasWeak g.hasColor = g := by
  cases g
  rfl

end GaugeGeometry.Core
