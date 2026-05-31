import GaugeGeometry.Core.GaugeChoice

namespace GaugeGeometry.Axioms

open GaugeGeometry.Core

/--
External gauge-group choice.
Version 1 keeps only the statement that the chosen gauge sectors
are the canonical U(1) × SU(2) × SU(3) ones.
-/
axiom chosenGaugeChoice : GaugeChoice

/--
The chosen gauge structure is the standard three-factor choice.
-/
axiom chosenGaugeChoice_isStandardLike :
  chosenGaugeChoice.isStandardLike

@[simp] theorem chosenGaugeChoice_hasHypercharge :
    chosenGaugeChoice.hasHypercharge = true := by
  exact chosenGaugeChoice_isStandardLike.1

@[simp] theorem chosenGaugeChoice_hasWeak :
    chosenGaugeChoice.hasWeak = true := by
  exact chosenGaugeChoice_isStandardLike.2.1

@[simp] theorem chosenGaugeChoice_hasColor :
    chosenGaugeChoice.hasColor = true := by
  exact chosenGaugeChoice_isStandardLike.2.2

@[simp] theorem chosenGaugeChoice_hasSector_hypercharge :
    chosenGaugeChoice.hasSector .hypercharge = true := by
  simpa using chosenGaugeChoice_hasHypercharge

@[simp] theorem chosenGaugeChoice_hasSector_weak :
    chosenGaugeChoice.hasSector .weak = true := by
  simpa using chosenGaugeChoice_hasWeak

@[simp] theorem chosenGaugeChoice_hasSector_color :
    chosenGaugeChoice.hasSector .color = true := by
  simpa using chosenGaugeChoice_hasColor

end GaugeGeometry.Axioms
