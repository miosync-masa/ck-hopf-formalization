/-
  Geometric/Platonic/Classification.lean
  The five Platonic solids theorem.
-/
import GaugeGeometry.Geometric.Platonic.Schlafli
import Mathlib.Tactic

namespace GaugeGeometry.Geometric.Platonic

inductive PlatonicSolid where
  | tetrahedron
  | cube
  | octahedron
  | dodecahedron
  | icosahedron
  deriving DecidableEq, Fintype, Repr

def PlatonicSolid.schlafli : PlatonicSolid → SchlafliPair
  | .tetrahedron => schlafli33
  | .cube => schlafli43
  | .octahedron => schlafli34
  | .dodecahedron => schlafli53
  | .icosahedron => schlafli35

def SchlafliPair.toPlatonicSolid (s : SchlafliPair) : PlatonicSolid :=
  if (s.p, s.q) = (3, 3) then
    .tetrahedron
  else if (s.p, s.q) = (3, 4) then
    .octahedron
  else if (s.p, s.q) = (3, 5) then
    .icosahedron
  else if (s.p, s.q) = (4, 3) then
    .cube
  else
    .dodecahedron

def platonic_bijection : PlatonicSolid ≃ SchlafliPair where
  toFun := PlatonicSolid.schlafli
  invFun := SchlafliPair.toPlatonicSolid
  left_inv := by
    intro s
    cases s <;> simp [PlatonicSolid.schlafli, SchlafliPair.toPlatonicSolid, schlafli33, schlafli34,
      schlafli35, schlafli43, schlafli53]
  right_inv := by
    intro s
    rcases schlafli_enumeration s with h33 | h34 | h35 | h43 | h53
    · apply SchlafliPair.ext
      · simpa [PlatonicSolid.schlafli, SchlafliPair.toPlatonicSolid, schlafli33, h33] using
          (congrArg Prod.fst h33).symm
      · simpa [PlatonicSolid.schlafli, SchlafliPair.toPlatonicSolid, schlafli33, h33] using
          (congrArg Prod.snd h33).symm
    · apply SchlafliPair.ext
      · simpa [PlatonicSolid.schlafli, SchlafliPair.toPlatonicSolid, schlafli34, h34] using
          (congrArg Prod.fst h34).symm
      · simpa [PlatonicSolid.schlafli, SchlafliPair.toPlatonicSolid, schlafli34, h34] using
          (congrArg Prod.snd h34).symm
    · apply SchlafliPair.ext
      · simpa [PlatonicSolid.schlafli, SchlafliPair.toPlatonicSolid, schlafli35, h35] using
          (congrArg Prod.fst h35).symm
      · simpa [PlatonicSolid.schlafli, SchlafliPair.toPlatonicSolid, schlafli35, h35] using
          (congrArg Prod.snd h35).symm
    · apply SchlafliPair.ext
      · simpa [PlatonicSolid.schlafli, SchlafliPair.toPlatonicSolid, schlafli43, h43] using
          (congrArg Prod.fst h43).symm
      · simpa [PlatonicSolid.schlafli, SchlafliPair.toPlatonicSolid, schlafli43, h43] using
          (congrArg Prod.snd h43).symm
    · apply SchlafliPair.ext
      · simpa [PlatonicSolid.schlafli, SchlafliPair.toPlatonicSolid, schlafli53, h53] using
          (congrArg Prod.fst h53).symm
      · simpa [PlatonicSolid.schlafli, SchlafliPair.toPlatonicSolid, schlafli53, h53] using
          (congrArg Prod.snd h53).symm

#print axioms platonic_bijection

end GaugeGeometry.Geometric.Platonic
