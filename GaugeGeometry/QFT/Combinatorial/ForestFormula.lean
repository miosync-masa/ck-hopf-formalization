import GaugeGeometry.QFT.Combinatorial.SubGraph
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

/-!
# Zimmermann's forest formula — light-weight presentation

This file implements the Zimmermann forest formula

  R(Γ) = ∑_{F ∈ forests(Γ)} (∏_{γ ∈ F} (-T(γ))) · Rem(F)

as a purely `ℚ`-valued expression, *without* committing to a specific
counterterm operator or a specific residual evaluator. The shape of
the formula is fixed; the two evaluation functions
(`CountertermScheme.T` and `RemainderEvaluator.eval`) are left abstract.

This is the "light Connes–Kreimer" path: we recover the combinatorial
content of the forest formula without passing through the graph quotient
`Γ / γ` and without a full Hopf-algebra construction. The full Hopf
identification is a separate Phase.

## How this hooks into the rest of the project

* `Forest` and `FeynmanSubgraph` come from `SubGraph.lean`.
* The counterterm scheme and the residual evaluator are meant to be
  instantiated later from the representation layer
  (`QFT/Representation/BetaCoefficients.lean`, etc.), where the
  actual `ℚ`-valued data lives.
* For Theorem 1 (MSSM 1-loop beta coefficients), only the one-loop
  slice of `R_operation` is needed; higher-loop forests are supplied
  here for free as a consequence of the general definition.
-/

namespace GaugeGeometry.QFT.Combinatorial

/--
A counterterm scheme on `G` assigns a rational counterterm to every
subgraph of `G`. In the Zimmermann / Bogoliubov tradition this is the
operator `-T_γ` applied to each divergent subgraph; here it is exposed
as a plain `ℚ`-valued function so that the forest formula can be
written at the combinatorial level.

Only the value on divergent subgraphs matters for `R_operation`, but
we keep the domain untyped to avoid threading divergence proofs
through every definition. Convergent subgraphs can simply be assigned
`0`.
-/
structure CountertermScheme (G : FeynmanGraph) where
  /-- The counterterm value `T γ` assigned to each subgraph. -/
  T : FeynmanSubgraph G → ℚ

/--
A residual evaluator on `G` assigns a rational value to every finite
set of subgraphs of `G`, interpreted as "the residual value of the
ambient graph after the subgraphs in the forest have been collapsed
into their counterterms".

In the standard forest formula the residual is obtained by evaluating
`Γ / F` — i.e. the graph-quotient picture. Keeping the evaluator
abstract here is what allows us to avoid constructing `Γ / γ`
explicitly while still writing the full formula.
-/
structure RemainderEvaluator (G : FeynmanGraph) where
  /-- Residual value of `G` once all subgraphs in `F` are collapsed. -/
  eval : Finset (FeynmanSubgraph G) → ℚ

namespace Forest

/--
The contribution of a single forest to the forest formula:

  (∏_{γ ∈ F} (-T γ)) · Rem(F.elements).

This is the product part of Zimmermann's combinatorial sum, written as
a plain `ℚ`-valued expression.
-/
def contribution {G : FeynmanGraph} [DivergenceMeasure G]
    (C : CountertermScheme G) (Rem : RemainderEvaluator G)
    (F : Forest G) : ℚ :=
  (∏ γ ∈ F.elements, -C.T γ) * Rem.eval F.elements

@[simp] theorem contribution_empty {G : FeynmanGraph} [DivergenceMeasure G]
    (C : CountertermScheme G) (Rem : RemainderEvaluator G) :
    Forest.contribution C Rem (Forest.empty G) = Rem.eval ∅ := by
  unfold contribution Forest.empty
  simp

end Forest

/--
Zimmermann's forest formula `R` as a rational-valued operator on the
finite set of forests of `G`:

  R(G; F_set) := ∑_{F ∈ F_set} contribution(C, Rem, F).

The caller supplies:

* `C`, a counterterm scheme (`T`),
* `Rem`, a residual evaluator,
* `F_set`, the finite set of forests over which to sum.

Typical choices of `F_set` are:

* the set of all Zimmermann forests of `G` (full BPHZ `R` operation),
* the singleton `{Forest.empty G}` (unrenormalized value),
* a 1-loop slice consisting of single-element forests on one-loop
  divergent subgraphs (which is what Theorem 1 needs).

Keeping the carrier finite set explicit avoids committing to a global
enumeration of forests, which would require further classical choice
principles.
-/
def R_operation {G : FeynmanGraph} [DivergenceMeasure G]
    (C : CountertermScheme G) (Rem : RemainderEvaluator G)
    (F_set : Finset (Forest G)) : ℚ :=
  ∑ F ∈ F_set, Forest.contribution C Rem F

/-!
### Basic algebraic properties of `R_operation`
-/

@[simp] theorem R_operation_empty {G : FeynmanGraph} [DivergenceMeasure G]
    (C : CountertermScheme G) (Rem : RemainderEvaluator G) :
    R_operation C Rem (∅ : Finset (Forest G)) = 0 := by
  unfold R_operation
  simp

theorem R_operation_insert {G : FeynmanGraph} [DivergenceMeasure G]
    {C : CountertermScheme G} {Rem : RemainderEvaluator G}
    {F_set : Finset (Forest G)} {F : Forest G} (hF : F ∉ F_set) :
    R_operation C Rem (Insert.insert F F_set)
      = Forest.contribution C Rem F + R_operation C Rem F_set := by
  unfold R_operation
  rw [Finset.sum_insert hF]

/--
If the residual evaluator is identically zero, the forest formula
vanishes. This is the trivial check that `R_operation` respects the
`Rem.eval ≡ 0` degenerate case.
-/
theorem R_operation_eq_zero_of_eval_eq_zero
    {G : FeynmanGraph} [DivergenceMeasure G]
    {C : CountertermScheme G} {Rem : RemainderEvaluator G}
    {F_set : Finset (Forest G)}
    (hRem : ∀ F : Forest G, F ∈ F_set → Rem.eval F.elements = 0) :
    R_operation C Rem F_set = 0 := by
  unfold R_operation Forest.contribution
  apply Finset.sum_eq_zero
  intro F hF
  rw [hRem F hF]
  ring

/--
Singleton forest set containing only the empty forest: the
unrenormalized value, i.e. `Rem(∅)`.
-/
@[simp] theorem R_operation_singleton_empty
    {G : FeynmanGraph} [DivergenceMeasure G]
    (C : CountertermScheme G) (Rem : RemainderEvaluator G) :
    R_operation C Rem ({Forest.empty G} : Finset (Forest G))
      = Rem.eval ∅ := by
  unfold R_operation
  rw [Finset.sum_singleton]
  exact Forest.contribution_empty C Rem

end GaugeGeometry.QFT.Combinatorial
