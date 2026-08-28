import Wikipedia.HopfProblem.CuspNormalizationSheafLocalCoordinatesExactPairsGluing

/-!
# The short exact analytic-germ complex for every actual double-branch pair

This is the two-branch local normalization sequence in the source's signed
coordinates, with the genuine reduced analytic-germ ring as its first term.
The analytic gluing construction proves exactness without a hypothesis of
cohomological or formal algebraic exactness.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.CuspQuotient.NormalizationLocalCoordinates

open ToricFan
open CuspNormalization.Germs CuspNormalization.SheafGermComplex

/-- The genuine local sequence for a source-oriented pair of branches. -/
def pairComplex (s : Triangle) (k : Fin 3) : ShortComplex AddCommGrpCat where
  X₁ := AddCommGrpCat.of (RestrictedAnalyticGerm (sourcePair s k))
  X₂ := AddCommGrpCat.of (Fin 2 → BranchGerm)
  X₃ := AddCommGrpCat.of AxisGerm
  f := AddCommGrpCat.ofHom (pairRestriction s k).toAddMonoidHom
  g := AddCommGrpCat.ofHom (pairDifference s k)
  zero := AddCommGrpCat.ext (pairRestriction_exact s k).apply_apply_eq_zero

theorem pairComplex_exact (s : Triangle) (k : Fin 3) : (pairComplex s k).Exact :=
  (ShortComplex.ab_exact_iff_function_exact (pairComplex s k)).mpr
    (pairRestriction_exact s k)

/-- Categorical short exactness, uniformly over the actual source edge and
the actual local triangular chart. -/
theorem pairComplex_shortExact (s : Triangle) (k : Fin 3) :
    (pairComplex s k).ShortExact where
  exact := pairComplex_exact s k
  mono_f := (AddCommGrpCat.mono_iff_injective _).mpr (pairRestriction_injective s k)
  epi_g := (AddCommGrpCat.epi_iff_surjective _).mpr (pairDifference_surjective s k)

end Wikipedia.HopfProblem.CuspQuotient.NormalizationLocalCoordinates
