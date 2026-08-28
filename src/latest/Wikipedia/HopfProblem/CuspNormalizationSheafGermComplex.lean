import Wikipedia.HopfProblem.CuspNormalizationSheafGermComplexGluing
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.ExactSequence

/-!
# The exact normal-crossing analytic-germ complex

The actual singular analytic-germ ring maps to the product of its plane
germs. Pairwise restrictions land in actual one-variable analytic germs,
and the last map is their alternating evaluation at the triple point.
All exactness assertions below are categorical exactness in additive
commutative groups, including the zero endpoints. The analytic
inclusion-exclusion and axis-extension proofs are in the imported files.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace Wikipedia.HopfProblem.CuspNormalization.SheafGermComplex

open Germs

/-- The first two nonzero arrows of the three-branch germ complex. -/
def tripleBranchComplex : ShortComplex AddCommGrpCat where
  X₁ := AddCommGrpCat.of (RestrictedAnalyticGerm (Finset.univ : Finset (Fin 3)))
  X₂ := AddCommGrpCat.of (Fin 3 → BranchGerm)
  X₃ := AddCommGrpCat.of (Fin 3 → AxisGerm)
  f := AddCommGrpCat.ofHom tripleRestriction.toAddMonoidHom
  g := AddCommGrpCat.ofHom tripleDifference
  zero := AddCommGrpCat.ext tripleRestriction_exact.apply_apply_eq_zero

/-- The last two nonzero arrows of the three-branch germ complex. -/
def tripleAxisComplex : ShortComplex AddCommGrpCat where
  X₁ := AddCommGrpCat.of (Fin 3 → BranchGerm)
  X₂ := AddCommGrpCat.of (Fin 3 → AxisGerm)
  X₃ := AddCommGrpCat.of ℂ
  f := AddCommGrpCat.ofHom tripleDifference
  g := AddCommGrpCat.ofHom tripleAugmentation
  zero := AddCommGrpCat.ext tripleAugmentation_difference

/-- The two-branch analytic-germ complex. -/
def doubleComplex : ShortComplex AddCommGrpCat where
  X₁ := AddCommGrpCat.of (RestrictedAnalyticGerm doubleBranches)
  X₂ := AddCommGrpCat.of (Fin 2 → BranchGerm)
  X₃ := AddCommGrpCat.of AxisGerm
  f := AddCommGrpCat.ofHom doubleRestriction.toAddMonoidHom
  g := AddCommGrpCat.ofHom doubleDifference
  zero := AddCommGrpCat.ext doubleRestriction_exact.apply_apply_eq_zero

theorem tripleBranchComplex_exact : tripleBranchComplex.Exact :=
  (ShortComplex.ab_exact_iff_function_exact tripleBranchComplex).mpr
    tripleRestriction_exact

theorem tripleAxisComplex_exact : tripleAxisComplex.Exact :=
  (ShortComplex.ab_exact_iff_function_exact tripleAxisComplex).mpr
    tripleDifference_exact

theorem doubleComplex_exact : doubleComplex.Exact :=
  (ShortComplex.ab_exact_iff_function_exact doubleComplex).mpr doubleRestriction_exact

/-- The two-plane singular germ ring, its two normalization germs, and
their common axis form a genuine short exact sequence. -/
theorem doubleComplex_shortExact : doubleComplex.ShortExact where
  exact := doubleComplex_exact
  mono_f := (AddCommGrpCat.mono_iff_injective _).mpr doubleRestriction_injective
  epi_g := (AddCommGrpCat.epi_iff_surjective _).mpr doubleDifference_surjective

/-- The initial zero arrow expresses injectivity of actual restriction. -/
def tripleStartComplex : ShortComplex AddCommGrpCat where
  X₁ := 0
  X₂ := tripleBranchComplex.X₁
  X₃ := tripleBranchComplex.X₂
  f := 0
  g := tripleBranchComplex.f
  zero := zero_comp

/-- The terminal zero arrow expresses surjectivity of alternating evaluation. -/
def tripleEndComplex : ShortComplex AddCommGrpCat where
  X₁ := tripleAxisComplex.X₂
  X₂ := tripleAxisComplex.X₃
  X₃ := 0
  f := tripleAxisComplex.g
  g := 0
  zero := comp_zero

theorem tripleStartComplex_exact : tripleStartComplex.Exact :=
  (tripleStartComplex.exact_iff_mono rfl).mpr
    ((AddCommGrpCat.mono_iff_injective _).mpr tripleRestriction_injective)

theorem tripleEndComplex_exact : tripleEndComplex.Exact :=
  (tripleEndComplex.exact_iff_epi rfl).mpr
    ((AddCommGrpCat.epi_iff_surjective _).mpr tripleAugmentation_surjective)

/-- The complete actual three-branch analytic-germ resolution, with zero
endpoints: `0 → O_{xyz=0,0} → ∏ O_{plane,0} → ∏ O_{axis,0} → ℂ → 0`. -/
def tripleResolution : ComposableArrows AddCommGrpCat 5 :=
  ComposableArrows.mk₅ tripleStartComplex.f tripleBranchComplex.f
    tripleBranchComplex.g tripleAxisComplex.g tripleEndComplex.g

theorem tripleResolution_isComplex : tripleResolution.IsComplex where
  zero i hi := by
    have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases h with rfl | rfl | rfl | rfl
    · exact tripleStartComplex.zero
    · exact tripleBranchComplex.zero
    · exact tripleAxisComplex.zero
    · exact tripleEndComplex.zero

/-- Exactness of the full three-branch analytic-germ resolution. -/
theorem tripleResolution_exact : tripleResolution.Exact where
  toIsComplex := tripleResolution_isComplex
  exact i hi := by
    have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases h with rfl | rfl | rfl | rfl
    · exact tripleStartComplex_exact
    · exact tripleBranchComplex_exact
    · exact tripleAxisComplex_exact
    · exact tripleEndComplex_exact

end Wikipedia.HopfProblem.CuspNormalization.SheafGermComplex
