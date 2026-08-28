import Wikipedia.HopfProblem.CuspNormalizationSheafLocalCoordinatesExactTriples

/-!
# The complete source-oriented triple germ resolution

The arrows are genuine singular-germ restriction, the actual oriented
axis restrictions, and alternating evaluation. Exactness includes the
initial and terminal zero terms and is categorical in additive groups.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace Wikipedia.HopfProblem.CuspQuotient.NormalizationLocalCoordinates

open ToricFan CuspNormalization.Germs CuspNormalization.SheafGermComplex

def orientedTripleBranchComplex (s : Triangle) : ShortComplex AddCommGrpCat where
  X₁ := AddCommGrpCat.of (RestrictedAnalyticGerm (Finset.univ : Finset (Fin 3)))
  X₂ := AddCommGrpCat.of (Fin 3 → BranchGerm)
  X₃ := AddCommGrpCat.of (Fin 3 → AxisGerm)
  f := AddCommGrpCat.ofHom tripleRestriction.toAddMonoidHom
  g := AddCommGrpCat.ofHom (orientedTripleDifference s)
  zero := AddCommGrpCat.ext (orientedTripleRestriction_exact s).apply_apply_eq_zero

def orientedTripleAxisComplex (s : Triangle) : ShortComplex AddCommGrpCat where
  X₁ := AddCommGrpCat.of (Fin 3 → BranchGerm)
  X₂ := AddCommGrpCat.of (Fin 3 → AxisGerm)
  X₃ := AddCommGrpCat.of ℂ
  f := AddCommGrpCat.ofHom (orientedTripleDifference s)
  g := AddCommGrpCat.ofHom tripleAugmentation
  zero := AddCommGrpCat.ext (orientedTripleAugmentation_difference s)

theorem orientedTripleBranchComplex_exact (s : Triangle) :
    (orientedTripleBranchComplex s).Exact :=
  (ShortComplex.ab_exact_iff_function_exact (orientedTripleBranchComplex s)).mpr
    (orientedTripleRestriction_exact s)

theorem orientedTripleAxisComplex_exact (s : Triangle) :
    (orientedTripleAxisComplex s).Exact :=
  (ShortComplex.ab_exact_iff_function_exact (orientedTripleAxisComplex s)).mpr
    (orientedTripleDifference_exact s)

def orientedTripleStartComplex (s : Triangle) : ShortComplex AddCommGrpCat where
  X₁ := 0
  X₂ := (orientedTripleBranchComplex s).X₁
  X₃ := (orientedTripleBranchComplex s).X₂
  f := 0
  g := (orientedTripleBranchComplex s).f
  zero := zero_comp

def orientedTripleEndComplex (s : Triangle) : ShortComplex AddCommGrpCat where
  X₁ := (orientedTripleAxisComplex s).X₂
  X₂ := (orientedTripleAxisComplex s).X₃
  X₃ := 0
  f := (orientedTripleAxisComplex s).g
  g := 0
  zero := comp_zero

theorem orientedTripleStartComplex_exact (s : Triangle) :
    (orientedTripleStartComplex s).Exact :=
  ((orientedTripleStartComplex s).exact_iff_mono rfl).mpr
    ((AddCommGrpCat.mono_iff_injective _).mpr tripleRestriction_injective)

theorem orientedTripleEndComplex_exact (s : Triangle) :
    (orientedTripleEndComplex s).Exact :=
  ((orientedTripleEndComplex s).exact_iff_epi rfl).mpr
    ((AddCommGrpCat.epi_iff_surjective _).mpr tripleAugmentation_surjective)

/-- The complete actual triple germ resolution in the source's orientation. -/
def orientedTripleResolution (s : Triangle) : ComposableArrows AddCommGrpCat 5 :=
  ComposableArrows.mk₅ (orientedTripleStartComplex s).f (orientedTripleBranchComplex s).f
    (orientedTripleBranchComplex s).g (orientedTripleAxisComplex s).g
    (orientedTripleEndComplex s).g

theorem orientedTripleResolution_isComplex (s : Triangle) :
    (orientedTripleResolution s).IsComplex where
  zero i hi := by
    have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases h with rfl | rfl | rfl | rfl
    · exact (orientedTripleStartComplex s).zero
    · exact (orientedTripleBranchComplex s).zero
    · exact (orientedTripleAxisComplex s).zero
    · exact (orientedTripleEndComplex s).zero

theorem orientedTripleResolution_exact (s : Triangle) :
    (orientedTripleResolution s).Exact where
  toIsComplex := orientedTripleResolution_isComplex s
  exact i hi := by
    have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases h with rfl | rfl | rfl | rfl
    · exact orientedTripleStartComplex_exact s
    · exact orientedTripleBranchComplex_exact s
    · exact orientedTripleAxisComplex_exact s
    · exact orientedTripleEndComplex_exact s

end Wikipedia.HopfProblem.CuspQuotient.NormalizationLocalCoordinates
