import Wikipedia.HopfProblem.SpecialPeriodsThreefold
import Wikipedia.HopfProblem.HolomorphicExponentialSheaf
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-!
# The actual exponential long exact sequence on the constructed threefold

The cohomology groups below are Mathlib's original derived `Sheaf.H`
groups of the actual holomorphic function and unit sheaves. The maps are
induced by the original ordinary exponential and the original normalized
integer inclusion. Both exactness statements are instances of the genuine
derived `Ext` long exact sequence of the already proved short exact
exponential sequence.
-/

noncomputable section

open CategoryTheory CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.PicardExponential

open HolomorphicExponentialSheaf

attribute [local instance] chartedSpace

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

/-- Genuine first cohomology of the original holomorphic function sheaf. -/
abbrev HolomorphicH1 : Type :=
  CategoryTheory.Sheaf.H.{0} (HolomorphicFunctionSheaf.additiveSheaf IF Space) 1

/-- Genuine first cohomology of the original holomorphic unit sheaf. -/
abbrev UnitsH1 : Type := CategoryTheory.Sheaf.H.{0} (unitsSheaf IF Space) 1

instance holomorphicH1AddCommGroup : AddCommGroup HolomorphicH1 := Ext.instAddCommGroup
instance unitsH1AddCommGroup : AddCommGroup UnitsH1 := Ext.instAddCommGroup

local instance (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H.{0} (integerSheaf (TopCat.of Space)) n) :=
  Ext.instAddCommGroup

/-- The original holomorphic exponential, on genuine degree-one cohomology. -/
def exponentialH1 : HolomorphicH1 →+ UnitsH1 :=
  CategoryTheory.Sheaf.H.map (exponential IF Space) 1

@[simp] theorem exponentialH1_apply (x : HolomorphicH1) :
    exponentialH1 x = CategoryTheory.Sheaf.H.map (exponential IF Space) 1 x := rfl

/-- The genuine connecting homomorphism of the original exponential sequence. -/
def exponentialConnectingH1 : UnitsH1 →+
    CategoryTheory.Sheaf.H.{0} (integerSheaf (TopCat.of Space)) 2 :=
  (exponentialComplex_shortExact IF Space).extClass.postcomp
    (integerULiftSheaf (TopCat.of Space)) rfl

@[simp] theorem exponentialConnectingH1_apply (x : UnitsH1) :
    exponentialConnectingH1 x = x.comp (exponentialComplex_shortExact IF Space).extClass rfl := rfl

/-- Exactness at original holomorphic degree-one cohomology. The first
map retains the original inclusion `n ↦ 2πi n`. -/
theorem exponentialH1_exact :
    Function.Exact (CategoryTheory.Sheaf.H.map (integerInclusion IF Space) 1) exponentialH1 :=
  (ShortComplex.ab_exact_iff_function_exact _).mp
    (Ext.covariant_sequence_exact₂'
      (C := TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of Space))
      (integerULiftSheaf (TopCat.of Space))
      (exponentialComplex_shortExact IF Space) 1)

/-- Exactness at original unit-sheaf degree-one cohomology. -/
theorem exponentialH1_connecting_exact : Function.Exact exponentialH1 exponentialConnectingH1 :=
  (ShortComplex.ab_exact_iff_function_exact _).mp
    (Ext.covariant_sequence_exact₃'
      (C := TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of Space))
      (integerULiftSheaf (TopCat.of Space))
      (exponentialComplex_shortExact IF Space) 1 2 rfl)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.PicardExponential
