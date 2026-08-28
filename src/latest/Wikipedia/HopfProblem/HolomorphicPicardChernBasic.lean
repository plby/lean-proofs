import Wikipedia.HopfProblem.HolomorphicPicardGroup
import Wikipedia.HopfProblem.HolomorphicExponentialSheaf
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-!
# First Chern classes from the original holomorphic exponential sequence

For an arbitrary original native holomorphic line bundle, the class below
is the genuine exponential connecting map applied to its original native
unit cocycle class. The integer sheaf and the ordinary exponential retain
the already proved normalization `n ↦ 2πi n`. No vanishing or numerical
cohomology computation enters the definition.

This is the exponential-sequence definition of the integral sheaf Chern
class. Comparison with singular cohomology is a separate genuine map, and
comparison with separately constructed winding representatives is not
assumed here.
-/

noncomputable section

open Bundle CategoryTheory CategoryTheory.Abelian
open scoped ContDiff

namespace Wikipedia.HopfProblem.HolomorphicPicard.Chern

open HolomorphicExponentialSheaf HolomorphicPicardNative
  PeriodTorusLineBundleClassificationNative

universe u v

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
    (M : Type) [TopologicalSpace M] [ChartedSpace H M]

/-- The genuine integral sheaf cohomology used by the original exponential sequence. -/
abbrev IntegralCohomology (n : ℕ) : Type :=
  CategoryTheory.Sheaf.H.{0} (integerSheaf (TopCat.of M)) n

instance integralCohomologyAddCommGroup (n : ℕ) : AddCommGroup (IntegralCohomology M n) :=
  Ext.instAddCommGroup

/-- The original connecting map, constructed by composition with the
actual short exact exponential sequence's derived extension class. -/
def exponentialConnecting (n : ℕ) :
    CategoryTheory.Sheaf.H.{0} (unitsSheaf I M) n →+ IntegralCohomology M (n + 1) :=
  (exponentialComplex_shortExact I M).extClass.postcomp
    (integerULiftSheaf (TopCat.of M)) rfl

@[simp] theorem exponentialConnecting_apply (n : ℕ)
    (x : CategoryTheory.Sheaf.H.{0} (unitsSheaf I M) n) :
    exponentialConnecting I M n x =
      x.comp (exponentialComplex_shortExact I M).extClass rfl := rfl

/-- Genuine derived exactness immediately before the original connecting map. -/
theorem exponentialConnecting_exact (n : ℕ) :
    Function.Exact (CategoryTheory.Sheaf.H.map (exponential I M) n)
      (exponentialConnecting I M n) :=
  (ShortComplex.ab_exact_iff_function_exact _).mp
    (Ext.covariant_sequence_exact₃'
      (C := TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of M))
      (integerULiftSheaf (TopCat.of M)) (exponentialComplex_shortExact I M) n (n + 1) rfl)

variable (V : M → Type u)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)]
    [FiberBundle ℂ V] [VectorBundle ℂ ℂ V] [ContMDiffVectorBundle ω ℂ V I]

/-- The exponential first Chern class of the original native fibre family.
Its input is the original transition cocycle, not a classification label. -/
def nativeFirstChernClass : IntegralCohomology M 2 :=
  exponentialConnecting I M 1 (HolomorphicPicard.nativeClass I M V)

/-- The literal original unit-cocycle and original exponential-extension formula. -/
theorem nativeFirstChernClass_eq_cocycle :
    nativeFirstChernClass I M V =
      (CechExtension.classOf (nativeCocycle I M V) (nativeCover_covers M V)).comp
        (exponentialComplex_shortExact I M).extClass rfl := rfl

/-- Vanishing is exactly liftability through the original exponential on
genuine cohomology, by the actual long exact sequence. -/
theorem nativeFirstChernClass_eq_zero_iff_exponential :
    nativeFirstChernClass I M V = 0 ↔
      ∃ a : CategoryTheory.Sheaf.H.{0} (HolomorphicFunctionSheaf.additiveSheaf I M) 1,
        CategoryTheory.Sheaf.H.map (exponential I M) 1 a = HolomorphicPicard.nativeClass I M V :=
  exponentialConnecting_exact I M 1 (HolomorphicPicard.nativeClass I M V)

variable (W : M → Type v)
    [∀ x, AddCommMonoid (W x)] [∀ x, Module ℂ (W x)]
    [∀ x, TopologicalSpace (W x)] [TopologicalSpace (TotalSpace ℂ W)]
    [FiberBundle ℂ W] [VectorBundle ℂ ℂ W] [ContMDiffVectorBundle ω ℂ W I]

/-- Actual analytic fibre-linear bundle isomorphisms preserve this original class. -/
theorem nativeFirstChernClass_eq_of_iso (e : AnalyticBundleIso I V W) :
    nativeFirstChernClass I M V = nativeFirstChernClass I M W :=
  congrArg (exponentialConnecting I M 1) (nativeClass_eq_of_iso I M V W e)

/-- The same genuine class for a bundled original native line bundle. -/
def firstChernClass (L : LineBundle.{u} I M) : IntegralCohomology M 2 :=
  nativeFirstChernClass I M L.Fiber

@[simp] theorem firstChernClass_ofFamily :
    firstChernClass I M (LineBundle.ofFamily I M V) = nativeFirstChernClass I M V := rfl

theorem firstChernClass_eq_connecting (L : LineBundle.{u} I M) :
    firstChernClass I M L =
      exponentialConnecting I M 1 (LineBundle.cohomologyClass I M L) := rfl

end Wikipedia.HopfProblem.HolomorphicPicard.Chern
