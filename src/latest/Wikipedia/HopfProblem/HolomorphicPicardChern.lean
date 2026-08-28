import Wikipedia.HopfProblem.HolomorphicPicardChernBasic

/-!
# The original Picard-group first-Chern homomorphism

The homomorphism is the original native unit-cocycle class followed by
the actual exponential connecting homomorphism. The proved native tensor
and dual class formulas give additivity, sign reversal, and the zero class
of the original trivial bundle, without assuming any cohomology vanishing.
-/

noncomputable section

namespace Wikipedia.HopfProblem.HolomorphicPicard.Chern

open PeriodTorusLineBundleClassificationNative

universe u v

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
    (M : Type) [TopologicalSpace M] [ChartedSpace H M]

/-- The genuine first-Chern homomorphism from original native bundle
isomorphism classes under their actual tensor-product group law. -/
def firstChernHom : LineBundle.IsoClasses.{0} I M →+ IntegralCohomology M 2 :=
  (exponentialConnecting I M 1).comp (LineBundle.classificationAddEquiv I M).toAddMonoidHom

@[simp] theorem firstChernHom_apply (x : LineBundle.IsoClasses.{0} I M) :
    firstChernHom I M x =
      exponentialConnecting I M 1 (LineBundle.isoClassCohomologyClass I M x) := rfl

/-- The descended map retains the actual original bundle's class. -/
@[simp] theorem firstChernHom_toIsoClasses (L : LineBundle.{0} I M) :
    firstChernHom I M (LineBundle.toIsoClasses I M L) = firstChernClass I M L := rfl

theorem firstChernClass_eq_of_iso (L : LineBundle.{u} I M) (K : LineBundle.{v} I M)
    (e : AnalyticBundleIso I L.Fiber K.Fiber) : firstChernClass I M L = firstChernClass I M K :=
  nativeFirstChernClass_eq_of_iso I M L.Fiber K.Fiber e

/-- Tensor additivity for the independently constructed original native tensor bundle. -/
theorem firstChernClass_tensorBundle (L : LineBundle.{u} I M) (K : LineBundle.{v} I M) :
    firstChernClass I M (LineBundle.tensorBundle I M L K) =
      firstChernClass I M L + firstChernClass I M K := by
  simp only [firstChernClass_eq_connecting, LineBundle.cohomologyClass_tensorBundle, map_add]

theorem firstChernClass_dualBundle (L : LineBundle.{u} I M) :
    firstChernClass I M (LineBundle.dualBundle I M L) = -firstChernClass I M L := by
  simp only [firstChernClass_eq_connecting, LineBundle.cohomologyClass_dualBundle, map_neg]

theorem firstChernClass_trivialBundle :
    firstChernClass I M (LineBundle.trivialBundle I M) = 0 := by
  simp only [firstChernClass_eq_connecting, LineBundle.cohomologyClass_trivialBundle, map_zero]

theorem firstChernHom_add (x y : LineBundle.IsoClasses.{0} I M) :
    firstChernHom I M (x + y) = firstChernHom I M x + firstChernHom I M y :=
  map_add (firstChernHom I M) x y

theorem firstChernHom_zsmul (n : ℤ) (x : LineBundle.IsoClasses.{0} I M) :
    firstChernHom I M (n • x) = n • firstChernHom I M x :=
  map_zsmul (firstChernHom I M) n x

end Wikipedia.HopfProblem.HolomorphicPicard.Chern
