import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupTotalNative
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupDerivationOperators

/-!
# The actual total resolution for every original period torus

The operators are constructed by prolonging the native Dolbeault
derivations through the genuine ring-Godement functor. Thus all
compatibility data, exactness and native cohomology comparisons above
are instantiated without any additional hypothesis on the period.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup

variable (p : PeriodDomain)

/-- The two actual native torus derivatives with their proved germ squares. -/
def totalOperators : Total.CompatibleOperators p where
  ringOperators := Derivation.nativeOperators p
  unit_derivative i := (Derivation.native_augmentation_derivative p i).symm

/-- The genuine signed total section algebra of the original period torus. -/
abbrev totalData := (totalOperators p).globalData

/-- The genuine actual partial resolution of the original holomorphic sheaf. -/
abbrev totalPartialResolution := (totalOperators p).partialResolution

/-- Native degree-one cohomology with its canonical actual total representative comparison. -/
abbrev totalNativeOneEquiv := (totalOperators p).nativeOneEquiv

/-- Native degree-two cohomology with its canonical actual total representative comparison. -/
abbrev totalNativeTwoEquiv := (totalOperators p).nativeTwoEquiv

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup
