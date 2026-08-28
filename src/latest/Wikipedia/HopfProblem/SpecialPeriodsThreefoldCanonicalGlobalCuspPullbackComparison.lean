import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalCuspPullbackLocalDiffeomorph
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalCuspPullbackRegular

/-!
# The actual regular canonical form in the cusp volume frame

The two sections are compared by pullback through the actual logarithmic
cover. Its genuine derivative is invertible, so the computed alternating
covector identities determine the equality in the original canonical fibre.
The normalization is exactly `width / (2πi)^3`, with a single factor of the
original cusp parameter in the denominator.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalCuspPullback

open CuspUniformization CuspGeometry HolomorphicForms.Cusp GlobalRegular

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

attribute [local instance] CuspGeometry.nativeChartedSpace Threefold.chartedSpace

local instance ratioGlobalManifold : IsManifold IF ω Threefold.Space :=
  Threefold.space_isManifold

/-- The scalar obtained from the two actual derivative pullbacks. -/
def regularToCuspFactor (x : LogDomain) : ℂ :=
  (Triangle.width : ℂ) * regularCoefficient (toRegularCover x).1 / logarithmicVolumeFactor x

theorem regularToCuspFactor_ne_zero (x : LogDomain) : regularToCuspFactor x ≠ 0 :=
  div_ne_zero
    (mul_ne_zero (Complex.ofReal_ne_zero.mpr Triangle.width_ne_zero)
      (regularCoefficient_ne_zero _))
    (logarithmicVolumeFactor_ne_zero x)

/-- Exact factorization into the nonzero normalization constant and one cusp parameter. -/
theorem regularToCuspFactor_eq (x : LogDomain) :
    regularToCuspFactor x =
      ((Triangle.width : ℂ) / (2 * Real.pi * Complex.I : ℂ) ^ 3) *
        (regularCoefficient (toRegularCover x).1 / exponential x.val.1) := by
  simp only [regularToCuspFactor, logarithmicVolumeFactor, div_eq_mul_inv, mul_inv_rev]
  ring

/-- The same factor uses the actual global cusp coordinate, not a formal parameter. -/
theorem regularToCuspFactor_eq_cuspCoordinate (x : LogDomain) :
    regularToCuspFactor x =
      ((Triangle.width : ℂ) / (2 * Real.pi * Complex.I : ℂ) ^ 3) *
        (regularCoefficient (toRegularCover x).1 / cuspCoordinate (globalLogMap x)) := by
  rw [cuspCoordinate_globalLogMap]
  exact regularToCuspFactor_eq x

/-- Equality in the genuine canonical fibre follows from its injective actual pullback. -/
theorem globalSection_eq_factor_smul_cuspVolume (x : LogDomain) :
    globalSection (regularLogPoint x) =
      regularToCuspFactor x • Cusp.volumeAlongInclusion (localLogMap x) := by
  apply (canonicalLogarithmicPullback x).injective
  calc
    canonicalLogarithmicPullback x (globalSection (regularLogPoint x)) =
        ((Triangle.width : ℂ) * regularCoefficient (toRegularCover x).1) •
          TrianglePeriodFamily.Canonical.volume := globalSection_log_pullback x
    _ = regularToCuspFactor x •
        (logarithmicVolumeFactor x • TrianglePeriodFamily.Canonical.volume) := by
      rw [smul_smul, regularToCuspFactor,
        div_mul_cancel₀ _ (logarithmicVolumeFactor_ne_zero x)]
    _ = canonicalLogarithmicPullback x
        (regularToCuspFactor x • Cusp.volumeAlongInclusion (localLogMap x)) := by
      exact (congrArg (fun α : TrianglePeriodFamily.Canonical.TopCovector =>
        regularToCuspFactor x • α) (canonicalLogarithmicPullback_cuspVolume x)).symm.trans
          (map_smul (canonicalLogarithmicPullback x) (regularToCuspFactor x)
            (show bundle.Fiber (globalLogMap x) from
              Cusp.volumeAlongInclusion (localLogMap x))).symm

/-- The equality concerns the original full-patch cusp section inside the glued threefold. -/
theorem globalSection_eq_factor_smul_patchVolume (x : LogDomain) :
    globalSection (regularLogPoint x) =
      regularToCuspFactor x • Cusp.patchVolume (nativePatchBiholomorph (localLogMap x)) := by
  rw [Cusp.patchVolume_inclusion]
  exact globalSection_eq_factor_smul_cuspVolume x

/-- Multiplication by the actual cusp coordinate removes the single displayed denominator. -/
theorem cuspCoordinate_smul_globalSection (x : LogDomain) :
    cuspCoordinate (globalLogMap x) • globalSection (regularLogPoint x) =
      (((Triangle.width : ℂ) / (2 * Real.pi * Complex.I : ℂ) ^ 3) *
        regularCoefficient (toRegularCover x).1) •
          Cusp.patchVolume (nativePatchBiholomorph (localLogMap x)) := by
  have hq : cuspCoordinate (globalLogMap x) ≠ 0 := by
    rw [cuspCoordinate_globalLogMap]
    exact exponential_ne_zero _
  have he : id (α := ℂ) (globalSection (regularLogPoint x)) =
      regularToCuspFactor x *
        id (α := ℂ) (Cusp.patchVolume (nativePatchBiholomorph (localLogMap x))) :=
    globalSection_eq_factor_smul_patchVolume x
  change cuspCoordinate (globalLogMap x) * id (α := ℂ) (globalSection (regularLogPoint x)) =
    _ * id (α := ℂ) (Cusp.patchVolume (nativePatchBiholomorph (localLogMap x)))
  rw [he, regularToCuspFactor_eq_cuspCoordinate]
  field_simp

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalCuspPullback
