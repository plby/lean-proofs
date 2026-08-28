import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalComparisonCuspFrames

/-!
# Actual cusp coefficients of the divisor and canonical sections

In the actual cusp chart, the Cartier section is `1/T` times its genuine
native chart frame, where `T` is the fixed reciprocal sphere coordinate.
The target frame is `T` times the actual regular canonical section. These
are identities of the original native bundle fibres and chart coefficients.
-/

noncomputable section

open Set Topology Bundle
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalComparisonCusp

open HolomorphicFunctionSheaf.SphereH1.NegativeOneFrames

attribute [local instance] Threefold.chartedSpace

/-- The literal reciprocal coordinate of the actual global projection. -/
def reciprocal (x : Threefold.Space) : ℂ :=
  GlobalCusp.reciprocalCoordinate (Threefold.projectionSphere x)

/-- The genuine source fraction, in its actual cusp defining chart. -/
theorem sourceFraction_eq_reciprocal_inv {x : Threefold.Space} (hx : x ∈ patch) :
    GlobalPrescribedDivisor.cartier.localFraction (true, none) x = (reciprocal x)⁻¹ := by
  rw [GlobalPrescribedDivisor.localFraction_outside, GlobalBasePullback.localFraction_infinity,
    GlobalBasePullback.infinityCoordinate_eq_reciprocal
      (GlobalBasePullback.cusp_projection_mem_infinityChart hx)]
  rfl

/-- The actual native local coefficient of the prescribed Cartier section. -/
theorem sourceRawSection_localCoefficient {x : Threefold.Space} (hx : x ∈ patch)
    (hg : x ∈ GlobalPrescribedDivisor.cartier.genericSet) :
    sourceData.localCoefficient GlobalPrescribedDivisor.cartier.rawSection (true, none) x =
      (reciprocal x)⁻¹ :=
  (GlobalPrescribedDivisor.rawSection_localCoefficient (true, none)
    (GlobalPrescribedDivisor.cuspPatch_subset_baseSet hx) hg).trans
      (sourceFraction_eq_reciprocal_inv hx)

/-- In the original source fibre, the actual section is `1/T` times its native chart frame. -/
theorem sourceRawSection_eq_inv_smul_frame {x : Threefold.Space} (hx : x ∈ patch)
    (hg : x ∈ GlobalPrescribedDivisor.cartier.genericSet) :
    GlobalPrescribedDivisor.cartier.rawSection x = (reciprocal x)⁻¹ • sourceFrame x := by
  let e := (sourceData.core.localTriv (true, none)).linearEquivAt ℂ x
    (GlobalPrescribedDivisor.cuspPatch_subset_baseSet hx)
  apply e.injective
  have hs : e (sourceFrame x) = 1 := sourceFrame_localCoefficient hx
  rw [map_smul, hs, smul_eq_mul, mul_one]
  exact sourceRawSection_localCoefficient hx hg

/-- The actual cusp chart and the actual generic set meet only in the actual regular locus. -/
theorem generic_mem_regular {x : Threefold.Space} (hx : x ∈ patch)
    (hg : x ∈ GlobalPrescribedDivisor.cartier.genericSet) : x ∈ regularLocus := by
  obtain ⟨hinf, h₁⟩ := (GlobalPrescribedDivisor.mem_genericSet x).mp hg
  have h₀ : Threefold.projectionSphere x ≠ ((0 : ℂ) : RiemannSphere) :=
    (mem_infinityChart _).mp (GlobalBasePullback.cusp_projection_mem_infinityChart hx)
  exact (mem_regularLocus_iff_sphere x).mpr ((mem_sphereRegularPatch _).mpr ⟨hinf, h₀, h₁⟩)

theorem reciprocal_ne_zero_of_generic {x : Threefold.Space} (hx : x ∈ patch)
    (hg : x ∈ GlobalPrescribedDivisor.cartier.genericSet) : reciprocal x ≠ 0 := by
  have hr := generic_mem_regular hx hg
  exact fun h => (GlobalCuspExtension.patch_mem_regular_iff (⟨x, hx⟩ : patch)).mp hr
    ((GlobalCuspExtension.patchReciprocal_eq_zero_iff (⟨x, hx⟩ : patch)).mp h)

/-- The genuine target frame is the reciprocal-coordinate multiple of the actual regular form. -/
theorem targetFrame_eq_reciprocal_smul {x : Threefold.Space} (hx : x ∈ patch)
    (hr : x ∈ regularLocus) :
    targetFrame x = reciprocal x • NativePresentation.fiberEquiv x
      (GlobalRegular.globalSection ⟨x, hr⟩) := by
  rw [targetFrame_of_mem hx]
  exact (congrArg (NativePresentation.fiberEquiv x)
    (GlobalCuspExtension.canonicalSection_overlap (⟨x, hx⟩ : patch) hr)).trans
      (map_smul (NativePresentation.fiberEquiv x) (reciprocal x)
        (GlobalRegular.globalSection ⟨x, hr⟩))

/-- The two actual section coefficients cancel, leaving the original regular canonical form. -/
theorem inv_smul_targetFrame {x : Threefold.Space} (hx : x ∈ patch)
    (hg : x ∈ GlobalPrescribedDivisor.cartier.genericSet) :
    (reciprocal x)⁻¹ • targetFrame x = NativePresentation.fiberEquiv x
      (GlobalRegular.globalSection ⟨x, generic_mem_regular hx hg⟩) := by
  rw [targetFrame_eq_reciprocal_smul hx (generic_mem_regular hx hg), smul_smul,
    inv_mul_cancel₀ (reciprocal_ne_zero_of_generic hx hg), one_smul]

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalComparisonCusp
