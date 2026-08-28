import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalCusp
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsCuspChart

/-!
# The actual cusp canonical volume in the reference toric chart

Both pullbacks below use the genuine manifold derivatives.  The quotient
pullback retains the signed coefficient of its actual covering chart;
the reference-chart transition cancels that sign and leaves coefficient one.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalCuspPullback

open ToricCharts ToricFan CuspGeometry
open HolomorphicForms.Cusp

local notation "I₃" => modelWithCornersSelf ℂ (CoordinateSpace 3)
local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

attribute [local instance] CuspGeometry.nativeChartedSpace Threefold.chartedSpace

local instance nativeManifold : IsManifold I₃ ω LocalSpace := native_isManifold
local instance globalManifold : IsManifold IF ω Threefold.Space := Threefold.space_isManifold

/-- The original quotient map with its codomain named as the actual cusp piece. -/
def nativeQuotientMap : ToricSpace.Tube (CuspQuotient.disc data.radius) → LocalSpace :=
  CuspQuotient.quotientMap data.correction data.radius

theorem nativeQuotientMap_holomorphic : ContMDiff I₃ I₃ ω nativeQuotientMap :=
  CuspQuotient.quotientMap_holomorphic data.correction data.radius data.radius_pos
    data.radius_lt_one data.holomorphic data.smallDrift

/-- Pullback through the original quotient, with its original tangent charts. -/
theorem nativeVolume_quotient_pullback
    (a : ToricSpace.Tube (CuspQuotient.disc data.radius)) :
    (Cusp.nativeIntrinsicEquiv (nativeQuotientMap a)
      (Cusp.nativeVolume (nativeQuotientMap a))).compContinuousLinearMap
          (mfderiv I₃ I₃ nativeQuotientMap a) =
      ((ToricSpace.preferredTriangle (a : ToricSpace.Space)).rays.det : ℂ) •
        CanonicalBundle.volume := by
  have hf : MDifferentiableAt I₃ I₃
      nativeQuotientMap a := nativeQuotientMap_holomorphic.mdifferentiable (by simp) a
  have hm : mfderiv I₃ I₃ nativeQuotientMap a =
      fderiv ℂ (chartAt (CoordinateSpace 3)
        (nativeQuotientMap a) ∘ nativeQuotientMap ∘
        (chartAt (CoordinateSpace 3) a).symm) (chartAt (CoordinateSpace 3) a a) := by
    simp only [mfderiv, hf, writtenInExtChartAt, mfld_simps, fderivWithin_univ]
    rfl
  rw [hm]
  have ha := mem_chart_source (CoordinateSpace 3) a
  let := CuspQuotient.chartedSpace data.correction data.radius data.radius_pos
    data.radius_lt_one data.holomorphic data.smallDrift
  have he := CuspQuotient.canonicalVolume_pullback_quotientMap data.correction data.radius
    data.radius_pos data.radius_lt_one data.holomorphic data.smallDrift a
      (nativeQuotientMap a)
      (chartAt (CoordinateSpace 3) a a) ((chartAt (CoordinateSpace 3) a).map_source ha)
  rw [(chartAt (CoordinateSpace 3) a).left_inv ha] at he
  exact he (mem_chart_source (CoordinateSpace 3) _)

/-- The actual derivative of the reference lift is the displayed toric transition. -/
theorem referenceLift_mfderiv (w : referenceDomain) :
    mfderiv I₃ I₃ referenceLift w =
      fderiv ℂ ((ToricSpace.parametrization ToricSpace.referenceTriangle).trans
        (ToricSpace.parametrization
          (ToricSpace.preferredTriangle (referenceLift w : ToricSpace.Space))).symm)
        (w : CoordinateSpace 3) := by
  let e := (ToricSpace.parametrization ToricSpace.referenceTriangle).trans
    (ToricSpace.parametrization
      (ToricSpace.preferredTriangle (referenceLift w : ToricSpace.Space))).symm
  have hw : (w : CoordinateSpace 3) ∈ e.source := by
    refine ⟨mem_univ _, ?_⟩
    change (referenceLift w : ToricSpace.Space) ∈
      (ToricSpace.parametrization
        (ToricSpace.preferredTriangle (referenceLift w : ToricSpace.Space))).target
    rw [ToricSpace.parametrization_target]
    exact ToricSpace.preferred_mem (referenceLift w : ToricSpace.Space)
  have he : MDifferentiableAt I₃ I₃ e (w : CoordinateSpace 3) :=
    ((ToricSpace.transition_holomorphic _ _).contDiffAt
      (e.open_source.mem_nhds hw)).contMDiffAt.mdifferentiableAt (by simp)
  have hf := referenceLift_holomorphic.mdifferentiable (by simp) w
  have hs : MDifferentiableAt I₃ I₃ (extChartAt I₃ w) w :=
    mdifferentiableAt_extChartAt (mem_chart_source (CoordinateSpace 3) w)
  have ht : MDifferentiableAt I₃ I₃
      (extChartAt I₃ (referenceLift w)) (referenceLift w) :=
    mdifferentiableAt_extChartAt (mem_chart_source (CoordinateSpace 3) (referenceLift w))
  have hfun : (extChartAt I₃ (referenceLift w)) ∘ referenceLift =
      e ∘ extChartAt I₃ w := by
    funext v
    rfl
  have hl := mfderiv_comp w ht hf
  have hr := mfderiv_comp w he hs
  have h := hl.symm.trans ((mfderiv_congr (I := I₃) (I' := I₃) (x := w) hfun).trans hr)
  apply ContinuousLinearMap.ext
  intro v
  have hv := congrArg (fun L : CoordinateSpace 3 →L[ℂ] CoordinateSpace 3 => L v) h
  change mfderiv I₃ I₃ (extChartAt I₃ (referenceLift w)) (referenceLift w)
    (mfderiv I₃ I₃ referenceLift w v) =
      mfderiv I₃ I₃ e (extChartAt I₃ w w) (mfderiv I₃ I₃ (extChartAt I₃ w) w v) at hv
  rw [mfderiv_extChartAt_self, mfderiv_extChartAt_self] at hv
  change mfderiv I₃ I₃ referenceLift w v = mfderiv I₃ I₃ e (w : CoordinateSpace 3) v at hv
  exact hv.trans (congrArg (fun L : CoordinateSpace 3 →L[ℂ] CoordinateSpace 3 => L v)
    (mfderiv_eq_fderiv (f := (e : CoordinateSpace 3 → CoordinateSpace 3))))

/-- The genuine lift cancels the orientation of the preferred toric chart. -/
theorem referenceLift_signed_volume_pullback (w : referenceDomain) :
    (((ToricSpace.preferredTriangle (referenceLift w : ToricSpace.Space)).rays.det : ℂ) •
      CanonicalBundle.volume).compContinuousLinearMap (mfderiv I₃ I₃ referenceLift w) =
        CanonicalBundle.volume := by
  change ContinuousAlternatingMap.compContinuousLinearMap
    (CanonicalBundle.coefficientEquiv
      ((ToricSpace.preferredTriangle (referenceLift w : ToricSpace.Space)).rays.det : ℂ))
    (show CoordinateSpace 3 →L[ℂ] CoordinateSpace 3 from mfderiv I₃ I₃ referenceLift w) = _
  rw [referenceLift_mfderiv]
  change (((ToricSpace.preferredTriangle (referenceLift w : ToricSpace.Space)).rays.det : ℂ) •
    CanonicalBundle.volume).compContinuousLinearMap
      (fderiv ℂ ((ToricSpace.parametrization ToricSpace.referenceTriangle).trans
        (ToricSpace.parametrization
          (ToricSpace.preferredTriangle (referenceLift w : ToricSpace.Space))).symm)
        (w : CoordinateSpace 3)) = CanonicalBundle.volume
  rw [CanonicalBundle.pullback_eq_det_smul]
  have hw : (w : CoordinateSpace 3) ∈
      ((ToricSpace.parametrization ToricSpace.referenceTriangle).trans
        (ToricSpace.parametrization
          (ToricSpace.preferredTriangle (referenceLift w : ToricSpace.Space))).symm).source :=
    by
      refine ⟨mem_univ _, ?_⟩
      change (referenceLift w : ToricSpace.Space) ∈
        (ToricSpace.parametrization
          (ToricSpace.preferredTriangle (referenceLift w : ToricSpace.Space))).target
      rw [ToricSpace.parametrization_target]
      exact ToricSpace.preferred_mem (referenceLift w : ToricSpace.Space)
  rw [ToricSpace.parametrization_transition_det_fderiv _ _ hw, smul_smul,
    div_mul_cancel₀ _ (Triangle.signed_volume_coefficient_ne_zero _)]
  have href : (ToricSpace.referenceTriangle.rays.det : ℂ) = 1 := by
    norm_num [Triangle.rays_det, ToricSpace.referenceTriangle]
  rw [href, one_smul]

/-- In the full original reference chart, including the central fibre, the
native cusp canonical form is the standard alternating volume. -/
theorem nativeVolume_reference_pullback (w : referenceDomain) :
    (Cusp.nativeIntrinsicEquiv (referenceQuotient w)
      (Cusp.nativeVolume (referenceQuotient w))).compContinuousLinearMap
        (mfderiv I₃ I₃ referenceQuotient w) = CanonicalBundle.volume := by
  have hq := nativeQuotientMap_holomorphic.mdifferentiable (by simp)
  have he : referenceQuotient = nativeQuotientMap ∘ referenceLift := rfl
  rw [he, mfderiv_comp w (hq (referenceLift w))
    (referenceLift_holomorphic.mdifferentiable (by simp) w)]
  change ((Cusp.nativeIntrinsicEquiv (nativeQuotientMap (referenceLift w))
    (Cusp.nativeVolume (nativeQuotientMap (referenceLift w)))).compContinuousLinearMap
        (mfderiv I₃ I₃ nativeQuotientMap
          (referenceLift w))).compContinuousLinearMap (mfderiv I₃ I₃ referenceLift w) = _
  rw [nativeVolume_quotient_pullback]
  exact referenceLift_signed_volume_pullback w

/-- The same equality in the genuine canonical bundle of the glued threefold. -/
theorem globalVolume_reference_pullback (w : referenceDomain) :
    (intrinsicEquiv (referenceMap w)
      (Cusp.volumeAlongInclusion (referenceQuotient w))).compContinuousLinearMap
        (mfderiv I₃ IF referenceMap w) = CanonicalBundle.volume := by
  rw [referenceMap, mfderiv_comp w
    (CuspGeometry.inclusion_holomorphic.mdifferentiable (by simp) (referenceQuotient w))
    (referenceQuotient_holomorphic.mdifferentiable (by simp) w)]
  change ((intrinsicEquiv (CuspGeometry.inclusion (referenceQuotient w))
    (Cusp.volumeAlongInclusion (referenceQuotient w))).compContinuousLinearMap
      (mfderiv I₃ IF CuspGeometry.inclusion (referenceQuotient w))).compContinuousLinearMap
        (mfderiv I₃ I₃ referenceQuotient w) = _
  rw [← Cusp.inclusionPullback_intrinsic, Cusp.inclusionPullback_volumeAlongInclusion]
  exact nativeVolume_reference_pullback w

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalCuspPullback
