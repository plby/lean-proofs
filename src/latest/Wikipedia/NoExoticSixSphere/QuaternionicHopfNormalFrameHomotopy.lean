import Wikipedia.NoExoticSixSphere.QuaternionicHopfRadialHomotopy

/-!
# The radial homotopy stays in the actual Hopf normal bundle

Every intermediate rotation fixes the original inclusion's tangent space.
The rotated frame is therefore injective with exactly the same normal
range. Its endpoint is the computed stereographic frame, with the scale
and fixed added-coordinate reflection still explicit.
-/

noncomputable section

open scoped Quaternion Manifold ContDiff
open unitInterval

namespace NoExoticSixSphere.QuaternionicHopf

theorem southFiberAmbient_tangent_iff (q : Sphere 3) (v : V 8) :
    v ∈ (NormalFrameOfEquations.ambientDifferential (𝓡 3) southFiberAmbient q).range ↔
      first v = 0 ∧ inner ℝ (southFiberPoint q).val v = 0 := by
  rw [NormalFrameOfEquations.range_ambientDifferential_eq_kernel
    contMDiff_southFiberAmbient (fun _ ↦ contDiff_southNormalEquations.contDiffAt)
    (fun q ↦ southNormalEquations_zero (southFiberPoint q) (first_southFiberPoint q))
    (fun q ↦ southNormalEquations_surjective (southFiberPoint q) (first_southFiberPoint q))
    southFiberAmbient_differential_injective southNormalDimensions q]
  change fderiv ℝ southNormalEquations (southFiberPoint q).val v = 0 ↔ _
  rw [southNormalEquations_kernel _ (first_southFiberPoint q), inner_quaternion_coordinates,
    first_southFiberPoint, inner_zero_left, zero_add]

theorem southRadialRotation_fixes_tangent (t : ℝ) (q : Sphere 3) (v : V 8)
    (hv : v ∈ (NormalFrameOfEquations.ambientDifferential
      (𝓡 3) southFiberAmbient q).range) : southRadialRotation t q v = v := by
  obtain ⟨hf, hx⟩ := (southFiberAmbient_tangent_iff q v).mp hv
  apply southRadialRotation_fixes t q v _ hx
  rw [sourcePole_inner, hf]
  rfl

theorem southRadialRotation_normal_iff (t : ℝ) (q : Sphere 3) (v : V 8) :
    southRadialRotation t q v ∈ (NormalFrameOfEquations.ambientDifferential
        (𝓡 3) southFiberAmbient q).rangeᗮ ↔
      v ∈ (NormalFrameOfEquations.ambientDifferential
        (𝓡 3) southFiberAmbient q).rangeᗮ := by
  have hinner (w : V 8)
      (hw : w ∈ (NormalFrameOfEquations.ambientDifferential
        (𝓡 3) southFiberAmbient q).range) :
      inner ℝ (southRadialRotation t q v) w = inner ℝ v w := by
    have h := (southRadialRotation t q).inner_map_map v w
    rw [southRadialRotation_fixes_tangent t q w hw] at h
    exact h
  simp only [Submodule.mem_orthogonal']
  constructor
  · intro h w hw
    rw [← hinner w hw]
    exact h w hw
  · intro h w hw
    rw [hinner w hw]
    exact h w hw

theorem southNormalFrame_range (q : Sphere 3) :
    (southNormalFrame.ambient q).range = (NormalFrameOfEquations.ambientDifferential
      (𝓡 3) southFiberAmbient q).rangeᗮ := by
  change (orthogonalRightInverse (fderiv ℝ southNormalEquations
    (southFiberPoint q).val)).range = _
  rw [range_orthogonalRightInverse _
    (southNormalEquations_surjective (southFiberPoint q) (first_southFiberPoint q))]
  exact congrArg (fun S : Submodule ℝ (V 8) ↦ Sᗮ)
    (NormalFrameOfEquations.range_ambientDifferential_eq_kernel
      contMDiff_southFiberAmbient (fun _ ↦ contDiff_southNormalEquations.contDiffAt)
      (fun q ↦ southNormalEquations_zero (southFiberPoint q) (first_southFiberPoint q))
      (fun q ↦ southNormalEquations_surjective (southFiberPoint q) (first_southFiberPoint q))
      southFiberAmbient_differential_injective southNormalDimensions q).symm

theorem contMDiff_southRadialRotation :
    ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 3)) 𝓘(ℝ, V 8 →L[ℝ] V 8) ∞
      (fun p : ℝ × Sphere 3 ↦
        (southRadialRotation p.1 p.2).toContinuousLinearEquiv.toContinuousLinearMap) :=
  contMDiff_localRotationOperator contMDiff_const contMDiff_southRadialSegment
    (fun p ↦ southRadialSegment_ne_zero p.1 p.2)
    (fun p ↦ pole_add_southRadialSegment_ne_zero p.1 p.2)

def southRadialFrame (t : ℝ) (q : Sphere 3) : SouthNormalModel →L[ℝ] V 8 :=
  (southRadialRotation t q).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (southNormalFrame.ambient q)

theorem southRadialFrame_injective (t : ℝ) (q : Sphere 3) :
    Function.Injective (southRadialFrame t q) :=
  (southRadialRotation t q).injective.comp (southNormalFrame.ambient_injective q)

theorem southRadialFrame_range (t : ℝ) (q : Sphere 3) :
    (southRadialFrame t q).range = (NormalFrameOfEquations.ambientDifferential
      (𝓡 3) southFiberAmbient q).rangeᗮ := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    apply (southRadialRotation_normal_iff t q _).mpr
    rw [← southNormalFrame_range]
    exact ⟨w, rfl⟩
  · intro hv
    have hi : (southRadialRotation t q).symm v ∈
        (NormalFrameOfEquations.ambientDifferential (𝓡 3) southFiberAmbient q).rangeᗮ := by
      apply (southRadialRotation_normal_iff t q _).mp
      simpa only [LinearIsometryEquiv.apply_symm_apply] using hv
    rw [← southNormalFrame_range] at hi
    obtain ⟨w, hw⟩ := hi
    change southNormalFrame.ambient q w = (southRadialRotation t q).symm v at hw
    refine ⟨w, ?_⟩
    change southRadialRotation t q (southNormalFrame.ambient q w) = v
    rw [hw, LinearIsometryEquiv.apply_symm_apply]

theorem contMDiff_southRadialFrame :
    ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 3)) 𝓘(ℝ, SouthNormalModel →L[ℝ] V 8) ∞
      (fun p : ℝ × Sphere 3 ↦ southRadialFrame p.1 p.2) :=
  contMDiff_southRadialRotation.clm_comp
    (southNormalFrame.contMDiff_ambient.comp contMDiff_snd)

theorem southRadialFrame_zero (q : Sphere 3) :
    southRadialFrame 0 q = southNormalFrame.ambient q := by
  rw [southRadialFrame, southRadialRotation_zero]
  rfl

theorem southRadialFrame_one (q : Sphere 3) (v : V 4) (u : ℝ) :
    letI := regularFiberAtlas sphereMap contMDiff_sphereMap south south_regular 3
      (by simp only [finrank_euclideanSpace_fin]);
    southRadialFrame 1 q
        (WithLp.toLp 2 ((2 : ℝ) * (-u), (2 : ℝ) • targetTailChartEquiv.symm v)) =
      StereographicEquator.lift 7 (southChartFrame.ambient (southFiberDiffeomorph q) v) +
        u • (spherePole 7).val := by
  let := regularFiberAtlas sphereMap contMDiff_sphereMap south south_regular 3
    (by simp only [finrank_euclideanSpace_fin])
  change southRadialRotation 1 q (southNormalFrame.ambient q _) = _
  rw [southRadialRotation_one]
  exact (stabilized_southChartFrame_comparison q v u).symm

def southRawNormalFrameMap : C(Sphere 3, SouthNormalModel →L[ℝ] V 8) :=
  ⟨southNormalFrame.ambient, southNormalFrame.contMDiff_ambient.continuous⟩

def southRotatedNormalFrameMap : C(Sphere 3, SouthNormalModel →L[ℝ] V 8) where
  toFun q := southRadialFrame 1 q
  continuous_toFun := by
    have h : Continuous (fun p : ℝ × Sphere 3 ↦ southRadialFrame p.1 p.2) :=
      contMDiff_southRadialFrame.continuous
    exact h.comp (f := fun q : Sphere 3 ↦ ((1 : ℝ), q))
      (continuous_const.prodMk continuous_id)

def southNormalFrameHomotopy : southRawNormalFrameMap.Homotopy southRotatedNormalFrameMap where
  toFun p := southRadialFrame (p.1 : ℝ) p.2
  continuous_toFun := by
    have h : Continuous (fun p : ℝ × Sphere 3 ↦ southRadialFrame p.1 p.2) :=
      contMDiff_southRadialFrame.continuous
    exact h.comp (f := fun p : I × Sphere 3 ↦ ((p.1 : ℝ), p.2))
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  map_zero_left q := southRadialFrame_zero q
  map_one_left _ := rfl

theorem southNormalFrameHomotopy_injective (t : I) (q : Sphere 3) :
    Function.Injective (southNormalFrameHomotopy (t, q)) :=
  southRadialFrame_injective t q

theorem southNormalFrameHomotopy_range (t : I) (q : Sphere 3) :
    (southNormalFrameHomotopy (t, q)).range =
      (NormalFrameOfEquations.ambientDifferential (𝓡 3) southFiberAmbient q).rangeᗮ :=
  southRadialFrame_range t q

end NoExoticSixSphere.QuaternionicHopf
