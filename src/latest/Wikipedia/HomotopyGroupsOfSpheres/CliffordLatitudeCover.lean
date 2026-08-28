import Wikipedia.HomotopyGroupsOfSpheres.CliffordSphereCoordinates
import Wikipedia.HomotopyGroupsOfSpheres.LatitudeDescent
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! # The explicit Clifford latitudes cover the entire parameter sphere -/

noncomputable section

open scoped Matrix unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian

open Wikipedia.HopfProblem.SphereHomology

theorem latitude_height_cos (t : I) :
    Real.cos (Real.arccos (Latitude.height t)) = Latitude.height t := by
  apply Real.cos_arccos <;> nlinarith [Latitude.height_sq_le_one t]

theorem latitude_radius_sin (t : I) :
    Real.sin (Real.arccos (Latitude.height t)) = Latitude.radius t := Real.sin_arccos _

theorem coordinateSphereHomeomorph_latitude (t : I) (v : UnitSphere) :
    coordinateSphereHomeomorph (Latitude.point 4 t v) =
      latitudePoint (Real.arccos (Latitude.height t)) v := by
  apply Subtype.ext
  apply PiLp.ext
  intro i
  change ofRealCoordinates (Latitude.vector 4 t v) i =
    latitudeVector (Real.arccos (Latitude.height t)) v.val i
  fin_cases i <;> apply Complex.ext <;>
    norm_num [ofRealCoordinates, Latitude.vector, latitudeVector, Matrix.cons_val_two,
      latitude_height_cos, latitude_radius_sin, Complex.mul_re, Complex.mul_im,
      -Complex.ofReal_cos, -Complex.ofReal_sin] <;> rfl

theorem latitudePoint_surjective (z : ComplexCrossProductUnitary.UnitSphere) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ Real.pi ∧ ∃ v : UnitSphere, latitudePoint θ v = z := by
  obtain ⟨⟨t, v⟩, h⟩ := Latitude.point_surjective 4 (coordinateSphereHomeomorph.symm z)
  change Latitude.point 4 t v = coordinateSphereHomeomorph.symm z at h
  refine ⟨Real.arccos (Latitude.height t), Real.arccos_nonneg _, Real.arccos_le_pi _, v, ?_⟩
  rw [← coordinateSphereHomeomorph_latitude, h, Homeomorph.apply_symm_apply]

end Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian
