import Wikipedia.NoExoticSixSphere.RankSixUnitSpinor
import Wikipedia.NoExoticSixSphere.EquatorDimension
import Wikipedia.NoExoticSixSphere.SphereConnectivity

/-!
# Contracting unit-spinor families on the four-sphere

The actual unit sphere of complex four-space is identified isometrically
with the standard real seven-sphere. The checked sphere-connectivity theorem
then contracts every continuous family parametrized by the four-sphere.
-/

namespace NoExoticSixSphere.RankSixComplexProjection

theorem spinor_finrank_real : Module.finrank ℝ Spinor = 8 := by
  rw [finrank_real_of_complex, finrank_euclideanSpace_fin]

noncomputable def spinorCoordinates : Spinor ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 8) :=
  ((stdOrthonormalBasis ℝ Spinor).reindex (finCongr spinor_finrank_real)).repr

noncomputable def unitSpinorHomeomorph : UnitSpinor ≃ₜ Sphere 7 :=
  unitSphereCongr spinorCoordinates

theorem unitSpinor_family_nullhomotopic (q : C(Sphere 4, UnitSpinor)) :
    ∃ r, q.Homotopic (ContinuousMap.const _ r) := by
  let e := unitSpinorHomeomorph
  let q' : C(Sphere 4, Sphere 7) := ⟨fun x ↦ e (q x), e.continuous.comp q.continuous⟩
  obtain ⟨r, ⟨H⟩⟩ := sphere_sphere_nullhomotopic (by decide : 4 < 7) q'
  refine ⟨e.symm r, ⟨{
    toFun := fun p ↦ e.symm (H p)
    continuous_toFun := e.symm.continuous.comp H.continuous
    map_zero_left := ?_
    map_one_left := ?_ }⟩⟩
  · intro x
    rw [H.apply_zero]
    exact e.symm_apply_apply (q x)
  · intro x
    change e.symm (H (1, x)) = e.symm r
    rw [H.apply_one]
    rfl

end NoExoticSixSphere.RankSixComplexProjection
