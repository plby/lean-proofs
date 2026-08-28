import Wikipedia.NoExoticSixSphere.PartialFrameCenterSection
import Wikipedia.NoExoticSixSphere.PartialFrameThirdGroup
import Wikipedia.NoExoticSixSphere.PartialFrameSplitStability
import Wikipedia.HopfProblem.CuspCentralHomologyAttachingCrossNull

/-!
# A generator of the actual one-column fiber has nonzero frame parity

The south fiber inclusion is the second summand of the genuine
Mayer–Vietoris presentation. Its third homology map is integer reduction
modulo two. Thus any homeomorphic parameterization of this sphere fiber
has parity one, also in arbitrary orthonormal splitting coordinates.
-/

noncomputable section

namespace NoExoticSixSphere.Stiefel.ColumnHomology

open GLOrthonormalization
open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.PeriodTorusHigherHomology
open Wikipedia.HopfProblem.CuspCentralHomology

variable (v : UnitSphere (Vector 2))

theorem integerQuotientParityEquiv_mk (p : ℤ × ℤ) :
    integerQuotientParityEquiv v (Submodule.Quotient.mk p) = parityProjection v p := by
  simp only [integerQuotientParityEquiv, LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]

theorem thirdHomologyEquivZModTwo_reducedRightMap (b : ℤ × ℤ) :
    thirdHomologyEquivZModTwo v
      (reducedRightMap 3 v 3 (pairThirdHomologyEquiv.symm b)) = parityProjection v b := by
  rw [← integerThirdHomologyPresentation_mk]
  change integerQuotientParityEquiv v
    ((integerThirdHomologyPresentation v).symm
      (integerThirdHomologyPresentation v (Submodule.Quotient.mk b))) = _
  rw [LinearEquiv.symm_apply_apply, integerQuotientParityEquiv_mk]

theorem thirdHomologyEquivZModTwo_southFiber (b : SingularHomology (Space 4 1) 3) :
    thirdHomologyEquivZModTwo v
      (singularHomologyMap (ColumnFiber.reconstructionMap v (antipode (spherePole 4)))
        3 b) = (fiberThirdHomologyEquiv b : ZMod 2) := by
  rw [← reducedRightMap_south]
  have hp : pairThirdHomologyEquiv.symm (0, fiberThirdHomologyEquiv b) = (0, b) := by
    change (fiberThirdHomologyEquiv.symm 0,
      fiberThirdHomologyEquiv.symm (fiberThirdHomologyEquiv b)) = (0, b)
    rw [map_zero, LinearEquiv.symm_apply_apply]
  rw [← hp, thirdHomologyEquivZModTwo_reducedRightMap, parityProjection_apply]
  simp only [map_zero, add_zero]

theorem southFiber_homology_ne_zero :
    singularHomologyMap (ColumnFiber.reconstructionMap v (antipode (spherePole 4)))
      3 ≠ 0 := by
  intro hz
  have h := thirdHomologyEquivZModTwo_southFiber v (fiberThirdHomologyEquiv.symm 1)
  rw [hz, LinearMap.zero_apply, map_zero, LinearEquiv.apply_symm_apply] at h
  norm_num at h

theorem southFiber_sphere_homology_ne_zero (e : Sphere 3 ≃ₜ Space 4 1) :
    singularHomologyMap
      ((ColumnFiber.reconstructionMap v (antipode (spherePole 4))).comp
        (e : C(Sphere 3, Space 4 1)))
      3 ≠ 0 := by
  intro hz
  apply southFiber_homology_ne_zero v
  apply LinearMap.ext
  intro b
  obtain ⟨a, ha⟩ := (homeomorphHomologyEquiv e 3).surjective b
  have h := LinearMap.congr_fun hz a
  rw [singularHomologyMap_comp] at h
  change singularHomologyMap (ColumnFiber.reconstructionMap v (antipode (spherePole 4)))
    3 (homeomorphHomologyEquiv e 3 a) = 0 at h
  rw [ha] at h
  exact h

theorem southFiber_sphere_parity (e : Sphere 3 ≃ₜ Space 4 1) :
    sphereThirdObstruction 0
      ((ColumnFiber.reconstructionMap v (antipode (spherePole 4))).comp (e : C(_, _))) =
      1 := by
  have hn : sphereThirdObstruction 0
      ((ColumnFiber.reconstructionMap v (antipode (spherePole 4))).comp (e : C(_, _))) ≠
      0 := by
    intro hz
    obtain ⟨H⟩ := (sphereThirdObstruction_zero_iff 0 _).mp hz
    apply southFiber_sphere_homology_ne_zero v e
    exact singularHomologyMap_eq_zero_of_nullhomotopic _
      ⟨_, ⟨H.toHomotopy⟩⟩ 3 (by decide)
  apply zmodTwo_eq_of_zero_iff
  exact iff_of_false hn (by decide)

end NoExoticSixSphere.Stiefel.ColumnHomology

namespace NoExoticSixSphere.Stiefel.SplitReconstruction

open GLOrthonormalization

attribute [local instance] vectorDimension

theorem oneColumn_sphere_parity
    (S : Vector 2 ≃ₗᵢ[ℝ] WithLp 2 (ℝ × Vector 1))
    (T : Vector 5 ≃ₗᵢ[ℝ] WithLp 2 (ℝ × Vector 4))
    (e : Sphere 3 ≃ₜ Space 4 1) :
    sphereThirdObstruction 0 ((map S T).comp (e : C(_, _))) = 1 := by
  let v := spherePole 1
  let c := antipode (spherePole 4)
  let U := (ColumnCoordinates.split (r := 4) c).trans T.symm
  let V := S.trans (ColumnCoordinates.split (r := 1) v).symm
  let h := FrameCoordinates.homeomorph U V
  have he : (map S T).comp (e : C(Sphere 3, Space 4 1)) =
      (h : C(_, _)).comp ((ColumnFiber.reconstructionMap v c).comp
        (e : C(Sphere 3, Space 4 1))) := by
    apply ContinuousMap.ext
    intro s
    exact reconstruct_eq_coordinates S T v c (e s)
  rw [he, sphereThirdObstruction_homeomorph]
  exact ColumnHomology.southFiber_sphere_parity v e

end NoExoticSixSphere.Stiefel.SplitReconstruction
