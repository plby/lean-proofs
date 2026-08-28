import Wikipedia.NoExoticSixSphere.QuaternionCommutatorNativeSphere

/-!
# The antipodal fiber of the original native seven-sphere representative

The unique-fiber calculation now concerns the actual descended map on
the standard seven-sphere, not just its interval-product presentation.
-/

noncomputable section

open scoped unitInterval

namespace NoExoticSixSphere.QuaternionCommutatorNativeSphere

open Wikipedia.HopfProblem.UnitQuaternionSphere
open Wikipedia.HomotopyGroupsOfSpheres.QuaternionicFibration
open QuaternionCommutatorBoundaryLift QuaternionCommutatorAntipodal CubeFirstCoordinate

local notation "south" => QuaternionCommutatorAntipodal.antipode
local notation "halfTime" => QuaternionCommutatorAntipodal.midpoint

theorem minusOne_ne_one : (-1 : UnitQuaternions) ≠ 1 := by
  intro h
  have hh := congrArg (fun q : UnitQuaternions ↦ q.val.re) h
  change (-1 : ℝ) = 1 at hh
  norm_num at hh

theorem quaternionCube_neg_one_injective (u v : Fin 3 → I)
    (hu : quaternionCube u = -1) (hv : quaternionCube v = -1) : u = v := by
  have he : SmoothCube.quotient 3 u = SmoothCube.quotient 3 v :=
    sphereHomeomorph.symm.injective (hu.trans hv.symm)
  rcases (SmoothCube.quotient_eq_iff 3 u v).mp he with h | h
  · exact h
  · exact False.elim (minusOne_ne_one (hu.symm.trans (quaternionCube.property u h.1)))

theorem symm_midpoint : unitInterval.symm halfTime = halfTime := by
  apply Subtype.ext
  change (1 - (1 / 2 : ℝ)) = 1 / 2
  norm_num

theorem symm_eq_midpoint_iff (t : I) : unitInterval.symm t = halfTime ↔ t = halfTime := by
  constructor
  · intro h
    have hh := congrArg unitInterval.symm h
    simpa only [unitInterval.symm_symm, symm_midpoint] using hh
  · rintro rfl
    exact symm_midpoint

theorem sevenLoop_antipode_iff (u : Fin 7 → I) :
    sevenLoop u = south ↔ (split 6 u).1 = halfTime ∧
      (cubePair quaternionCube quaternionCube (split 6 u).2).1 = -1 ∧
      (cubePair quaternionCube quaternionCube (split 6 u).2).2 = -1 := by
  change projection (QuaternionCommutatorRotation.contraction (unitInterval.symm (split 6 u).1)
    (cubePair quaternionCube quaternionCube (split 6 u).2).1
    (cubePair quaternionCube quaternionCube (split 6 u).2).2) = south ↔ _
  rw [contraction_antipode_iff, symm_eq_midpoint_iff]

theorem sevenLoop_antipode_injective (u v : Fin 7 → I)
    (hu : sevenLoop u = south) (hv : sevenLoop v = south) : u = v := by
  obtain ⟨hu₀, hu₁, hu₂⟩ := (sevenLoop_antipode_iff u).mp hu
  obtain ⟨hv₀, hv₁, hv₂⟩ := (sevenLoop_antipode_iff v).mp hv
  have hl := quaternionCube_neg_one_injective _ _ hu₁ hv₁
  have hr := quaternionCube_neg_one_injective _ _ hu₂ hv₂
  have ht : (split 6 u).2 = (split 6 v).2 := by
    funext i
    obtain ⟨j, rfl⟩ := blockCoordinates.surjective i
    cases j with
    | inl j => exact congrFun hl j
    | inr j => exact congrFun hr j
  have hsplit : split 6 u = split 6 v := Prod.ext (hu₀.trans hv₀.symm) ht
  exact (join_split 6 u).symm.trans ((congrArg (join 6) hsplit).trans (join_split 6 v))

def antipodalCube : Fin 3 → I := Classical.choose (quaternionCube_surjective (-1))

theorem antipodalCube_value : quaternionCube antipodalCube = -1 :=
  Classical.choose_spec (quaternionCube_surjective (-1))

def antipodalSixCube (i : Fin 6) : I :=
  Sum.elim antipodalCube antipodalCube (blockCoordinates.symm i)

theorem antipodal_leftBlock :
    (fun i : Fin 3 ↦ antipodalSixCube (blockCoordinates (Sum.inl i))) = antipodalCube := by
  funext i
  simp only [antipodalSixCube, Equiv.symm_apply_apply, Sum.elim_inl]

theorem antipodal_rightBlock :
    (fun i : Fin 3 ↦ antipodalSixCube (blockCoordinates (Sum.inr i))) = antipodalCube := by
  funext i
  simp only [antipodalSixCube, Equiv.symm_apply_apply, Sum.elim_inr]

theorem antipodalSixCube_pair :
    cubePair quaternionCube quaternionCube antipodalSixCube = (-1, -1) := by
  apply Prod.ext
  · change quaternionCube (fun i ↦ antipodalSixCube (blockCoordinates (Sum.inl i))) = -1
    rw [antipodal_leftBlock, antipodalCube_value]
  · change quaternionCube (fun i ↦ antipodalSixCube (blockCoordinates (Sum.inr i))) = -1
    rw [antipodal_rightBlock, antipodalCube_value]

def antipodalSevenCube : Fin 7 → I := join 6 (halfTime, antipodalSixCube)

theorem antipodalSevenCube_value : sevenLoop antipodalSevenCube = south := by
  apply (sevenLoop_antipode_iff _).mpr
  exact ⟨rfl, congrArg Prod.fst antipodalSixCube_pair, congrArg Prod.snd antipodalSixCube_pair⟩

theorem sphereMap_unique_antipodal_fiber : ∃! x : Sphere 7, sphereMap x = south := by
  refine ⟨SmoothCube.quotient 7 antipodalSevenCube,
    (sphereMap_quotient _).trans antipodalSevenCube_value, ?_⟩
  intro x hx
  obtain ⟨u, rfl⟩ := SmoothCube.quotient_surjective (by decide : 0 < 7) x
  have hu : sevenLoop u = south := (sphereMap_quotient u).symm.trans hx
  exact congrArg (SmoothCube.quotient 7)
    (sevenLoop_antipode_injective u antipodalSevenCube hu antipodalSevenCube_value)

end NoExoticSixSphere.QuaternionCommutatorNativeSphere
