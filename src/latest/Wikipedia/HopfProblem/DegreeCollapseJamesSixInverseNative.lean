import Wikipedia.HopfProblem.DegreeCollapseJamesSixInverseCoordinates
import Wikipedia.HopfProblem.DegreeCollapseSphereSelfMapSurjectivity
import Wikipedia.NoExoticSixSphere.JamesSphereSecondStageHomotopyRange

/-!
# The original second-stage collapse has involutive image in degree twelve

The original second-stage inclusion reflects native classes in this
degree. Reflected word reversal therefore inverts its native classes.
But its exact collapse coordinate map is based homotopic to the
identity on S12. The collapse class must equal its own inverse.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.JamesSixInverseNative

open NoExoticSixSphere JamesSphere JamesSixInverseCoordinates

theorem targetTwist_native (d : ℕ) (c : π_ d (Sphere 12) (spherePole 12)) :
    HigherHomotopy.map (N := Fin d) targetTwist targetTwist_pole c = c := by
  obtain ⟨H⟩ := targetTwist_homotopic_id
  exact (HigherHomotopy.map_eq_of_based_homotopy targetTwist
    (ContinuousMap.id (Sphere 12)) targetTwist_pole rfl H c).trans
      (SphereSelfMapSurjectivity.native_map_id c)

theorem stageInverse_native
    (c : π_ 12 (SecondStage.Space 6) (SecondStage.basepoint 6)) :
    HigherHomotopy.map (N := Fin 12) stageInverse stageInverse_basepoint c = c⁻¹ := by
  let F := HigherHomotopy.mapMonoidHom (N := Fin 12)
    (SecondStage.wordInclusion 6) (y := SecondStage.basepoint 6) rfl
  apply (SecondStage.wordInclusion_pi_bijective 6 (by decide) 12
    (by decide) (by decide) (SecondStage.basepoint 6)).injective
  change F (HigherHomotopy.map (N := Fin 12) stageInverse stageInverse_basepoint c) = F c⁻¹
  rw [map_inv]
  have h₁ := HigherHomotopy.map_comp stageInverse stageInverse_basepoint
    (SecondStage.wordInclusion 6) rfl c
  have h₂ := HigherHomotopy.map_comp (SecondStage.wordInclusion 6) rfl
    (JamesInverseAction.inverseWords 6 (by decide) 0)
    (JamesInverseAction.inverseWords_one 6 (by decide) 0) c
  exact h₁.trans (h₂.symm.trans
    (JamesInverseAction.inverseWords_native 6 (by decide) 0 12 (F c)))

theorem collapse_stage_inverse
    (c : π_ 12 (SecondStage.Space 6) (SecondStage.basepoint 6)) :
    HigherHomotopy.map (N := Fin 12) (SecondStage.collapse 6)
      (SecondStage.collapse_basepoint 6)
      (HigherHomotopy.map (N := Fin 12) stageInverse stageInverse_basepoint c) =
    HigherHomotopy.map (N := Fin 12) (SecondStage.collapse 6)
      (SecondStage.collapse_basepoint 6) c := by
  have he : (SecondStage.collapse 6).comp stageInverse =
      targetTwist.comp (SecondStage.collapse 6) := by
    apply ContinuousMap.ext
    exact collapse_inverse
  have h₁ := HigherHomotopy.map_comp stageInverse stageInverse_basepoint
    (SecondStage.collapse 6) (SecondStage.collapse_basepoint 6) c
  have h₂ := HigherHomotopy.map_comp (SecondStage.collapse 6)
    (SecondStage.collapse_basepoint 6) targetTwist targetTwist_pole c
  have H : ((SecondStage.collapse 6).comp stageInverse).HomotopyRel
      (targetTwist.comp (SecondStage.collapse 6)) {SecondStage.basepoint 6} :=
    (ContinuousMap.HomotopyRel.refl ((SecondStage.collapse 6).comp stageInverse)
      {SecondStage.basepoint 6}).cast rfl he
  have hmid := HigherHomotopy.map_eq_of_based_homotopy
    ((SecondStage.collapse 6).comp stageInverse) (targetTwist.comp (SecondStage.collapse 6))
    ((congrArg (SecondStage.collapse 6) stageInverse_basepoint).trans
      (SecondStage.collapse_basepoint 6))
    ((congrArg targetTwist (SecondStage.collapse_basepoint 6)).trans targetTwist_pole) H c
  exact h₁.trans (hmid.trans (h₂.symm.trans (targetTwist_native 12 _)))

theorem collapse_eq_inv
    (c : π_ 12 (SecondStage.Space 6) (SecondStage.basepoint 6)) :
    HigherHomotopy.map (N := Fin 12) (SecondStage.collapse 6)
      (SecondStage.collapse_basepoint 6) c =
    (HigherHomotopy.map (N := Fin 12) (SecondStage.collapse 6)
      (SecondStage.collapse_basepoint 6) c)⁻¹ := by
  have h := collapse_stage_inverse c
  rw [stageInverse_native] at h
  let F := HigherHomotopy.mapMonoidHom (N := Fin 12)
    (SecondStage.collapse 6) (SecondStage.collapse_basepoint 6)
  change F c⁻¹ = F c at h
  rw [map_inv] at h
  exact h.symm

end Wikipedia.HopfProblem.DegreeCollapse.JamesSixInverseNative
