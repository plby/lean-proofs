import Wikipedia.NoExoticSixSphere.RankSixSphereSpinorLift
import Wikipedia.NoExoticSixSphere.RankSixSpinorNullhomotopy
import Wikipedia.NoExoticSixSphere.RankSixPfaffianSign

/-!
# Four-sphere families of rank-six complex structures are nullhomotopic

Lift the complex-line projection family to unit spinors, contract those
spinors on the actual seven-sphere, and apply the quadratic reconstruction.
The constant Pfaffian sign restores the original complex-structure family.
-/

namespace NoExoticSixSphere.OrthogonalComplexStructures

open RankSixComplexProjection RankSixSkewMatrix

theorem fourthSphere_nullhomotopic (J : C(Sphere 4, Space 6)) :
    ∃ K, J.Homotopic (ContinuousMap.const _ K) := by
  classical
  let : SimplyConnectedSpace (Sphere 4) := EuclideanSphere.simplyConnectedSpace 2
  let x₀ : Sphere 4 := Classical.choice (inferInstance : Nonempty (Sphere 4))
  let c : ℝ := -pfaffian (matrix (J x₀))
  have hc : c ^ 2 = 1 := by
    dsimp only [c]
    rw [neg_sq]
    exact pfaffian_sq_one _ (matrix_transpose _) (matrix_square _)
  obtain ⟨q, hq⟩ := exists_fourthSphere_unitSection J
  obtain ⟨r, ⟨H⟩⟩ := unitSpinor_family_nullhomotopic q
  have hstart (x : Sphere 4) : signScale c hc (fromSpinor (q x)) = J x := by
    apply matrix_injective
    rw [matrix_signScale, fromSpinor_recovers_of_fixed (J x) (q x) (hq x),
      pfaffian_constant J x x₀]
    change c • (c • matrix (J x)) = matrix (J x)
    rw [smul_smul, ← pow_two, hc, one_smul]
  refine ⟨signScale c hc (fromSpinor r), ⟨{
    toFun := fun p ↦ signScale c hc (fromSpinor (H p))
    continuous_toFun := (continuous_signScale c hc).comp
      (continuous_fromSpinor.comp H.continuous)
    map_zero_left := ?_
    map_one_left := ?_ }⟩⟩
  · intro x
    rw [H.apply_zero]
    exact hstart x
  · intro x
    change signScale c hc (fromSpinor (H (1, x))) = signScale c hc (fromSpinor r)
    rw [H.apply_one]
    rfl

end NoExoticSixSphere.OrthogonalComplexStructures
