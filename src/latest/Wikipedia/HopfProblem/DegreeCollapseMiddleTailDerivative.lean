import Wikipedia.HopfProblem.DegreeCollapseSmoothMiddleFamilies
import Wikipedia.NoExoticSixSphere.SphereThreeFramedDerivative

/-!
# The genuine tail differential at the critical source pole

The derivative of the original sphere inclusion has image the orthogonal
hyperplane. At the negative pole that hyperplane is exactly the zero-head
plane, so tail projection gives an isomorphism on the original tangent space.
-/

noncomputable section

open Set Function Metric Manifold
open scoped ContDiff RealInnerProductSpace
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.MiddleDuality

open NoExoticSixSphere.SphereThreeTangentFrame

theorem pole_inner (v : Hemisphere.Ambient 4) : inner ℝ middlePole.val v = -v 0 := by
  rw [PiLp.inner_apply, Fin.sum_univ_succ]
  simp [middlePole, Hemisphere.point, Hemisphere.vector, Hemisphere.radius]

theorem inclusionDerivative_pole_head (u : Hemisphere.Ambient 3) :
    inclusionDerivative middlePole u 0 = 0 := by
  have hm : inclusionDerivative middlePole u ∈ (ℝ ∙ middlePole.val)ᗮ := by
    rw [← range_inclusionDerivative]
    exact ⟨u, rfl⟩
  have hi := Submodule.mem_orthogonal_singleton_iff_inner_right.mp hm
  rw [pole_inner] at hi
  exact neg_eq_zero.mp hi

def tailDerivative : Hemisphere.Ambient 3 →L[ℝ] Hemisphere.Ambient 3 :=
  mfderiv (𝓡 3) 𝓘(ℝ, Hemisphere.Ambient 3) Hemisphere.tail middlePole

theorem tail_mfderiv : tailDerivative =
      (NoExoticSixSphere.SphereCylinder.tail 2).comp (inclusionDerivative middlePole) := by
  let _ : Fact (Module.finrank ℝ (Hemisphere.Ambient 4) = 3 + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  have hc : ContMDiff (𝓡 3) 𝓘(ℝ, Hemisphere.Ambient 4) ∞
      (fun x : Hemisphere.Sphere 3 => x.val) := contMDiff_coe_sphere
  have he : Hemisphere.tail =
      (fun x : Hemisphere.Sphere 3 => NoExoticSixSphere.SphereCylinder.tail 2 x.val) := by
    funext x
    ext i
    rfl
  change (mfderiv (𝓡 3) 𝓘(ℝ, Hemisphere.Ambient 3) Hemisphere.tail middlePole :
    Hemisphere.Ambient 3 →L[ℝ] Hemisphere.Ambient 3) = _
  rw [he]
  have hs : ContMDiff 𝓘(ℝ, Hemisphere.Ambient 4) 𝓘(ℝ, Hemisphere.Ambient 3) ∞
      (NoExoticSixSphere.SphereCylinder.tail 2) :=
    (NoExoticSixSphere.SphereCylinder.tail 2).contDiff.contMDiff
  have h := mfderiv_comp middlePole
    (hs.mdifferentiableAt (by simp))
    (hc.mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv, (NoExoticSixSphere.SphereCylinder.tail 2).fderiv] at h
  exact h

theorem tail_mfderiv_injective : Injective tailDerivative := by
  let _ : Fact (Module.finrank ℝ (Hemisphere.Ambient 4) = 3 + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  have hi : Injective (inclusionDerivative middlePole) := by
    convert! injective_mvfderiv_subtypeVal_sphere middlePole
  rw [tail_mfderiv]
  intro (u : Hemisphere.Ambient 3) (v : Hemisphere.Ambient 3) huv
  apply hi
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [inclusionDerivative_pole_head, inclusionDerivative_pole_head]
  · exact congrArg (fun w : Hemisphere.Ambient 3 => w j) huv

theorem tail_mfderiv_bijective : Bijective tailDerivative :=
  ⟨tail_mfderiv_injective, LinearMap.surjective_of_injective tail_mfderiv_injective⟩

def tailDifferential : Hemisphere.Ambient 3 ≃L[ℝ] Hemisphere.Ambient 3 :=
  (LinearEquiv.ofBijective tailDerivative.toLinearMap
      tail_mfderiv_bijective).toContinuousLinearEquiv

theorem tailDifferential_coe : tailDifferential.toContinuousLinearMap = tailDerivative := rfl

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.MiddleDuality
