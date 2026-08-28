import Wikipedia.HopfProblem.DegreeCollapseSmoothCappedMeridian

/-!
# Two-sphere tangent coordinates and composition at the original pole

The native inclusion identifies the pole tangent with the zero-head plane.
Tail projection is invertible. The general germ composition calculation
is kept separate from all Morse-chart data.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff RealInnerProductSpace
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.BeltMeridianSphere

def inclusionDerivative (x : Hemisphere.Sphere 2) :
    Hemisphere.Ambient 2 →L[ℝ] Hemisphere.Ambient 3 :=
  mfderiv (𝓡 2) 𝓘(ℝ, Hemisphere.Ambient 3) (fun y : Hemisphere.Sphere 2 => y.val) x

theorem range_inclusionDerivative (x : Hemisphere.Sphere 2) :
    (inclusionDerivative x).range = (ℝ ∙ x.val)ᗮ := by
  let _ : Fact (Module.finrank ℝ (Hemisphere.Ambient 3) = 2 + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  change (mfderiv (𝓡 2) 𝓘(ℝ, Hemisphere.Ambient 3)
    (fun y : Hemisphere.Sphere 2 => y.val) x).range = _
  convert! range_mvfderiv_subtypeVal x

theorem pole_inner (v : Hemisphere.Ambient 3) : inner ℝ pole.val v = -v 0 := by
  rw [PiLp.inner_apply, Fin.sum_univ_succ]
  simp [pole, Hemisphere.point, Hemisphere.vector, Hemisphere.radius]

theorem inclusionDerivative_pole_head (u : Hemisphere.Ambient 2) :
    inclusionDerivative pole u 0 = 0 := by
  have hm : inclusionDerivative pole u ∈ (ℝ ∙ pole.val)ᗮ := by
    rw [← range_inclusionDerivative]
    exact ⟨u, rfl⟩
  have hi := Submodule.mem_orthogonal_singleton_iff_inner_right.mp hm
  rw [pole_inner] at hi
  exact neg_eq_zero.mp hi

def tailDerivative : Hemisphere.Ambient 2 →L[ℝ] Hemisphere.Ambient 2 :=
  mfderiv (𝓡 2) 𝓘(ℝ, Hemisphere.Ambient 2) Hemisphere.tail pole

theorem tail_mfderiv : tailDerivative =
    (NoExoticSixSphere.SphereCylinder.tail 1).comp (inclusionDerivative pole) := by
  let _ : Fact (Module.finrank ℝ (Hemisphere.Ambient 3) = 2 + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  have hc : ContMDiff (𝓡 2) 𝓘(ℝ, Hemisphere.Ambient 3) ∞
      (fun x : Hemisphere.Sphere 2 => x.val) := contMDiff_coe_sphere
  have he : Hemisphere.tail =
      (fun x : Hemisphere.Sphere 2 => NoExoticSixSphere.SphereCylinder.tail 1 x.val) := by
    funext x
    ext i
    rfl
  change (mfderiv (𝓡 2) 𝓘(ℝ, Hemisphere.Ambient 2) Hemisphere.tail pole :
    Hemisphere.Ambient 2 →L[ℝ] Hemisphere.Ambient 2) = _
  rw [he]
  have hs : ContMDiff 𝓘(ℝ, Hemisphere.Ambient 3) 𝓘(ℝ, Hemisphere.Ambient 2) ∞
      (NoExoticSixSphere.SphereCylinder.tail 1) :=
    (NoExoticSixSphere.SphereCylinder.tail 1).contDiff.contMDiff
  have h := mfderiv_comp pole (hs.mdifferentiableAt (by simp)) (hc.mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv, (NoExoticSixSphere.SphereCylinder.tail 1).fderiv] at h
  exact h

theorem tail_mfderiv_injective : Injective tailDerivative := by
  let _ : Fact (Module.finrank ℝ (Hemisphere.Ambient 3) = 2 + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  have hi : Injective (inclusionDerivative pole) := by
    convert! injective_mvfderiv_subtypeVal_sphere pole
  rw [tail_mfderiv]
  intro (u : Hemisphere.Ambient 2) (v : Hemisphere.Ambient 2) huv
  apply hi
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [inclusionDerivative_pole_head, inclusionDerivative_pole_head]
  · exact congrArg (fun w : Hemisphere.Ambient 2 => w j) huv

theorem tail_mfderiv_bijective : Bijective tailDerivative :=
  ⟨tail_mfderiv_injective, LinearMap.surjective_of_injective tail_mfderiv_injective⟩

theorem tail_pole : Hemisphere.tail pole = (0 : Hemisphere.Ambient 2) := by
  ext i
  simp [pole, Hemisphere.tail, Hemisphere.point, Hemisphere.vector]

theorem linear_tail_mfderiv {N : Type*} [NormedAddCommGroup N] [InnerProductSpace ℝ N]
    (L : Hemisphere.Ambient 2 ≃ₗᵢ[ℝ] N) :
    (mfderiv (𝓡 2) 𝓘(ℝ, N) (fun x : Hemisphere.Sphere 2 => L (Hemisphere.tail x)) pole :
      Hemisphere.Ambient 2 →L[ℝ] N) =
      L.toContinuousLinearEquiv.toContinuousLinearMap.comp tailDerivative := by
  have hL : ContMDiff 𝓘(ℝ, Hemisphere.Ambient 2) 𝓘(ℝ, N) ∞
      L.toContinuousLinearEquiv.toContinuousLinearMap :=
    L.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.contMDiff
  change mfderiv (𝓡 2) 𝓘(ℝ, N)
    (L.toContinuousLinearEquiv.toContinuousLinearMap ∘ Hemisphere.tail) pole = _
  rw [mfderiv_comp pole (hL.mdifferentiableAt (by simp))
    (smooth_tail.mdifferentiableAt (by simp)), mfderiv_eq_fderiv,
    L.toContinuousLinearEquiv.toContinuousLinearMap.fderiv]
  rfl

theorem surjective_coprod_comp {U V W Z : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (A : V →L[ℝ] Z) (B : W →L[ℝ] Z) (T : U →L[ℝ] V)
    (hAB : Surjective (A.coprod B)) (hT : Surjective T) :
    Surjective ((A.comp T).coprod B) := by
  intro z
  obtain ⟨⟨u, w⟩, huw⟩ := hAB z
  obtain ⟨a, ha⟩ := hT u
  refine ⟨(a, w), ?_⟩
  change A (T a) + B w = z
  rw [ha]
  exact huw

theorem pole_germ_comp_derivative
    {N G X : Type*} [NormedAddCommGroup N] [InnerProductSpace ℝ N]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace X] [ChartedSpace G X]
    (L : Hemisphere.Ambient 2 ≃ₗᵢ[ℝ] N) (g : N → X)
    (hg : ContMDiff 𝓘(ℝ, N) 𝓘(ℝ, G) ∞ g) (γ : Hemisphere.Sphere 2 → X)
    (hγ : γ =ᶠ[𝓝 pole] (fun x => g (L (Hemisphere.tail x)))) :
    (mfderiv (𝓡 2) 𝓘(ℝ, G) γ pole : Hemisphere.Ambient 2 →L[ℝ] G) =
      (mfderiv 𝓘(ℝ, N) 𝓘(ℝ, G) g 0).comp
        (L.toContinuousLinearEquiv.toContinuousLinearMap.comp tailDerivative) := by
  let R : Hemisphere.Sphere 2 → N := fun x => L (Hemisphere.tail x)
  have hR : ContMDiff (𝓡 2) 𝓘(ℝ, N) ∞ R := L.contDiff.contMDiff.comp smooth_tail
  have hRzero : R pole = 0 := by
    change L (Hemisphere.tail pole) = 0
    rw [tail_pole, map_zero]
  have hRT : mfderiv (𝓡 2) 𝓘(ℝ, N) R pole =
      L.toContinuousLinearEquiv.toContinuousLinearMap.comp tailDerivative := linear_tail_mfderiv L
  rw [hγ.mfderiv_eq]
  change mfderiv (𝓡 2) 𝓘(ℝ, G) (g ∘ R) pole = _
  rw [mfderiv_comp pole (hg.mdifferentiableAt (by simp))
    (hR.mdifferentiableAt (by simp)), hRzero, hRT]
  rfl

theorem injective_transverse_of_comp
    {U V W Z : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (F : U →L[ℝ] Z) (A : V →L[ℝ] Z) (B : W →L[ℝ] Z) (T : U →L[ℝ] V)
    (hF : F = A.comp T) (hA : Injective A) (hAB : Surjective (A.coprod B))
    (hTi : Injective T) (hTs : Surjective T) :
    Injective F ∧ Surjective (F.coprod B) := by
  rw [hF]
  exact ⟨hA.comp hTi, surjective_coprod_comp A B T hAB hTs⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.BeltMeridianSphere
