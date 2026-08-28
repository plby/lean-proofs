import Wikipedia.HopfProblem.DegreeCollapseTwoSphereGermComposition
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Native two-sphere coordinates and an actual protected pole cutoff

Tail projection is injective on the negative hemisphere and has injective
native derivative wherever the head coordinate is nonzero. The constructed
nonnegative cutoff vanishes on a closed cap strictly inside the retained
meridian cap. A larger compact complement excludes the pole and contains
every point where the perturbation can move the original sphere.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff RealInnerProductSpace
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.BeltMeridianSphere

theorem tail_injective_negative : InjOn (Hemisphere.tail (n := 2)) negativeHemisphere := by
  intro x hx y hy hxy
  have hd : Hemisphere.disk x = Hemisphere.disk y := Subtype.ext hxy
  exact (Hemisphere.point_disk_of_nonpos x hx.le).symm.trans
    ((congrArg (Hemisphere.point false) hd).trans (Hemisphere.point_disk_of_nonpos y hy.le))

theorem tail_mfderiv_at (x : Hemisphere.Sphere 2) :
    (mfderiv (𝓡 2) 𝓘(ℝ, Hemisphere.Ambient 2) Hemisphere.tail x :
      Hemisphere.Ambient 2 →L[ℝ] Hemisphere.Ambient 2) =
      (NoExoticSixSphere.SphereCylinder.tail 1).comp (inclusionDerivative x) := by
  let _ : Fact (Module.finrank ℝ (Hemisphere.Ambient 3) = 2 + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  have hc : ContMDiff (𝓡 2) 𝓘(ℝ, Hemisphere.Ambient 3) ∞
      (fun y : Hemisphere.Sphere 2 => y.val) := contMDiff_coe_sphere
  have he : Hemisphere.tail =
      (fun y : Hemisphere.Sphere 2 => NoExoticSixSphere.SphereCylinder.tail 1 y.val) := by
    funext y
    ext i
    rfl
  rw [he]
  have hs : ContMDiff 𝓘(ℝ, Hemisphere.Ambient 3) 𝓘(ℝ, Hemisphere.Ambient 2) ∞
      (NoExoticSixSphere.SphereCylinder.tail 1) :=
    (NoExoticSixSphere.SphereCylinder.tail 1).contDiff.contMDiff
  have h := mfderiv_comp x (hs.mdifferentiableAt (by simp)) (hc.mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv, (NoExoticSixSphere.SphereCylinder.tail 1).fderiv] at h
  exact h

theorem tail_mfderiv_injective_of_head_ne_zero (x : Hemisphere.Sphere 2) (hx : x.val 0 ≠ 0) :
    Injective (mfderiv (𝓡 2) 𝓘(ℝ, Hemisphere.Ambient 2) Hemisphere.tail x) := by
  let _ : Fact (Module.finrank ℝ (Hemisphere.Ambient 3) = 2 + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  have hi : Injective (inclusionDerivative x) := by
    convert! injective_mvfderiv_subtypeVal_sphere x
  apply (injective_iff_map_eq_zero _).mpr
  intro u hu
  rw [tail_mfderiv_at] at hu
  let v := inclusionDerivative x u
  have ht : NoExoticSixSphere.SphereCylinder.tail 1 v = 0 := hu
  have htail (j : Fin 2) : v j.succ = 0 := congrArg (fun w : Hemisphere.Ambient 2 => w j) ht
  have hm : v ∈ (ℝ ∙ x.val)ᗮ := by
    rw [← range_inclusionDerivative]
    exact ⟨u, rfl⟩
  have hinner := Submodule.mem_orthogonal_singleton_iff_inner_right.mp hm
  have hprod : x.val 0 * v 0 = 0 := by
    simpa [PiLp.inner_apply, Fin.sum_univ_succ, htail, mul_comm] using hinner
  have hhead : v 0 = 0 := (mul_eq_zero.mp hprod).resolve_left hx
  have hv : v = 0 := by
    ext i
    exact Fin.cases hhead (fun j => htail j) i
  exact hi (hv.trans (map_zero (inclusionDerivative x)).symm)

theorem smooth_head : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞
    (fun x : Hemisphere.Sphere 2 => x.val 0) := by
  let _ : Fact (Module.finrank ℝ (Hemisphere.Ambient 3) = 2 + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let H : Hemisphere.Ambient 3 →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ (Hemisphere.Ambient 2)).comp
      (NoExoticSixSphere.SphereCylinder.join 1).symm.toContinuousLinearMap
  exact H.contDiff.contMDiff.comp (contMDiff_coe_sphere (n := 2))

def poleCutoff (x : Hemisphere.Sphere 2) : ℝ := Real.smoothTransition (4 * x.val 0 + 3)

theorem poleCutoff_smooth : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ poleCutoff :=
  Real.smoothTransition.contDiff.contMDiff.comp
    ((contMDiff_const.mul smooth_head).add contMDiff_const)

theorem poleCutoff_nonneg (x : Hemisphere.Sphere 2) : 0 ≤ poleCutoff x :=
  Real.smoothTransition.nonneg _

theorem poleCutoff_norm_le_one (x : Hemisphere.Sphere 2) : ‖poleCutoff x‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (poleCutoff_nonneg x)]
  exact Real.smoothTransition.le_one _

theorem poleCutoff_zero_iff (x : Hemisphere.Sphere 2) :
    poleCutoff x = 0 ↔ x.val 0 ≤ -(3 / 4 : ℝ) := by
  rw [poleCutoff, Real.smoothTransition.zero_iff_nonpos]
  constructor <;> intro h <;> linarith

theorem poleCutoff_zero_mem_nhds : {x | poleCutoff x = 0} ∈ 𝓝 pole := by
  apply mem_of_superset (innerPoleCap_open.mem_nhds pole_mem_inner)
  intro x hx
  exact (poleCutoff_zero_iff x).mpr hx.le

def awayPoleCap : Set (Hemisphere.Sphere 2) := {x | -(7 / 8 : ℝ) ≤ x.val 0}

theorem awayPoleCap_compact : IsCompact awayPoleCap :=
  (isClosed_le continuous_const smooth_head.continuous).isCompact

theorem pole_not_mem_awayPoleCap : pole ∉ awayPoleCap := by
  change ¬(-(7 / 8 : ℝ) ≤ -Hemisphere.radius (⟨0, by simp⟩ : Hemisphere.Ball 2))
  norm_num [Hemisphere.radius]

theorem poleCutoff_zero_outside (x : Hemisphere.Sphere 2) (hx : x ∉ awayPoleCap) :
    poleCutoff x = 0 := by
  apply (poleCutoff_zero_iff x).mpr
  change ¬(-(7 / 8 : ℝ) ≤ x.val 0) at hx
  linarith

theorem poleCutoff_zero_fixed_germ (x : Hemisphere.Sphere 2) (hx : poleCutoff x = 0) :
    fixedPoleCap ∈ 𝓝 x := by
  have hhead : x.val 0 < -(1 / 2 : ℝ) := by
    have hh := (poleCutoff_zero_iff x).mp hx
    linarith
  exact mem_of_superset
    ((isOpen_lt smooth_head.continuous continuous_const).mem_nhds hhead)
    (fun y hy => show y.val 0 ≤ -(1 / 2 : ℝ) from hy.le)

theorem immersive_germ_of_tail
    {N G X : Type*} [NormedAddCommGroup N] [InnerProductSpace ℝ N]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace X] [ChartedSpace G X]
    (L : Hemisphere.Ambient 2 ≃ₗᵢ[ℝ] N) (g : N → X)
    (hg : ContMDiff 𝓘(ℝ, N) 𝓘(ℝ, G) ∞ g)
    (hgi : ∀ z, Injective (mfderiv 𝓘(ℝ, N) 𝓘(ℝ, G) g z))
    (γ : Hemisphere.Sphere 2 → X) (x : Hemisphere.Sphere 2) (hx : x.val 0 ≠ 0)
    (hγ : γ =ᶠ[𝓝 x] (fun y => g (L (Hemisphere.tail y)))) :
    Injective (mfderiv (𝓡 2) 𝓘(ℝ, G) γ x) := by
  let R : Hemisphere.Sphere 2 → N := fun y => L (Hemisphere.tail y)
  have hL : ContMDiff 𝓘(ℝ, Hemisphere.Ambient 2) 𝓘(ℝ, N) ∞
      L.toContinuousLinearEquiv.toContinuousLinearMap :=
    L.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.contMDiff
  have hR : ContMDiff (𝓡 2) 𝓘(ℝ, N) ∞ R := L.contDiff.contMDiff.comp smooth_tail
  have hRi : Injective (mfderiv (𝓡 2) 𝓘(ℝ, N) R x) := by
    change Injective (mfderiv (𝓡 2) 𝓘(ℝ, N)
      (L.toContinuousLinearEquiv.toContinuousLinearMap ∘ Hemisphere.tail) x)
    rw [mfderiv_comp x (hL.mdifferentiableAt (by simp))
      (smooth_tail.mdifferentiableAt (by simp)), mfderiv_eq_fderiv,
      L.toContinuousLinearEquiv.toContinuousLinearMap.fderiv]
    exact L.injective.comp (tail_mfderiv_injective_of_head_ne_zero x hx)
  rw [hγ.mfderiv_eq]
  change Injective (mfderiv (𝓡 2) 𝓘(ℝ, G) (g ∘ R) x)
  rw [mfderiv_comp x (hg.mdifferentiableAt (by simp)) (hR.mdifferentiableAt (by simp))]
  exact (hgi (R x)).comp hRi

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.BeltMeridianSphere
