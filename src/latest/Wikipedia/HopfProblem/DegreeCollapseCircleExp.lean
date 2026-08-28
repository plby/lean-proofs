import Wikipedia.SmoothSixDPoincare.BoundarylessLocalInverse
import Wikipedia.SmoothSixDPoincare.SphereLinearDiffeomorph
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Smooth descent through the actual circle exponential

The exponential parametrization is a local diffeomorphism for the native
sphere atlas. Thus smoothness of a circle-valued parametrization into a
manifold can be checked after composition with the real angle parameter.
-/

noncomputable section

open Set Function Filter
open scoped ContDiff Manifold Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.CircleGluing

theorem circleExp_derivative_injective (t : ℝ) :
    Injective (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp t) := by
  let _ : Fact (Module.finrank ℝ ℂ = 1 + 1) := ⟨Complex.finrank_real_complex⟩
  have hd : HasDerivAt (fun s : ℝ => (Circle.exp s : ℂ))
      (Complex.exp ((t : ℂ) * Complex.I) * Complex.I) t := by
    simpa only [Circle.coe_exp, Complex.real_smul, id_eq, one_mul] using
      ((hasDerivAt_id (t : ℂ)).mul_const Complex.I).cexp.comp_ofReal
  have hdne : (Complex.exp ((t : ℂ) * Complex.I) * Complex.I : ℂ) ≠ 0 :=
    mul_ne_zero (Complex.exp_ne_zero _) Complex.I_ne_zero
  have hi0 : Injective (fderiv ℝ (fun s : ℝ => (Circle.exp s : ℂ)) t) := by
    rw [hd.hasFDerivAt.fderiv]
    exact smul_left_injective ℝ hdne
  let c : Circle → ℂ := fun z => (z : ℂ)
  have hc : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ c := contMDiff_coe_sphere
  have hi : Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ)
      (c ∘ (fun s : ℝ => Circle.exp s)) t) := by
    rw [mfderiv_eq_fderiv]
    exact hi0
  rw [mfderiv_comp t (hc.mdifferentiableAt (by simp))
    ((contMDiff_circleExp (m := ∞)).mdifferentiableAt (by simp))] at hi
  intro x y hxy
  exact hi (congrArg (mfderiv (𝓡 1) 𝓘(ℝ, ℂ) c (Circle.exp t)) hxy)

theorem circleExp_localDiffeomorph (t : ℝ) :
    IsLocalDiffeomorphAt 𝓘(ℝ, ℝ) (𝓡 1) ∞ Circle.exp t := by
  let L : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1) := mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp t
  have hi : Injective L := circleExp_derivative_injective t
  have hs : Surjective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := L.toLinearMap)
      (by simp)).mp hi
  apply isLocalDiffeomorphAt_boundaryless isOpen_univ (mem_univ t)
    (contMDiff_circleExp (m := ∞)).contMDiffOn
  exact ⟨(LinearEquiv.ofBijective L.toLinearMap ⟨hi, hs⟩).toContinuousLinearEquiv, rfl⟩

variable {G H N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
  [TopologicalSpace N] [ChartedSpace H N]

theorem contMDiff_of_comp_circleExp {γ : Circle → N}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) J ∞ (γ ∘ Circle.exp)) :
    ContMDiff (𝓡 1) J ∞ γ := by
  intro z
  obtain ⟨t, rfl⟩ := Circle.exp_surjective z
  let h := circleExp_localDiffeomorph t
  have hs : ContMDiffAt (𝓡 1) J ∞ ((γ ∘ Circle.exp) ∘ h.localInverse) (Circle.exp t) :=
    (hγ.contMDiffAt (x := h.localInverse (Circle.exp t))).comp _ h.localInverse_contMDiffAt
  apply hs.congr_of_eventuallyEq
  filter_upwards [h.localInverse_eventuallyEq_right] with y hy
  exact (congrArg γ hy).symm

end Wikipedia.HopfProblem.DegreeCollapse.CircleGluing
