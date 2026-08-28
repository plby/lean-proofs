import Wikipedia.HopfProblem.DegreeCollapseNativeLevelSuspensionField
import Mathlib.Geometry.Manifold.IntegralCurve.Basic

/-!
# The complete native suspension flow solves its generator field

Vertical translation is an actual native integral curve on the product
of the regular level with the real line. The chain rule through the
genuine suspension diffeomorphism gives the complete integral curves of
the constructed native generator, with exact retained-time translation.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension

variable {Z N : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [FiniteDimensional ℝ Z] [TopologicalSpace N] [ChartedSpace Z N]
  [IsManifold 𝓘(ℝ, Z) ∞ N]

theorem nativeVerticalField_integralCurve (p : N × ℝ) :
    IsMIntegralCurve (fun t : ℝ => (p.1, p.2 + t)) (nativeVerticalField (Z := Z)) := by
  intro t
  have hn : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Z) (fun _ : ℝ => p.1) t (0 : ℝ →L[ℝ] Z) :=
    hasMFDerivAt_const p.1 t
  have ht := (hasMFDerivAt_const (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ)) p.2 t).add
    (hasMFDerivAt_id (I := 𝓘(ℝ, ℝ)) t)
  apply (hn.prodMk ht).congr_mfderiv
  apply ContinuousLinearMap.ext
  intro r
  let s : ℝ := r
  change ((0 : Z), (0 : ℝ) + s) = s • ((0 : Z), (1 : ℝ))
  simp

theorem nativeSuspensionFlow_integralCurve
    (Ψ : Diffeomorph (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ))
      (N × ℝ) (N × ℝ) ∞) (p : N × ℝ) :
    IsMIntegralCurve (fun t : ℝ => nativeSuspensionFlow Ψ t p) (nativeSuspensionField Ψ) := by
  intro t
  let γ : ℝ → N × ℝ := fun s => ((Ψ.symm p).1, (Ψ.symm p).2 + s)
  have hb := nativeVerticalField_integralCurve (Z := Z) (Ψ.symm p) t
  have hd := (Ψ.contMDiff.mdifferentiableAt (by simp)).hasMFDerivAt.comp (f := γ) t hb
  change HasMFDerivAt 𝓘(ℝ, ℝ) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (fun s => Ψ (γ s)) t
    ((1 : ℝ →L[ℝ] ℝ).smulRight
      (mfderiv (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) Ψ
        (Ψ.symm (Ψ (γ t))) (nativeVerticalField (Ψ.symm (Ψ (γ t))))))
  rw [Ψ.symm_apply_apply]
  change HasMFDerivAt 𝓘(ℝ, ℝ) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (fun s => Ψ (γ s)) t
    ((mfderiv (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) Ψ (γ t)).comp
      ((1 : ℝ →L[ℝ] ℝ).smulRight (nativeVerticalField (γ t)))) at hd
  apply hd.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro r
  exact (mfderiv (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) Ψ (γ t)).map_smul
    (r : ℝ) (nativeVerticalField (γ t))

theorem nativeSuspensionFlow_height
    (Ψ : Diffeomorph (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ))
      (N × ℝ) (N × ℝ) ∞)
    (hheight : ∀ p, (Ψ p).2 = p.2) (t : ℝ) (p : N × ℝ) :
    (nativeSuspensionFlow Ψ t p).2 = p.2 + t := by
  have hi : (Ψ.symm p).2 = p.2 := by
    have hh := hheight (Ψ.symm p)
    rw [Ψ.apply_symm_apply] at hh
    exact hh.symm
  change (Ψ ((Ψ.symm p).1, (Ψ.symm p).2 + t)).2 = p.2 + t
  rw [hheight, hi]

end Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension
