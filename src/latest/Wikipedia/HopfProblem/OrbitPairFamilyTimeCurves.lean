import Wikipedia.HopfProblem.OrbitPairFamilyTimeVelocity
import Mathlib.Geometry.Manifold.IntegralCurve.Basic

/-!
# The family time curves solve the prescribed native velocity equation

The native chain rule along the real time inclusion identifies the actual
curve derivative with the smooth time velocity. A field agreeing with that
velocity therefore has the original family curves as integral curves.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.OrbitPair.NativeFamily

variable {E G H K M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]

theorem hasMFDerivAt_time_curve {F : ℝ × M → N}
    (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F) (t : ℝ) (x : M) :
    HasMFDerivAt 𝓘(ℝ, ℝ) J (fun s => F (s, x)) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (timeVelocity (I := I) (J := J) F (t, x))) := by
  have hin : HasMFDerivAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I)
      (fun s : ℝ => (s, x)) t (ContinuousLinearMap.inl ℝ ℝ E) :=
    (hasMFDerivAt_id t).prodMk (hasMFDerivAt_const x t)
  let D : (ℝ × E) →L[ℝ] G := mfderiv (𝓘(ℝ, ℝ).prod I) J F (t, x)
  have hdf : HasMFDerivAt 𝓘(ℝ, ℝ) J (fun s => F (s, x)) t
      (D.comp (ContinuousLinearMap.inl ℝ ℝ E)) :=
    (hF.mdifferentiableAt (by simp)).hasMFDerivAt.comp t hin
  have heq : D.comp (ContinuousLinearMap.inl ℝ ℝ E) =
      (1 : ℝ →L[ℝ] ℝ).smulRight (D (1, 0)) := by
    apply ContinuousLinearMap.ext
    intro a
    change D (a, 0) = a • D (1, 0)
    rw [← map_smul]
    congr 1
    simp
  exact hdf.congr_mfderiv heq

theorem isMIntegralCurveOn_family_of_velocity {F : ℝ × M → N}
    (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F)
    {v : (y : N) → TangentSpace J y} {S : Set ℝ} (x : M)
    (hmatch : ∀ t ∈ S, v (F (t, x)) = timeVelocity (I := I) (J := J) F (t, x)) :
    IsMIntegralCurveOn (fun t => F (t, x)) v S := by
  intro t ht
  rw [hmatch t ht]
  exact (hasMFDerivAt_time_curve hF t x).hasMFDerivWithinAt

end Wikipedia.HopfProblem.OrbitPair.NativeFamily
