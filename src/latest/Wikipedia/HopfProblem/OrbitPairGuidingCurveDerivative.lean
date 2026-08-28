import Wikipedia.HopfProblem.OrbitPairNativeFamilyTrack

/-!
# Native derivative of a vertical guiding curve
-/

noncomputable section

open Function
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.OrbitPair.NativeFamily

variable {E G H K M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace K N]

theorem guiding_curve_derivative {F : ℝ × M → N}
    (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F) (t : ℝ) (x : M) :
    (mfderiv 𝓘(ℝ, ℝ) J (fun s => F (s, x)) t : ℝ →L[ℝ] G) (1 : ℝ) =
    (mfderiv (𝓘(ℝ, ℝ).prod I) J F (t, x) : ℝ × E →L[ℝ] G) (1, 0) := by
  have hin : HasMFDerivAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I)
      (fun s : ℝ => (s, x)) t (ContinuousLinearMap.inl ℝ ℝ E) :=
    (hasMFDerivAt_id t).prodMk (hasMFDerivAt_const x t)
  let A : ℝ × E →L[ℝ] G := mfderiv (𝓘(ℝ, ℝ).prod I) J F (t, x)
  let B : ℝ →L[ℝ] G := mfderiv 𝓘(ℝ, ℝ) J (fun s => F (s, x)) t
  have hB : B = A.comp (ContinuousLinearMap.inl ℝ ℝ E) := by
    have hh := mfderiv_comp t (hF.mdifferentiableAt (by simp)) hin.mdifferentiableAt
    rw [hin.mfderiv] at hh
    exact hh
  change B 1 = A (1, 0)
  rw [hB]
  rfl

def HasTransverseGuidingVelocity (F : ℝ × M → N) (p : ℝ × (M × M)) : Prop :=
  let A : ℝ × E →L[ℝ] G := mfderiv (𝓘(ℝ, ℝ).prod I) J F (p.1, p.2.1)
  let B : ℝ × E →L[ℝ] G := mfderiv (𝓘(ℝ, ℝ).prod I) J F (p.1, p.2.2)
  A (1, 0) ∉ LinearMap.range B.toLinearMap

end Wikipedia.HopfProblem.OrbitPair.NativeFamily
