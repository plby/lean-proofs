import Wikipedia.HopfProblem.DegreeCollapseGlobalFlowSmoothness

/-!
# Native flow time maps as actual field-preserving diffeomorphisms

A smooth complete flow gives genuine native diffeomorphisms at every
fixed time. Differentiating the commuting flow action proves that these
maps preserve the original tangent field. They can therefore adjust
constant endpoint time origins without changing the vector field.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.SmoothODE

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

/-- The actual time map has the opposite time map as its smooth inverse. -/
def nativeFlowTimeDiffeomorph (F : Flow ℝ M)
    (hs : ∀ t, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (F t)) (t : ℝ) :
    M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M where
  toFun := F t
  invFun := F (-t)
  left_inv x := by rw [← F.map_add, neg_add_cancel, F.map_zero_apply]
  right_inv x := by rw [← F.map_add, add_neg_cancel, F.map_zero_apply]
  contMDiff_toFun := hs t
  contMDiff_invFun := hs (-t)

/-- The derivative of an actual flow time map transports the original
tangent vector to the original field at the image point. -/
theorem mfderiv_flow_time_field (F : Flow ℝ M)
    (hs : ∀ t, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (F t))
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) (t : ℝ) (x : M) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (F t) x (V x) = V (F t x) := by
  have hd := ((hs t).mdifferentiableAt (by simp) (x := F 0 x)).hasMFDerivAt.comp 0 (hF x 0)
  change HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (F t ∘ fun s => F s x) 0
    ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (F t) (F 0 x)).comp
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (F 0 x)))) at hd
  rw [F.map_zero_apply] at hd
  have hcomm : (F t ∘ fun s => F s x) = (fun s => F s (F t x)) := by
    funext s
    change F t (F s x) = F s (F t x)
    rw [← F.map_add, ← F.map_add, add_comm]
  rw [hcomm] at hd
  have hd' := hF (F t x) 0
  change HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s => F s (F t x)) 0
    ((1 : ℝ →L[ℝ] ℝ).smulRight (V (F 0 (F t x)))) at hd'
  rw [F.map_zero_apply] at hd'
  have hh := hd.mfderiv.symm.trans hd'.mfderiv
  have hv := congrArg (fun A : ℝ →L[ℝ] TangentSpace 𝓘(ℝ, E) (F t x) => A 1) hh
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (F t) x ((1 : ℝ) • V x) =
    (1 : ℝ) • V (F t x) at hv
  simpa only [one_smul] using hv

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]

/-- Smoothness of the actual native field constructs the time diffeomorphism;
smooth dependence is supplied by the proved native-flow theorem. -/
def nativeFlowTimeDiffeomorph_of_field
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) (t : ℝ) :
    M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M :=
  nativeFlowTimeDiffeomorph F
    (fun s => (contMDiff_native_flow hV F hF).comp (contMDiff_id.prodMk contMDiff_const)) t

end Wikipedia.HopfProblem.DegreeCollapse.SmoothODE
