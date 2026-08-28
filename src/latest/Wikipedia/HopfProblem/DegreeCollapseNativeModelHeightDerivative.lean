import Wikipedia.HopfProblem.DegreeCollapseNativeModelCurveTransport
import Wikipedia.HopfProblem.DegreeCollapseNativeLevelSuspensionHeight

/-!
# Original height derivatives after native level-field transport

Native pullback and the chain rule compute the original scalar height
speed directly in the level-product atlas. A time-speed-one field has
height speed minus the given positive normalization factor.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension

variable {D E H X M : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace X] [ChartedSpace H X]
  {I : ModelWithCorners ℝ D H}
  [TopologicalSpace M] [ChartedSpace E M]

theorem mvfderiv_native_model_pullback
    (A : PartialDiffeomorph I 𝓘(ℝ, E) X M ∞)
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (W : (z : X) → TangentSpace I z) {x : M} (hx : x ∈ A.target) :
    mvfderiv 𝓘(ℝ, E) f x (VectorField.mpullback 𝓘(ℝ, E) I A.symm W x) =
      mvfderiv I (f ∘ A) (A.symm x) (W (A.symm x)) := by
  rw [native_model_pullback_eq_mfderiv_symm A.symm W hx]
  exact (mvfderiv_comp_apply_of_eq (A.symm x) (hf.mdifferentiableAt (by simp))
    ((A.contMDiffOn_toFun.contMDiffAt
      (A.open_source.mem_nhds (A.map_target' hx))).mdifferentiableAt (by simp))
    (A.right_inv' hx) (W (A.symm x))).symm

variable {Z N : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [TopologicalSpace N] [ChartedSpace Z N]

theorem mvfderiv_native_level_height
    (A : PartialDiffeomorph (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (N × ℝ) M ∞)
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {b s : ℝ}
    (hheight : ∀ p ∈ A.source, f (A p) = b - s * p.2)
    (W : (p : N × ℝ) → TangentSpace (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) p)
    {x : M} (hx : x ∈ A.target) :
    mvfderiv 𝓘(ℝ, E) f x
      (VectorField.mpullback 𝓘(ℝ, E) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) A.symm W x) =
      -s * (W (A.symm x)).2 := by
  let q := A.symm x
  have heq : (f ∘ A) =ᶠ[𝓝 q] (fun p : N × ℝ => b - s * p.2) := by
    filter_upwards [A.open_source.mem_nhds (A.map_target' hx)] with p hp
    exact hheight p hp
  have hd : mfderiv (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (f ∘ A) q =
      mfderiv (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
        (fun p : N × ℝ => b - s * p.2) q := heq.mfderiv_eq
  rw [mvfderiv_native_model_pullback A hf W hx]
  change mfderiv (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (f ∘ A) q (W q) = _
  rw [hd]
  have hsnd : HasMFDerivAt (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
      (Prod.snd : N × ℝ → ℝ) q (ContinuousLinearMap.snd ℝ Z ℝ) := hasMFDerivAt_snd q
  have hh := (hasMFDerivAt_const (I := 𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) b q).sub
    ((hasMFDerivAt_const (I := 𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) s q).mul hsnd)
  have hh' : mfderiv (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
      (fun p : N × ℝ => b - s * p.2) q =
      (0 : (Z × ℝ) →L[ℝ] ℝ) -
        (s • ContinuousLinearMap.snd ℝ Z ℝ + q.2 • (0 : (Z × ℝ) →L[ℝ] ℝ)) :=
    hh.mfderiv
  rw [hh']
  change (0 : ℝ) - (s * (W q).2 + q.2 * (0 : ℝ)) = -s * (W q).2
  ring

end Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension
