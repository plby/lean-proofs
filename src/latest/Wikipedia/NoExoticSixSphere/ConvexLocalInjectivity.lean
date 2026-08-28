import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Local injectivity within a convex set from an invertible derivative

Subtract the inverse-linearized map from the identity. Its derivative is
zero at the base point, so the convex mean-value estimate makes the error
locally less than one-Lipschitz. No extension across the set's boundary is used.
-/

noncomputable section

open Function Set Filter Metric
open scoped Topology ContDiff

namespace NoExoticSixSphere

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_injOn_nhdsWithin_of_convex_derivative {f : E → F} {f' : E → E →L[ℝ] F}
    {s : Set E} {x : E} (hs : Convex ℝ s) (A : E ≃L[ℝ] F)
    (hA : f' x = A.toContinuousLinearMap)
    (hd : ∀ᶠ y in 𝓝[s] x, HasFDerivWithinAt f (f' y) s y)
    (hc : ContinuousWithinAt f' s x) : ∃ t ∈ 𝓝[s] x, InjOn f t := by
  let g : E → E := fun y ↦ y - A.symm (f y)
  let g' : E → E →L[ℝ] E := fun y ↦ 1 - A.symm.toContinuousLinearMap.comp (f' y)
  have hgd : ∀ᶠ y in 𝓝[s] x, HasFDerivWithinAt g (g' y) s y := by
    filter_upwards [hd] with y hy
    exact (hasFDerivWithinAt_id y s).sub (A.symm.hasFDerivAt.comp_hasFDerivWithinAt y hy)
  have hgc : ContinuousWithinAt g' s x :=
    continuousWithinAt_const.sub (continuousWithinAt_const.clm_comp hc)
  have hgx : g' x = 0 := by
    ext v
    change v - A.symm (f' x v) = 0
    rw [hA]
    simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply, sub_self]
  obtain ⟨t, ht, hL⟩ := hs.exists_nhdsWithin_lipschitzOnWith_of_hasFDerivWithinAt_of_nnnorm_lt
    hgd hgc (1 / 2) (by rw [hgx]; norm_num)
  refine ⟨t, ht, ?_⟩
  intro y hy z hz he
  have hbound := hL.norm_sub_le hy hz
  have hdiff : g y - g z = y - z := by
    change (y - A.symm (f y)) - (z - A.symm (f z)) = y - z
    rw [he]
    abel
  rw [hdiff] at hbound
  have hn : ‖y - z‖ = 0 := by
    norm_num at hbound
    linarith [norm_nonneg (y - z)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

theorem exists_injOn_nhdsWithin_of_convex_contDiffWithinAt {f : E → F} {s : Set E} {x : E}
    (hs : Convex ℝ s) (hu : UniqueDiffOn ℝ s) (hx : x ∈ s)
    (hf : ContDiffWithinAt ℝ 1 f s x) (A : E ≃L[ℝ] F)
    (hA : fderivWithin ℝ f s x = A.toContinuousLinearMap) :
    ∃ t ∈ 𝓝[s] x, InjOn f t := by
  apply exists_injOn_nhdsWithin_of_convex_derivative hs A hA
  · have he := hf.eventually (by norm_num)
    rw [insert_eq_of_mem hx] at he
    filter_upwards [he] with y hy
    exact (hy.differentiableWithinAt (by norm_num)).hasFDerivWithinAt
  · exact hf.continuousWithinAt_fderivWithin hu (by norm_num) hx

end NoExoticSixSphere
