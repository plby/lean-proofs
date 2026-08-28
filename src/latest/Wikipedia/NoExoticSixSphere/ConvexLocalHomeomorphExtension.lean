import Wikipedia.NoExoticSixSphere.ConvexLocalInjectivity
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FiniteDimensional

/-!
# Local topological extension of a map on a convex set

An invertible derivative and continuous nearby derivatives give arbitrarily
small Lipschitz error after subtracting the linear part. A finite-dimensional
Lipschitz extension gives a genuine ambient homeomorphism agreeing locally on
the set. It is not asserted to be smooth or to preserve either half-space.
-/

noncomputable section

open Function Set Filter Metric
open scoped Topology ContDiff

namespace NoExoticSixSphere

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_homeomorph_nhdsWithin_of_convex_derivative
    {f : E → F} {f' : E → E →L[ℝ] F} {s : Set E} {x : E}
    (hs : Convex ℝ s) (A : E ≃L[ℝ] F) (hA : f' x = A.toContinuousLinearMap)
    (hd : ∀ᶠ y in 𝓝[s] x, HasFDerivWithinAt f (f' y) s y)
    (hc : ContinuousWithinAt f' s x) :
    ∃ (t : Set E) (g : E ≃ₜ F), t ∈ 𝓝[s] x ∧ EqOn f g t := by
  let u : E → F := fun y ↦ f y - A y
  let u' : E → E →L[ℝ] F := fun y ↦ f' y - A.toContinuousLinearMap
  have hud : ∀ᶠ y in 𝓝[s] x, HasFDerivWithinAt u (u' y) s y := by
    filter_upwards [hd] with y hy
    exact hy.sub A.hasFDerivAt.hasFDerivWithinAt
  have huc : ContinuousWithinAt u' s x := hc.sub continuousWithinAt_const
  have hux : u' x = 0 := sub_eq_zero.mpr hA
  rcases subsingleton_or_nontrivial E with hE | hE
  · letI := hE
    letI : Subsingleton F := A.symm.injective.subsingleton
    exact ⟨univ, A.toHomeomorph, Filter.univ_mem, fun _ _ ↦ Subsingleton.elim _ _⟩
  · letI := hE
    have hn : 0 < ‖A.symm.toContinuousLinearMap‖₊⁻¹ := by
      apply inv_pos.mpr
      exact A.nnnorm_symm_pos
    obtain ⟨c, hc0, hcsmall⟩ := exists_pos_mul_lt hn (lipschitzExtensionConstant F)
    obtain ⟨t, ht, hL⟩ := hs.exists_nhdsWithin_lipschitzOnWith_of_hasFDerivWithinAt_of_nnnorm_lt
      hud huc c (by simpa only [hux, nnnorm_zero] using hc0)
    have happ : ApproximatesLinearOn f A.toContinuousLinearMap t c :=
      LipschitzOnWith.approximatesLinearOn hL
    obtain ⟨g, hg⟩ := happ.exists_homeomorph_extension (Or.inr hcsmall)
    exact ⟨t, g, ht, hg⟩

theorem exists_homeomorph_nhdsWithin_of_convex_contDiffWithinAt
    {f : E → F} {s : Set E} {x : E} (hs : Convex ℝ s) (hu : UniqueDiffOn ℝ s) (hx : x ∈ s)
    (hf : ContDiffWithinAt ℝ 1 f s x) (A : E ≃L[ℝ] F)
    (hA : fderivWithin ℝ f s x = A.toContinuousLinearMap) :
    ∃ (t : Set E) (g : E ≃ₜ F), t ∈ 𝓝[s] x ∧ EqOn f g t := by
  apply exists_homeomorph_nhdsWithin_of_convex_derivative hs A hA
  · have he := hf.eventually (by norm_num)
    rw [insert_eq_of_mem hx] at he
    filter_upwards [he] with y hy
    exact (hy.differentiableWithinAt (by norm_num)).hasFDerivWithinAt
  · exact hf.continuousWithinAt_fderivWithin hu (by norm_num) hx

end NoExoticSixSphere
