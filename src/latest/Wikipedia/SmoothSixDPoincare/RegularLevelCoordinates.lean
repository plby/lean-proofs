import Wikipedia.NoExoticSixSphere.LocalInverse
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Smooth coordinates with the original regular height as first coordinate

The complementary coordinate is the continuous projection onto the actual
derivative kernel. The analytic inverse-function theorem constructs both
smooth directions on genuine open sets.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.RegularLevel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A nonzero real-valued continuous linear map is onto. -/
theorem surjective_of_ne_zero {L : E →L[ℝ] ℝ} (hL : L ≠ 0) : Surjective L := by
  have hex : ∃ v, L v ≠ 0 := by
    by_contra! h
    exact hL (ContinuousLinearMap.ext h)
  obtain ⟨v, hv⟩ := hex
  intro r
  refine ⟨(r / L v) • v, ?_⟩
  rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hv]

variable [FiniteDimensional ℝ E]

theorem finrank_kernel_add_one {L : E →L[ℝ] ℝ} (hL : L ≠ 0) :
    Module.finrank ℝ L.ker + 1 = Module.finrank ℝ E := by
  have hr : L.range = ⊤ := LinearMap.range_eq_top.mpr (surjective_of_ne_zero hL)
  have hdim := L.toLinearMap.finrank_range_add_finrank_ker
  change Module.finrank ℝ L.range + Module.finrank ℝ L.ker = Module.finrank ℝ E at hdim
  rw [hr, finrank_top, Module.finrank_self] at hdim
  omega

/-- A regular smooth scalar function is the first coordinate of a constructed smooth chart. -/
theorem exists_height_partialDiffeomorph {f : E → ℝ} {U : Set E} {x : E}
    (hU : IsOpen U) (hx : x ∈ U) (hf : ContDiffOn ℝ ∞ f U)
    (hreg : fderiv ℝ f x ≠ 0) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, E)
        𝓘(ℝ, ℝ × (fderiv ℝ f x).ker) E (ℝ × (fderiv ℝ f x).ker) ∞,
      x ∈ Φ.source ∧ Φ.source ⊆ U ∧
        (∀ y, (Φ y).1 = f y) ∧ Φ x = (f x, 0) := by
  let L := fderiv ℝ f x
  have hs : HasStrictFDerivAt f L x :=
    (hf.contDiffAt (hU.mem_nhds hx)).hasStrictFDerivAt (by simp)
  have hr : L.range = ⊤ := LinearMap.range_eq_top.mpr (surjective_of_ne_zero hreg)
  have hk : L.ker.ClosedComplemented := L.ker_closedComplemented_of_finiteDimensional_range
  let φ := hs.implicitFunctionDataOfComplemented f L hr hk
  have hg : ContDiffOn ℝ ∞ φ.prodFun U := by
    apply hf.prodMk
    change ContDiffOn ℝ ∞ (fun y => Classical.choose hk (y - x)) U
    exact (Classical.choose hk).contDiff.comp_contDiffOn
      (contDiffOn_id.sub contDiffOn_const)
  obtain ⟨Φ, hΦ, hΦU, hΦf⟩ := NoExoticSixSphere.exists_partialDiffeomorph_of_contDiffOn
    hU hx hg φ.isInvertible_fderiv_prodFun
  refine ⟨Φ, hΦ, hΦU, ?_, ?_⟩
  · intro y
    rw [hΦf]
    rfl
  · rw [hΦf]
    change (f x, Classical.choose hk (x - x)) = (f x, 0)
    simp

end Wikipedia.SmoothSixDPoincare.RegularLevel
