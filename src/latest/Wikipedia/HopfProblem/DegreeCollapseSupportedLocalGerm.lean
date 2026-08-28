import Wikipedia.HopfProblem.DegreeCollapseSpecialLinearGerm
import Wikipedia.SmoothSixDPoincare.RelativeGermLinearization

/-!
# Realizing a nonlinear coordinate germ with determinant-one derivative

The actual derivative is realized by elementary supported shears. The
remaining tangent-to-identity germ is realized by a small smooth displacement.
Composition retains a common compact support and a fixed origin.
-/

noncomputable section

open Set Function Filter
open scoped Topology ContDiff Manifold
open Wikipedia.SmoothSixDPoincare SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.SupportedGerms

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι] [DecidableEq ι] [Nontrivial ι]

theorem realizes_local_germ (b : Module.Basis ι ℝ E) {f : E → E} {U : Set E}
    (hU : IsOpen U) (h0 : (0 : E) ∈ U) (hf : ContDiffOn ℝ ∞ f U)
    (hf0 : f 0 = 0) (hbij : Bijective (fderiv ℝ f 0))
    (hdet : (fderiv ℝ f 0).toLinearMap.det = 1) : Realizes U f := by
  obtain ⟨C, A, K, hC, -, -, hK, hKU, hA, hA0, hdiff, hfix, -, hfixed, hgerm⟩ :=
    SmallPerturbation.exists_relative_germ_linearization_isotopy hU h0 hf hf0 hbij
      (0 : E →L[ℝ] ℝ) (fun _ _ => rfl) (⊥ : Submodule ℝ E) (by
        intro x hx
        have hx0 : x = 0 := hx.2
        subst x
        exact hf0)
  have hCdet : C.toLinearMap.det = 1 := by
    change C.toContinuousLinearMap.toLinearMap.det = 1
    rw [hC]
    exact hdet
  obtain ⟨d, hd⟩ := hdiff 1
  have H : SupportedRelativeIsotopy d K {0} := by
    refine ⟨A, hA, hA0, fun x => (hd x).symm, hdiff, hfix, ?_⟩
    intro t x hx
    exact hfixed t x (mem_singleton_iff.mp hx)
  have hdreal : Realizes U (fun x => A (1, x)) :=
    ⟨d, K, hK, hKU, ⟨H⟩, Filter.Eventually.of_forall hd⟩
  obtain ⟨D, L, hL, hLU, hH, hDgerm⟩ := (realizes_det_one b C hCdet hU h0).comp hdreal
  exact ⟨D, L, hL, hLU, hH, hDgerm.trans hgerm.symm⟩

end Wikipedia.HopfProblem.DegreeCollapse.SupportedGerms
