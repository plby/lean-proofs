import Wikipedia.HopfProblem.RiemannBoundaryPrimitive
import Wikipedia.HopfProblem.RiemannBoundaryTrace
import Wikipedia.HopfProblem.SchwarzReflection

/-!
# Analytic gluing with a vanishing jump

The input functions need not have continuous boundary values. Boundedness
supplies continuous primitives; the vanishing jump identifies their traces;
Morera glues the primitives. Differentiating the glued primitive supplies
the actual analytic extension of the input functions.
-/

noncomputable section

open Complex Filter Metric Set
open scoped Topology ComplexConjugate

namespace Wikipedia.HopfProblem.RiemannBoundary

/-- Bounded holomorphic functions on the two sides of a straight line
extend together when their reflected jump tends to zero. No complex
boundary value of either input function is assumed. -/
theorem exists_analytic_extension_of_vanishing_jump {f g : ℂ → ℂ} {a b h M N : ℝ}
    (hab : a < b) (hh : 0 < h)
    (hf : DifferentiableOn ℂ f (openRectangle a b 0 h))
    (hg : DifferentiableOn ℂ g (openRectangle a b (-h) 0))
    (hfb : ∀ z ∈ openRectangle a b 0 h, ‖f z‖ ≤ M)
    (hgb : ∀ z ∈ openRectangle a b (-h) 0, ‖g z‖ ≤ N)
    (hjump : ∀ x ∈ Ioo a b,
      Tendsto (fun z => f z - g (conj z))
        (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 0)) :
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H (openRectangle a b (-h) h) ∧
      EqOn H f (openRectangle a b 0 h) ∧
      EqOn H g (openRectangle a b (-h) 0) := by
  obtain ⟨F, hFc, hFd⟩ := exists_continuous_primitive_openRectangle_of_norm_le hf hfb
  obtain ⟨G, hGc, hGd⟩ := exists_continuous_primitive_openRectangle_of_norm_le hg hgb
  let x₀ : ℝ := (a + b) / 2
  have hx₀ : x₀ ∈ Ioo a b := by dsimp [x₀]; constructor <;> linarith
  let c : ℂ := F x₀ - G x₀
  have htrace : ∀ x ∈ Ioo a b, F (x : ℂ) = G (x : ℂ) + c := by
    intro x hx
    have hdF : ∀ t ∈ Ioo a b, ∀ y ∈ Ioo 0 h,
        HasDerivAt F (f (t + y * I)) (t + y * I) := by
      intro t ht y hy
      exact hFd _ (by simpa [openRectangle] using And.intro ht hy)
    have hdG : ∀ t ∈ Ioo a b, ∀ y ∈ Ioo 0 h,
        HasDerivAt G (g (t - y * I)) (t - y * I) := by
      intro t ht y hy
      apply hGd
      simpa [openRectangle] using And.intro ht (show -y ∈ Ioo (-h) 0 by
        constructor <;> linarith [hy.1, hy.2])
    have he := boundary_trace_sub_eq hh hx hx₀ hFc hGc hdF hdG hjump
    dsimp [c]
    linear_combination he
  let P := SchwarzReflection.pasteUpper F (fun z => G z + c)
  have hP : AnalyticOnNhd ℂ P (openRectangle a b (-h) h) := by
    apply SchwarzReflection.analyticOnNhd_pasteUpper (isOpen_openRectangle _ _ _ _)
      hFc.continuousOn (hGc.add continuous_const).continuousOn
    · intro z hz hpos
      exact (hFd z ⟨hz.1, hpos, hz.2.2⟩).differentiableAt
    · intro z hz hneg
      exact ((hGd z ⟨hz.1, hz.2.1, hneg⟩).add_const c).differentiableAt
    · intro z hz hzero
      change F z = G z + c
      have heq : (z.re : ℂ) = z := by
        exact Complex.ext (by simp) (by simpa using hzero.symm)
      simpa only [heq] using htrace z.re hz.1
  refine ⟨deriv P, hP.deriv, ?_, ?_⟩
  · intro z hz
    have hnear : P =ᶠ[𝓝 z] F := by
      filter_upwards [continuousAt_const.eventually_lt continuous_im.continuousAt hz.2.1]
        with w hw
      exact SchwarzReflection.pasteUpper_of_nonneg F (fun w => G w + c) hw.le
    exact ((hFd z hz).congr_of_eventuallyEq hnear).deriv
  · intro z hz
    have hnear : P =ᶠ[𝓝 z] (fun w => G w + c) := by
      filter_upwards [continuous_im.continuousAt.eventually_lt continuousAt_const hz.2.2]
        with w hw
      exact SchwarzReflection.pasteUpper_of_neg F (fun w => G w + c) hw
    exact (((hGd z hz).add_const c).congr_of_eventuallyEq hnear).deriv

end Wikipedia.HopfProblem.RiemannBoundary
