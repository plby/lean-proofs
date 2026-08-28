import Wikipedia.HopfProblem.SpecialPeriodsCuspFamilyBase

/-!
# Normalized logarithms near the cusp

A nonvanishing analytic germ has a genuine normalized holomorphic logarithm
on a sufficiently small disc. Its value at the centre is the specified
normalized principal logarithm. Continuous logarithmic lifts on a connected
space differ by a single integer, rather than pointwise choices of integers.
-/

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.TauCusp

open CuspUniformization

/-- A local logarithm of an analytic unit, normalized by its actual value at zero. -/
theorem analytic_unit_normalized_logarithm {u : ℂ → ℂ}
    (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0) :
    ∃ r > 0, ∃ h : ℂ → ℂ,
      AnalyticOnNhd ℂ h (Metric.ball 0 r) ∧
      h 0 = logarithm (u 0) ∧
      ∀ t ∈ Metric.ball 0 r, exponential (h t) = u t := by
  let s := logarithm (u 0)
  let e := CuspFamily.scalarExponentialChart s
  have hs : s ∈ e.source := CuspFamily.scalarExponentialChart_mem_source s
  have he0 : e s = u 0 := exponential_logarithm hu0
  have huT : u 0 ∈ e.target := he0 ▸ e.map_source hs
  have hlocal : ∀ᶠ t in 𝓝 (0 : ℂ), AnalyticAt ℂ u t ∧ u t ∈ e.target :=
    hu.eventually_analyticAt.and (hu.continuousAt (e.open_target.mem_nhds huT))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hlocal
  refine ⟨r, hr, e.symm ∘ u, ?_, ?_, ?_⟩
  · intro t ht
    have hInv : ContDiffOn ℂ ω e.symm e.target :=
      CuspFamily.scalarExponentialChart_symm_holomorphic s
    exact ((hInv (u t) (hball ht).2).contDiffAt
      (e.open_target.mem_nhds (hball ht).2)).analyticAt.comp (hball ht).1
  · change e.symm (u 0) = s
    rw [← he0]
    exact e.left_inv hs
  · intro t ht
    exact e.right_inv (hball ht).2

/-- Two continuous normalized logarithmic lifts differ by one fixed integer
on any nonempty preconnected space. -/
theorem continuous_exponential_eq_int_constant
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X] [Nonempty X]
    {f g : X → ℂ} (hf : Continuous f) (hg : Continuous g)
    (he : ∀ x, exponential (f x) = exponential (g x)) :
    ∃ k : ℤ, ∀ x, f x = g x + k := by
  classical
  let x₀ : X := Classical.arbitrary X
  obtain ⟨k, hk⟩ := (exponential_eq_iff (f x₀) (g x₀)).mp (he x₀)
  refine ⟨k, ?_⟩
  have hfg : f = fun x => g x + (k : ℂ) :=
    (T2Space.isSeparatedMap exponential).eq_of_comp_eq
      CuspFamily.exponential_isLocalDiffeomorph.isLocalHomeomorph.isLocallyInjective
      hf (hg.add continuous_const)
      (funext fun x => by
        simpa only [Function.comp_apply, exponential_add, exponential_int, mul_one] using he x)
      x₀ hk
  exact fun x => congrFun hfg x

end Wikipedia.HopfProblem.SpecialPeriods.TauCusp
