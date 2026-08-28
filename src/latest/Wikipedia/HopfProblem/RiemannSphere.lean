import Wikipedia.HopfProblem.AffineSphereManifold

/-!
# The standard analytic Riemann sphere

The one-point compactification of `ℂ` carries the standard two affine charts,
with the reciprocal parametrization sending zero to infinity. Both its
topology and its analytic atlas are constructed. Any verified pair of affine
charts with the same inversion transition gives a biholomorphic sphere.
-/

noncomputable section

open Set Filter Topology Bornology OnePoint
open scoped ContDiff

namespace Wikipedia.HopfProblem

abbrev RiemannSphere := OnePoint ℂ

namespace RiemannSphere

def infinityParametrization (z : ℂ) : RiemannSphere := by
  classical
  exact if z = 0 then (∞ : RiemannSphere) else (z⁻¹ : ℂ)

@[simp] theorem infinityParametrization_zero :
    infinityParametrization 0 = (∞ : RiemannSphere) := by
  simp [infinityParametrization]

theorem infinityParametrization_of_ne {z : ℂ} (hz : z ≠ 0) :
    infinityParametrization z = (z⁻¹ : ℂ) := by simp [infinityParametrization, hz]

theorem infinityParametrization_continuous : Continuous infinityParametrization := by
  classical
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z = 0
  · subst z
    change Tendsto infinityParametrization (𝓝 (0 : ℂ)) (𝓝 (infinityParametrization 0))
    rw [infinityParametrization_zero, ← nhdsNE_sup_pure (0 : ℂ), tendsto_sup]
    constructor
    · have hc : Tendsto ((↑) : ℂ → OnePoint ℂ) (cobounded ℂ) (𝓝 (∞ : RiemannSphere)) := by
        simpa only [coclosedCompact_eq_cocompact, Metric.cobounded_eq_cocompact] using
          (OnePoint.tendsto_coe_infty (X := ℂ))
      have hi := hc.comp (tendsto_inv₀_nhdsNE_zero (α := ℂ))
      apply hi.congr'
      filter_upwards [self_mem_nhdsWithin] with w hw
      have hw' : w ≠ 0 := hw
      simp [infinityParametrization, hw']
    · simpa only [infinityParametrization_zero] using
        (tendsto_pure_nhds infinityParametrization (0 : ℂ))
  · have hc : ContinuousAt (fun w : ℂ => ((w⁻¹ : ℂ) : OnePoint ℂ)) z :=
      OnePoint.continuous_coe.continuousAt.comp (contDiffAt_inv ℂ hz (n := ω)).continuousAt
    apply hc.congr_of_eventuallyEq
    filter_upwards [(isOpen_ne_fun continuous_id continuous_const).mem_nhds hz] with w hw
    exact infinityParametrization_of_ne hw

theorem infinityParametrization_injective : Function.Injective infinityParametrization := by
  classical
  intro z w he
  by_cases hz : z = 0 <;> by_cases hw : w = 0
  · exact hz.trans hw.symm
  · simp [infinityParametrization, hz, hw] at he
  · simp [infinityParametrization, hz, hw] at he
  · simpa [infinityParametrization, hz, hw] using he

def standardCharts : TwoAffineCharts RiemannSphere where
  left := ((↑) : ℂ → OnePoint ℂ)
  right := infinityParametrization
  continuous_left := OnePoint.continuous_coe
  continuous_right := infinityParametrization_continuous
  left_injective := OnePoint.coe_injective
  right_injective := infinityParametrization_injective
  inversion z hz := by simp [infinityParametrization, inv_ne_zero hz]
  endpoints_ne := by simp [infinityParametrization]
  covered p := by
    induction p using OnePoint.rec with
    | infty => exact Or.inr ⟨0, infinityParametrization_zero⟩
    | coe z => exact Or.inl ⟨z, rfl⟩

instance chartedSpace : ChartedSpace ℂ RiemannSphere := standardCharts.chartedSpace

instance isManifold : IsManifold (modelWithCornersSelf ℂ ℂ) ω RiemannSphere :=
  standardCharts.isManifold

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] (A : TwoAffineCharts Y)

theorem homeomorph_infinityParametrization (z : ℂ) :
    A.homeomorph (infinityParametrization z) = A.right z := by
  by_cases hz : z = 0
  · subst z
    rw [infinityParametrization_zero]
    exact A.homeomorph_infty
  · rw [infinityParametrization_of_ne hz]
    change A.left z⁻¹ = A.right z
    simpa only [inv_inv] using A.inversion z⁻¹ (inv_ne_zero hz)

theorem homeomorph_comp_standardCharts (b : Bool) :
    A.homeomorph ∘ standardCharts.affineMap b = A.affineMap b := by
  funext z
  cases b
  · exact A.homeomorph_coe z
  · exact homeomorph_infinityParametrization A z

theorem homeomorph_symm_comp_affineMaps (b : Bool) :
    A.homeomorph.symm ∘ A.affineMap b = standardCharts.affineMap b := by
  funext z
  apply A.homeomorph.injective
  rw [Function.comp_apply, Homeomorph.apply_symm_apply]
  exact (congrFun (homeomorph_comp_standardCharts A b) z).symm

theorem homeomorph_holomorphic :
    letI := A.chartedSpace
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω A.homeomorph := by
  let := A.chartedSpace
  apply standardCharts.contMDiff_of_comp_affineMaps (modelWithCornersSelf ℂ ℂ)
  intro b
  rw [homeomorph_comp_standardCharts]
  exact A.affineMap_holomorphic b

theorem homeomorph_symm_holomorphic :
    letI := A.chartedSpace
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω A.homeomorph.symm := by
  let := A.chartedSpace
  apply A.contMDiff_of_comp_affineMaps (modelWithCornersSelf ℂ ℂ)
  intro b
  rw [homeomorph_symm_comp_affineMaps]
  exact standardCharts.affineMap_holomorphic b

end RiemannSphere

end Wikipedia.HopfProblem
