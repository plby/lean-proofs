import ErdosProblems.Erdos587.NVDevelopment

/-! # Extreme points of a cube fiber have no interior-supported kernel direction -/

open Filter
open scoped Topology

namespace Erdos587.CFP

theorem delta_extreme_cube_fiber_kernel_eq_zero {ι E : Type*} [Finite ι]
    [AddCommGroup E] [Module ℝ E] (L : (ι → ℝ) →ₗ[ℝ] E) (z : E)
    (β : ι → ℝ)
    (hβ : β ∈ (Set.Icc (0 : ι → ℝ) 1 ∩ {x | L x = z}).extremePoints ℝ)
    (γ : ι → ℝ) (hγ : L γ = 0)
    (hsupp : ∀ i, γ i ≠ 0 → 0 < β i ∧ β i < 1) : γ = 0 := by
  classical
  let S := Set.Icc (0 : ι → ℝ) 1 ∩ {x | L x = z}
  have hneigh (i : ι) : ∀ᶠ t : ℝ in 𝓝 0, β i + t * γ i ∈ Set.Icc (0 : ℝ) 1 := by
    by_cases hi : γ i = 0
    · filter_upwards [] with t
      simpa only [hi, mul_zero, add_zero, Set.mem_Icc, Pi.zero_apply, Pi.one_apply] using
        And.intro (hβ.1.1.1 i) (hβ.1.1.2 i)
    · have hbounds := hsupp i hi
      have hcont : ContinuousAt (fun t : ℝ => β i + t * γ i) 0 := by fun_prop
      have hopen : Set.Ioo (0 : ℝ) 1 ∈ 𝓝 (β i + 0 * γ i) := by
        simpa only [zero_mul, add_zero] using Ioo_mem_nhds hbounds.1 hbounds.2
      exact (hcont.eventually hopen).mono (fun _ ht => ⟨ht.1.le, ht.2.le⟩)
  have hall : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, β i + t * γ i ∈ Set.Icc (0 : ℝ) 1 :=
    eventually_all.mpr hneigh
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hall
  have hmem (t : ℝ) (ht : |t| < ε) : β + t • γ ∈ S := by
    have hh := hball (by simpa only [Real.dist_eq, sub_zero] using ht)
    refine ⟨⟨fun i => (hh i).1, fun i => (hh i).2⟩, ?_⟩
    change L (β + t • γ) = z
    rw [map_add, map_smul, hγ, smul_zero, add_zero]
    exact hβ.1.2
  have hhalf : |ε / 2| < ε := by rw [abs_of_pos (by positivity)]; linarith
  have hplus : β + (ε / 2) • γ ∈ S := hmem _ hhalf
  have hminus : β - (ε / 2) • γ ∈ S := by
    simpa only [neg_smul, sub_eq_add_neg] using
      hmem (-(ε / 2)) (by simpa only [abs_neg] using hhalf)
  have heq : β + (ε / 2) • γ = β :=
    hβ.2 hplus hminus (mem_openSegment_add_sub (𝕜 := ℝ) β ((ε / 2) • γ))
  funext i
  have hi := congrFun heq i
  change β i + (ε / 2) * γ i = β i at hi
  change γ i = 0
  nlinarith

theorem delta_exists_extreme_cube_fiber {ι : Type*} [Finite ι] {d : ℕ}
    (L : (ι → ℝ) →ₗ[ℝ] (Fin d → ℝ)) (α : ι → ℝ)
    (hα : α ∈ Set.Icc (0 : ι → ℝ) 1) :
    ∃ β : ι → ℝ, β ∈ (Set.Icc (0 : ι → ℝ) 1 ∩ {x | L x = L α}).extremePoints ℝ := by
  let _ := Fintype.ofFinite ι
  have hcompact : IsCompact (Set.Icc (0 : ι → ℝ) 1 ∩ {x | L x = L α}) :=
    isCompact_Icc.inter_right (isClosed_eq L.continuous_of_finiteDimensional continuous_const)
  exact hcompact.extremePoints_nonempty ⟨α, hα, rfl⟩

end Erdos587.CFP
