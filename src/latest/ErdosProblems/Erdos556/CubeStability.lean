import ErdosProblems.Erdos556.ApproxCubeWeights
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecificLimits.Basic

/-! Quantitative stability of the finite cube-profile inequality. -/

namespace Erdos556

open Finset Filter
open scoped Topology

theorem exists_cube_stability_and_energy_tolerance (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w : CubeProfile → ℝ, ApproxCubeWeight w δ →
      ∃ v : CubeProfile → ℝ, IsCubeWeight v ∧ IsCubeTiling v ∧
        (∀ p, |w p - v p| < η) ∧ |cubeEnergy w| < η := by
  classical
  by_contra hn
  have hbad (δ : ℝ) (hδ : 0 < δ) : ∃ w : CubeProfile → ℝ, ApproxCubeWeight w δ ∧
      ¬ ∃ v : CubeProfile → ℝ, IsCubeWeight v ∧ IsCubeTiling v ∧
        (∀ p, |w p - v p| < η) ∧ |cubeEnergy w| < η := by
    by_contra h
    apply hn
    refine ⟨δ, hδ, ?_⟩
    intro w hw
    by_contra hv
    exact h ⟨w, hw, hv⟩
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hεpos (n : ℕ) : 0 < ε n := by dsimp only [ε]; positivity
  have hεle (n : ℕ) : ε n ≤ 1 := by
    dsimp only [ε]
    apply (div_le_one (by positivity : 0 < (n : ℝ) + 1)).mpr
    have hn : 0 ≤ (n : ℝ) := by positivity
    linarith
  choose w hw hfar using fun n => hbad (ε n) (hεpos n)
  let K : Set (CubeProfile → ℝ) := Set.Icc (fun _ => 0) (fun _ => 5)
  have hcompact : IsCompact K := isCompact_Icc
  have hwK (n : ℕ) : w n ∈ K :=
    ⟨(hw n).nonneg, fun p => (hw n).le_five (hεle n) p⟩
  obtain ⟨v, hvK, φ, hφ, hv⟩ := hcompact.tendsto_subseq hwK
  have hε : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hlimε : Tendsto (ε ∘ φ) atTop (𝓝 0) := hε.comp hφ.tendsto_atTop
  obtain ⟨hvweight, hvtiling⟩ := approximate_cube_limit (fun n => hw (φ n)) hlimε hv
  have heach (p : CubeProfile) : ∀ᶠ n in atTop, |w (φ n) p - v p| < η := by
    have hp := (tendsto_pi_nhds.mp hv) p
    simpa only [Real.dist_eq, Function.comp_apply] using (Metric.tendsto_nhds.mp hp) η hη
  have hall : ∀ᶠ n in atTop, ∀ p, |w (φ n) p - v p| < η := Filter.eventually_all.mpr heach
  have henergy : Tendsto (fun n => cubeEnergy (w (φ n))) atTop (𝓝 0) := by
    have hh := (continuous_cubeEnergy.tendsto v).comp hv
    rwa [hvtiling.energy_eq_zero hvweight] at hh
  have hevent : ∀ᶠ n in atTop, |cubeEnergy (w (φ n))| < η := by
    simpa only [Real.dist_eq, sub_zero] using (Metric.tendsto_nhds.mp henergy) η hη
  obtain ⟨n, hn, he⟩ := (hall.and hevent).exists
  exact hfar (φ n) ⟨v, hvweight, hvtiling, hn, he⟩

theorem exists_cube_stability_tolerance (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w : CubeProfile → ℝ, ApproxCubeWeight w δ →
      ∃ v : CubeProfile → ℝ, IsCubeWeight v ∧ IsCubeTiling v ∧ ∀ p, |w p - v p| < η := by
  obtain ⟨δ, hδ, h⟩ := exists_cube_stability_and_energy_tolerance η hη
  refine ⟨δ, hδ, ?_⟩
  intro w hw
  obtain ⟨v, hv, ht, hclose, _⟩ := h w hw
  exact ⟨v, hv, ht, hclose⟩

#print axioms exists_cube_stability_tolerance
#print axioms exists_cube_stability_and_energy_tolerance

end Erdos556
