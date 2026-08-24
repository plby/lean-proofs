import ErdosProblems.Erdos587.CountComparison

/-! Uniform critical count comparison for a fixed finite family of root weights. -/

open Filter
open scoped BigOperators SchwartzMap

namespace Erdos587

theorem exists_finite_critical_count_comparison (F : Finset 𝓢(ℝ, ℂ))
    (g : 𝓢(ℝ, ℂ)) (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∃ C : ℝ, 0 < C ∧ ∃ O : ℕ, 0 < O ∧ ∀ᶠ T : ℝ in atTop,
      ∀ f ∈ F, ∀ a b u v H t : ℕ, 0 < u → 0 < v → 0 < H → H ≤ v →
        a * u = b * v + 1 → b.Coprime u → u.Coprime v →
        T ^ (1 / 16 : ℝ) ≤ u → (u : ℝ) ≤ Real.sqrt T * T ^ (1 / 1000 : ℝ) →
        c₀ * T ^ (3 / 4 - 1 / 1000 : ℝ) ≤ v → (v : ℝ) ≤ T ^ (3 / 4 : ℝ) →
        Real.sqrt T * T ^ (-(1 / 1000 : ℝ)) ≤ H → (u : ℝ) * H ≤ T →
        let σ := ((v : ℝ) / H)⁻¹
        ‖weightedSquareCount f g a v t (Real.sqrt T) σ -
          alternativeSquareMain f g a u b v t (Real.sqrt T) σ‖ ≤
          C * Real.sqrt (Real.sqrt T) * (1 + Real.log T) ^ O := by
  classical
  choose C hC O hO herror using (fun f : 𝓢(ℝ, ℂ) => exists_critical_count_comparison f g c₀ hc₀)
  let K : ℝ := 1 + ∑ f ∈ F, C f
  let D : ℕ := 1 + ∑ f ∈ F, O f
  have hK : 0 < K := by
    have hh := Finset.sum_nonneg (fun f (_ : f ∈ F) => (hC f).le)
    dsimp [K]
    linarith
  have hD : 0 < D := by dsimp [D]; omega
  refine ⟨K, hK, D, hD, ?_⟩
  have hall := (eventually_all_finset F).mpr (fun f _ => herror f)
  filter_upwards [hall, eventually_ge_atTop (1 : ℝ)] with T hT hT1
  intro f hf a b u v H t hu hv hH hHv hab hb huv hu0 hu1 hv0 hv1 hH0 huH
  have hCf : C f ≤ K := by
    have hh := Finset.single_le_sum (fun f (_ : f ∈ F) => (hC f).le) hf
    dsimp [K]
    linarith
  have hOf : O f ≤ D := by
    have hh := Finset.single_le_sum (fun f (_ : f ∈ F) => Nat.zero_le (O f)) hf
    dsimp [D]
    omega
  have hΛ : 1 ≤ 1 + Real.log T := by have := Real.log_nonneg hT1; linarith
  have hh := hT f hf a b u v H t hu hv hH hHv hab hb huv hu0 hu1 hv0 hv1 hH0 huH
  apply hh.trans
  exact mul_le_mul (mul_le_mul_of_nonneg_right hCf (Real.sqrt_nonneg _))
    (pow_le_pow_right₀ hΛ hOf) (pow_nonneg (by linarith) _) (by positivity)

end Erdos587
