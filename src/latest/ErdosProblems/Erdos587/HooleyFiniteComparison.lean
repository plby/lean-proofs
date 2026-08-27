import ErdosProblems.Erdos587.HooleyCountComparison

/-! # Uniform log-log count comparison over a fixed finite family -/

open Filter
open scoped BigOperators SchwartzMap

namespace Erdos587

theorem exists_delta_finite_critical_count_comparison (F : Finset 𝓢(ℝ, ℂ))
    (g : 𝓢(ℝ, ℂ)) (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ f ∈ F, ∀ a b u v H t : ℕ, 0 < u → 0 < v → 0 < H → H ≤ v →
      a * u = b * v + 1 → b.Coprime u → u.Coprime v →
      T ^ (1 / 16 : ℝ) ≤ u → (u : ℝ) ≤ Real.sqrt T * T ^ (1 / 1000 : ℝ) →
      c₀ * T ^ (3 / 4 - 1 / 1000 : ℝ) ≤ v → (v : ℝ) ≤ T ^ (3 / 4 : ℝ) →
      Real.sqrt T * T ^ (-(1 / 1000 : ℝ)) ≤ H → (u : ℝ) * H ≤ T →
      let σ := ((v : ℝ) / H)⁻¹
      ‖weightedSquareCount f g a v t (Real.sqrt T) σ -
        alternativeSquareMain f g a u b v t (Real.sqrt T) σ‖ ≤
        C * Real.sqrt (Real.sqrt T) * (max 1 (Real.log (Real.log T))) ^ (9 / 2 : ℝ) := by
  classical
  choose C hC herror using (fun f : 𝓢(ℝ, ℂ) => exists_delta_critical_count_comparison f g c₀ hc₀)
  let K : ℝ := 1 + ∑ f ∈ F, C f
  have hK : 0 < K := by
    have hh := Finset.sum_nonneg (fun f (_ : f ∈ F) => (hC f).le)
    dsimp [K]
    linarith
  refine ⟨K, hK, ?_⟩
  have hall := (eventually_all_finset F).mpr (fun f _ => herror f)
  filter_upwards [hall] with T hT
  intro f hf a b u v H t hu hv hH hHv hab hb huv hu0 hu1 hv0 hv1 hH0 huH
  have hCf : C f ≤ K := by
    have hh := Finset.single_le_sum (s := F) (f := C) (fun f _ => (hC f).le) hf
    dsimp [K]
    linarith
  apply (hT f hf a b u v H t hu hv hH hHv hab hb huv hu0 hu1 hv0 hv1 hH0 huH).trans
  gcongr

end Erdos587
