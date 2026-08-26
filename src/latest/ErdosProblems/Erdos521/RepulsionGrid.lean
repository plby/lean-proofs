/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
A quantitative repulsion bound from the proved small-ball and grid estimates.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.PolynomialDerivatives
import ErdosProblems.Erdos521.IntervalGrid
import ErdosProblems.Erdos521.RepulsionParameters
import ErdosProblems.Erdos521.RepulsionSmallBall

namespace Erdos521

open MeasureTheory Filter
open scoped BigOperators

def smallValueDerivativeEvent (n : ℕ) (l u η : ℝ) : Set (ℕ → ℝ) :=
  {ε | ∃ x ∈ Set.Icc l u, |(polynomial ε n).eval x| ≤ η ∧
    |(polynomial ε n).derivative.eval x| ≤ η}

theorem smallValueDerivative_grid_probability (n j : ℕ) (hn : 1 < n) {C : ℝ}
    (hC : 0 < C) (hj : 12 * (j : ℝ) ≤ C * Real.log n)
    (hinterval : 9 / 10 ≤ endpointCenter C n) :
    sequenceLaw.real (smallValueDerivativeEvent n (9 / 10) (endpointCenter C n) (repulsionThreshold j)) ≤
      (repulsionMesh n j + 1 : ℕ) * (1 / 4 : ℝ) ^ (2 * j) := by
  let M := repulsionMesh n j
  let b := endpointCenter C n
  let y := intervalGrid (9 / 10) b M
  let E := fun i : Fin (M + 1) ↦ {ε : ℕ → ℝ |
    |powerSum ε (n + 1) (y i)| ≤ (1 / 4) * (1 / 8 : ℝ) ^ (2 * j)}
  have hM : 0 < M := repulsionMesh_pos n j
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  have hb : b < 1 := sub_lt_self _ (div_pos (mul_pos hC hlog) hn₀)
  have hy (i : Fin (M + 1)) : y i ∈ Set.Icc (9 / 10) b := intervalGrid_mem hinterval M i
  have hsub : ∀ᵐ ε ∂sequenceLaw,
      ε ∈ smallValueDerivativeEvent n (9 / 10) b (repulsionThreshold j) → ε ∈ ⋃ i, E i := by
    filter_upwards [ae_sequence_signs] with ε hε hsmall
    obtain ⟨x, hx, hvalue, hderiv⟩ := hsmall
    obtain ⟨i, hdist⟩ := intervalGrid_covers (by linarith : b - 9 / 10 ≤ 1) M hM hx
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    have hsign (k : ℕ) : |ε k| ≤ 1 := by rcases hε k with h | h <;> simp [h]
    have hx' : x ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith [hx.1], hx.2.trans hb.le⟩
    have hy' : y i ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith [(hy i).1], (hy i).2.trans hb.le⟩
    have hnear := polynomial_value_le_of_small_value_derivative ε hsign n hx' hy'
      (repulsionThreshold_pos j).le (by positivity : 0 ≤ (M : ℝ)⁻¹) hdist hvalue hderiv
    have hgrid := hnear.trans (repulsion_grid_error_le n j)
    change |powerSum ε (n + 1) (y i)| ≤ _
    simpa only [polynomial_eval] using hgrid
  have hmono : sequenceLaw.real
      (smallValueDerivativeEvent n (9 / 10) b (repulsionThreshold j)) ≤ sequenceLaw.real (⋃ i, E i) :=
    ENNReal.toReal_mono (measure_ne_top sequenceLaw _) (measure_mono_ae hsub)
  have hprob (i : Fin (M + 1)) : sequenceLaw.real (E i) ≤ (1 / 4 : ℝ) ^ (2 * j) := by
    have hj' : 6 * ((2 * j : ℕ) : ℝ) ≤ C * Real.log n := by push_cast; nlinarith
    have h := powerSum_smallBall_repulsion_scale n (2 * j) hn (x := y i) (z := 0) hC
      hj' (hy i).1 (hy i).2
    simpa only [sub_zero] using h
  apply (hmono.trans (measureReal_iUnion_fintype_le E)).trans
  calc
    (∑ i : Fin (M + 1), sequenceLaw.real (E i)) ≤ ∑ _i : Fin (M + 1), (1 / 4 : ℝ) ^ (2 * j) :=
      Finset.sum_le_sum (fun i _ ↦ hprob i)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; rfl

end Erdos521
