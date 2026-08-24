import ErdosProblems.Erdos587.InversePhaseGeometry

/-! A first-derivative bound in its discrete increment form. -/

open scoped BigOperators

namespace Erdos587

theorem norm_phase_sum_le_of_monotone_unit_increments (f : ℕ → ℝ) (N : ℕ) {δ : ℝ}
    (hδ : 0 < δ)
    (hlo : ∀ n ≤ N, δ ≤ f (n + 1) - f n)
    (hhi : ∀ n ≤ N, f (n + 1) - f n ≤ 1 - δ)
    (hmono : ∀ n < N, f (n + 1) - f n ≤ f (n + 2) - f (n + 1)) :
    ‖∑ n ∈ Finset.range (N + 1), phase (f n)‖ ≤ 1 / δ := by
  let b (n : ℕ) := (phase (f (n + 1) - f n) - 1)⁻¹
  have hbound (n : ℕ) (hn : n ≤ N) :
      phase (f (n + 1) - f n) ≠ 1 ∧ ‖b n‖ ≤ 1 / (4 * δ) :=
    inverse_phase_increment_norm_bound hδ (hlo n hn) (hhi n hn)
  have hmem (n : ℕ) (hn : n ≤ N) : f (n + 1) - f n ∈ Set.Ioo (0 : ℝ) 1 := by
    exact ⟨hδ.trans_le (hlo n hn), by linarith [hhi n hn]⟩
  have hre (n : ℕ) (hn : n ≤ N) : (b n).re = (b 0).re := by
    dsimp [b]
    rw [inverse_unit_sub_one_re (norm_phase _) (hbound n hn).1,
      inverse_unit_sub_one_re (norm_phase _) (hbound 0 (by omega)).1]
  have him (n : ℕ) (hn : n < N) : (b n).im ≤ (b (n + 1)).im := by
    exact monotoneOn_inverse_phase_increment_im (hmem n hn.le) (hmem (n + 1) (by omega))
      (by simpa only [Nat.add_assoc] using hmono n hn)
  have hh := norm_sum_le_of_monotone_inverse_differences (fun n => phase (f n)) b N
    (fun n hn => inverse_phase_increment_recurrence f n (hbound n hn).1)
    (fun n hn => (norm_phase _).le) hre him (hbound 0 (by omega)).2 (hbound N le_rfl).2
  calc
    _ ≤ 4 * (1 / (4 * δ)) := hh
    _ = 1 / δ := by ring

lemma phase_sub_intCast (x : ℝ) (k : ℤ) : phase (x - k) = phase x := by
  rw [phase_sub]
  have hk : phase (k : ℝ) = 1 := fourierChar_intCast k
  rw [hk, map_one, mul_one]

lemma phase_sub_integer_linear (f : ℕ → ℝ) (k : ℤ) (n : ℕ) :
    phase (f n - (k : ℝ) * n) = phase (f n) := by
  have hcast : (k : ℝ) * (n : ℝ) = ((k * (n : ℤ) : ℤ) : ℝ) := by push_cast; rfl
  rw [hcast, phase_sub_intCast]

theorem norm_phase_sum_le_of_monotone_increments (f : ℕ → ℝ) (N : ℕ) (k : ℤ) {δ : ℝ}
    (hδ : 0 < δ)
    (hlo : ∀ n ≤ N, (k : ℝ) + δ ≤ f (n + 1) - f n)
    (hhi : ∀ n ≤ N, f (n + 1) - f n ≤ (k : ℝ) + 1 - δ)
    (hmono : ∀ n < N, f (n + 1) - f n ≤ f (n + 2) - f (n + 1)) :
    ‖∑ n ∈ Finset.range (N + 1), phase (f n)‖ ≤ 1 / δ := by
  let g (n : ℕ) := f n - (k : ℝ) * n
  have hinc (n : ℕ) : g (n + 1) - g n = f (n + 1) - f n - k := by
    dsimp [g]
    push_cast
    ring
  have hh := norm_phase_sum_le_of_monotone_unit_increments g N hδ
    (fun n hn => by rw [hinc]; linarith [hlo n hn])
    (fun n hn => by rw [hinc]; linarith [hhi n hn])
    (fun n hn => by rw [hinc, hinc]; simpa only [Nat.add_assoc] using sub_le_sub_right (hmono n hn) k)
  simpa only [g, phase_sub_integer_linear] using hh

end Erdos587
