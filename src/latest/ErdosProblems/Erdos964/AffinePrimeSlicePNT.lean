import ErdosProblems.Erdos964.PrimeIntervalWindow

/-!
# Uniform prime-counting asymptotics for the exact affine slices

The integer endpoints are retained exactly. Their real difference is
`m*N/p`, so no floor error remains in the main term.
-/

namespace Erdos964

theorem exists_affine_primeInterval_error (m c : ℕ) (hm : 1 ≤ m) (hc : 1 ≤ c)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ Y₀ : ℝ, 2 ≤ Y₀ ∧ ∀ N p : ℕ, 1 ≤ N → 0 < p → Y₀ ≤ (N : ℝ) / p →
      |(((Finset.Ioc ((m * N + c - 1) / p) ((m * (2 * N) + c - 1) / p)).filter
          Nat.Prime).card : ℝ) - (m : ℝ) * ((N : ℝ) / p) / Real.log ((N : ℝ) / p)| ≤
        ε * (((N : ℝ) / p) / Real.log ((N : ℝ) / p)) := by
  let B : ℝ := (2 * m + c : ℕ)
  have hB : 1 ≤ B := by dsimp only [B]; exact_mod_cast (show 1 ≤ 2 * m + c by omega)
  obtain ⟨Y₀, hY₀, herror⟩ := exists_primeInterval_multiplicative_window_error B hB ε hε
  refine ⟨Y₀, hY₀, ?_⟩
  intro N p hN hp hY
  let x := m * N + c - 1
  let z := m * (2 * N) + c - 1
  let Y := (N : ℝ) / p
  let u := (x : ℝ) / p
  let v := (z : ℝ) / p
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hmN : N ≤ m * N := Nat.le_mul_of_pos_left N hm
  have hNx : N ≤ x := by dsimp only [x]; omega
  have hmxz : m * N ≤ m * (2 * N) := Nat.mul_le_mul_left m (by omega)
  have hxz : x ≤ z := by dsimp only [x, z]; omega
  have hcN : c ≤ c * N := Nat.le_mul_of_pos_right c hN
  have hzB : z ≤ (2 * m + c) * N := by
    calc
      z ≤ m * (2 * N) + c := Nat.sub_le _ _
      _ ≤ (2 * m + c) * N := by nlinarith
  have hYu : Y ≤ u := div_le_div_of_nonneg_right (by exact_mod_cast hNx) hpR.le
  have huv : u ≤ v := div_le_div_of_nonneg_right (by exact_mod_cast hxz) hpR.le
  have hvB : v ≤ B * Y := by
    dsimp only [v, B, Y]
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hzB) hpR.le
  have hxpos : 1 ≤ m * N + c := by omega
  have hzpos : 1 ≤ m * (2 * N) + c := by omega
  have hdiff : v - u = (m : ℝ) * Y := by
    dsimp only [v, u, z, x, Y]
    rw [Nat.cast_sub hzpos, Nat.cast_sub hxpos]
    push_cast
    ring
  have hu : ⌊u⌋₊ = x / p := by simp only [u, Nat.floor_div_natCast, Nat.floor_natCast]
  have hv : ⌊v⌋₊ = z / p := by simp only [v, Nat.floor_div_natCast, Nat.floor_natCast]
  have h := herror Y u v hY hYu huv hvB
  rw [hu, hv, hdiff] at h
  exact h

theorem exists_affine_primeSlice_error (m c : ℕ) (hm : 1 ≤ m) (hc : 1 ≤ c)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ Y₀ : ℝ, 2 ≤ Y₀ ∧ ∀ N p L U : ℕ, 1 ≤ N → 0 < p → Y₀ ≤ (N : ℝ) / p →
      p * L ≤ m * N + c - 1 → m * (2 * N) + c - 1 ≤ p * U →
      |((primeSlice ((Finset.Ioc L U).filter Nat.Prime) p
          (m * N + c - 1) (m * (2 * N) + c - 1)).card : ℝ) -
        (m : ℝ) * ((N : ℝ) / p) / Real.log ((N : ℝ) / p)| ≤
        ε * (((N : ℝ) / p) / Real.log ((N : ℝ) / p)) := by
  obtain ⟨Y₀, hY₀, herror⟩ := exists_affine_primeInterval_error m c hm hc ε hε
  refine ⟨Y₀, hY₀, ?_⟩
  intro N p L U hN hp hY hlo hhi
  rw [primeSlice_eq_primeInterval L U p _ _ hp hlo hhi]
  exact herror N p hN hp hY

end Erdos964
