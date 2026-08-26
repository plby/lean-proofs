import ErdosProblems.Erdos547.EmbeddingConstants

/-!
# Integral reservoir sizes with all rounding margins
-/

namespace Erdos547

structure ReservoirNumbers {a : ℝ} (k : EmbeddingConstants a) (m : ℕ) where
  q : ℕ
  main : ℕ
  volume : main + 2 * q = m
  main_pos : 0 < main
  main_lower : (1 - 2 * k.beta) * m ≤ (main : ℝ)
  main_half : (m : ℝ) / 2 ≤ main
  reservoir_lower : k.beta * m / 2 ≤ (q : ℝ)
  buffer : k.beta / 4 * m ≤ (q : ℝ) / 2
  main_typical : (m : ℝ) * k.epsilon ≤ main
  reservoir_typical : (m : ℝ) * k.epsilon ≤ q
  roots : 12 * k.epsilon * m ≤ (k.theta - k.epsilon) * q

theorem exists_reservoir_numbers {a : ℝ} (k : EmbeddingConstants a) (m : ℕ)
    (hm : 0 < m) (hlarge : 2 ≤ k.beta * m) : Nonempty (ReservoirNumbers k m) := by
  let q := Nat.floor (k.beta * m)
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hqUpper : (q : ℝ) ≤ k.beta * m := Nat.floor_le (by positivity)
  have hqLower : k.beta * m / 2 ≤ (q : ℝ) := by
    have hh : k.beta * m < (q : ℝ) + 1 := Nat.lt_floor_add_one _
    linarith only [hh, hlarge]
  have hbeta := mul_le_mul_of_nonneg_right k.beta_le hmR.le
  have hqHalf : 2 * (q : ℝ) ≤ (m : ℝ) / 2 := by linarith only [hqUpper, hbeta]
  have hqNat : 2 * q ≤ m := by
    exact_mod_cast (show 2 * (q : ℝ) ≤ (m : ℝ) by linarith only [hqHalf, hmR.le])
  let M := m - 2 * q
  have hMcast : (M : ℝ) = (m : ℝ) - 2 * q := by
    dsimp only [M]
    rw [Nat.cast_sub hqNat, Nat.cast_mul, Nat.cast_ofNat]
  have hMhalf : (m : ℝ) / 2 ≤ M := by rw [hMcast]; linarith only [hqHalf]
  have hMpos : 0 < M := by exact_mod_cast (show 0 < (M : ℝ) by linarith only [hMhalf, hmR])
  refine ⟨{
    q := q
    main := M
    volume := by dsimp only [M]; omega
    main_pos := hMpos
    main_lower := by rw [hMcast]; nlinarith only [hqUpper]
    main_half := hMhalf
    reservoir_lower := hqLower
    buffer := by linarith only [hqLower]
    main_typical := ?_
    reservoir_typical := ?_
    roots := ?_
  }⟩
  · have hh := mul_le_mul_of_nonneg_right k.epsilon_le hmR.le
    nlinarith only [hh, hMhalf]
  · have hh := mul_le_mul_of_nonneg_right k.buffer_margin hmR.le
    have hb := mul_nonneg k.beta_pos.le hmR.le
    nlinarith only [hh, hqLower, hb]
  · exact reservoir_neighbour_margin k.theta k.epsilon k.theta k.beta q m
      k.theta_pos.le k.beta_pos.le hmR.le le_rfl k.theta_margin hqLower k.root_margin

theorem ReservoirNumbers.seeds_fit {a : ℝ} {k : EmbeddingConstants a} {m : ℕ}
    (Q : ReservoirNumbers k m) (K : ℕ) (hK : (K : ℝ) ≤ k.epsilon * m) :
    2 * K ≤ Q.q := by
  have hh := mul_le_mul_of_nonneg_right k.buffer_margin (show 0 ≤ (m : ℝ) by positivity)
  have hq := Q.reservoir_lower
  exact_mod_cast (show 2 * (K : ℝ) ≤ (Q.q : ℝ) by nlinarith only [hK, hh, hq])

end Erdos547

#print axioms Erdos547.exists_reservoir_numbers
