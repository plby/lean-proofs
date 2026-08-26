import ErdosProblems.Erdos633.EulerParameters

/-!
# The successor pair in the two Euler descents

Both parametrizations preserve positivity, coprimality, the exclusion of
three, and all three square conditions. The denominator divisibility is
proved from the equations rather than assumed.
-/

namespace Erdos633

structure EulerDescentData (ε u v : ℤ) where
  m : ℤ
  n : ℤ
  U : ℤ
  V : ℤ
  n_pos : 0 < n
  U_pos : 0 < U
  V_pos : 0 < V
  coprime_mn : IsCoprime m n
  coprime_UV : IsCoprime U V
  U_three : ¬ (3 : ℤ) ∣ U
  U_square : IsSquare U
  V_square : IsSquare V
  quadratic_square : IsSquare (eulerQuadratic ε U V)
  first_u : u = m ^ 2 - 3 * n ^ 2
  first_v : v = n * (3 * ε * n - 2 * m)
  second_eq : 2 * m * U * V = -n * (U ^ 2 + 3 * V ^ 2)
  product_dvd : U * V ∣ n

theorem exists_euler_descent_data (ε u v : ℤ) (hε : ε ^ 2 = 1)
    (hu : 0 < u) (hv : 0 < v) (huv : IsCoprime u v)
    (hu3 : ¬ (3 : ℤ) ∣ u) (husq : IsSquare u) (hvsq : IsSquare v)
    (hQ : IsSquare (eulerQuadratic ε u v)) : Nonempty (EulerDescentData ε u v) := by
  obtain ⟨m, n, hn, hmn, hm3, hu', hv'⟩ :=
    euler_first_parameters ε u v hε hu hv huv hu3 husq hQ
  obtain ⟨U, V, hV, hUV, hU3, hsecond⟩ :=
    euler_second_parameters m n hn hm3 (hu' ▸ husq)
  have hbalance : v * (U * V) = n ^ 2 * eulerQuadratic ε U V := by
    dsimp [eulerQuadratic]
    linear_combination U * V * hv' - n * hsecond
  have hQpos := eulerQuadratic_pos ε U V hε hV
  have hprod : 0 < v * (U * V) := by
    rw [hbalance]
    exact mul_pos (sq_pos_of_pos hn) hQpos
  have hUVpos : 0 < U * V := pos_of_mul_pos_right hprod hv.le
  have hU : 0 < U := pos_of_mul_pos_left hUVpos hV.le
  have hP : IsSquare (U * V * eulerQuadratic ε U V) := by
    obtain ⟨k, hk⟩ := hvsq
    apply int_isSquare_of_sq_mul n _ (ne_of_gt hn)
    refine ⟨k * (U * V), ?_⟩
    linear_combination -(U * V) * hbalance + (U * V) ^ 2 * hk
  obtain ⟨hUQ, hVQ⟩ := eulerQuadratic_coprime ε U V hUV hU3
  have hUVQ := hUQ.mul_left hVQ
  obtain ⟨hUVsq, hQsq⟩ := int_coprime_square_factors (U * V) (eulerQuadratic ε U V)
    hUVpos.le hQpos.le hUVQ hP
  obtain ⟨hUsq, hVsq⟩ := int_coprime_square_factors U V hU.le hV.le hUV hUVsq
  have hndvd : U * V ∣ n := by
    apply hUVQ.dvd_of_dvd_mul_right
    refine ⟨3 * ε * n - 2 * m, ?_⟩
    apply mul_left_cancel₀ (ne_of_gt hn)
    linear_combination -hbalance + (U * V) * hv'
  exact ⟨⟨m, n, U, V, hn, hU, hV, hmn, hUV, hU3, hUsq, hVsq, hQsq,
    hu', hv', hsecond, hndvd⟩⟩

theorem EulerDescentData.balance {ε u v : ℤ} (D : EulerDescentData ε u v) :
    v * (D.U * D.V) = D.n ^ 2 * eulerQuadratic ε D.U D.V := by
  dsimp [eulerQuadratic]
  linear_combination D.U * D.V * D.first_v - D.n * D.second_eq

theorem EulerDescentData.V_le_n {ε u v : ℤ} (D : EulerDescentData ε u v) :
    D.V ≤ D.n := by
  have h := Int.le_of_dvd D.n_pos D.product_dvd
  have hU : 1 ≤ D.U := by have := D.U_pos; omega
  nlinarith only [h, hU, D.V_pos]

theorem EulerDescentData.n_le_v {ε u v : ℤ} (D : EulerDescentData ε u v)
    (hv : 0 < v) : D.n ≤ v :=
  Int.le_of_dvd hv ⟨3 * ε * D.n - 2 * D.m, D.first_v⟩

theorem EulerDescentData.plus_strict {u v : ℤ} (D : EulerDescentData 1 u v)
    (hu : 0 < u) (hv : 0 < v) : D.V < v := by
  have hv' : v = D.n * (3 * D.n - 2 * D.m) := by
    simpa only [mul_one] using D.first_v
  have hB : 0 < 3 * D.n - 2 * D.m := by
    have h : 0 < D.n * (3 * D.n - 2 * D.m) := by rw [← hv']; exact hv
    exact pos_of_mul_pos_right h D.n_pos.le
  have hm : D.m < 0 := by
    by_contra hm
    have hm0 : 0 ≤ D.m := by omega
    have hplus : 0 < 3 * D.n + 2 * D.m := by have := D.n_pos; omega
    have hp := mul_pos hB hplus
    nlinarith only [hp, D.first_u, hu, sq_nonneg D.n]
  have hB1 : 1 < 3 * D.n - 2 * D.m := by have := D.n_pos; omega
  have hnv : D.n < v := by
    calc
      D.n < D.n * (3 * D.n - 2 * D.m) := by
        simpa only [mul_one] using mul_lt_mul_of_pos_left hB1 D.n_pos
      _ = v := hv'.symm
  exact lt_of_le_of_lt D.V_le_n hnv

theorem EulerDescentData.minus_preimage_one {u v : ℤ} (D : EulerDescentData (-1) u v)
    (hU : D.U = 1) (hV : D.V = 1) : u = 1 ∧ v = 1 := by
  have hm : D.m = -2 * D.n := by
    have h := D.second_eq
    rw [hU, hV] at h
    nlinarith only [h]
  have hunit : IsUnit D.n := D.coprime_mn.symm.isUnit_of_dvd ⟨-2, by rw [hm]; ring⟩
  have hn : D.n = 1 := by
    rcases Int.isUnit_iff.mp hunit with h | h
    · exact h
    · have := D.n_pos; omega
  have hmu : D.m = -2 := by rw [hm, hn]; ring
  constructor
  · have h := D.first_u
    norm_num [hn, hmu] at h
    exact h
  · have h := D.first_v
    norm_num [hn, hmu] at h
    exact h

theorem EulerDescentData.minus_eq_one_of_not_strict {u v : ℤ}
    (D : EulerDescentData (-1) u v) (hv : 0 < v) (hnot : ¬ D.V < v) :
    u = 1 ∧ v = 1 := by
  have hVv : D.V = v := le_antisymm (D.V_le_n.trans (D.n_le_v hv)) (by omega)
  have hUVle : D.U * D.V ≤ v := (Int.le_of_dvd D.n_pos D.product_dvd).trans (D.n_le_v hv)
  have hU : D.U = 1 := by
    have hUle : D.U ≤ 1 := by
      apply le_of_mul_le_mul_right _ D.V_pos
      simpa only [one_mul, hVv] using hUVle
    have := D.U_pos
    omega
  have hn : D.n = D.V := by
    have h₁ := D.V_le_n
    have h₂ := D.n_le_v hv
    omega
  have hb := D.balance
  simp only [hU, hn, ← hVv, one_mul] at hb
  have hQ : eulerQuadratic (-1) 1 D.V = 1 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 (ne_of_gt D.V_pos))
    nlinarith only [hb]
  have hV : D.V = 1 := by
    have hV1 : 1 ≤ D.V := by have := D.V_pos; omega
    dsimp [eulerQuadratic] at hQ
    nlinarith only [hQ, hV1]
  exact D.minus_preimage_one hU hV

end Erdos633
