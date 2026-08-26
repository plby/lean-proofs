import ErdosProblems.Erdos633.EulerQuadratic

/-!
# The coprime factors of the two cubic equations

The case in which three divides the shifted numerator is handled explicitly.
After removing a factor of nine, the same quadratic descent applies with
the two parameters interchanged.
-/

namespace Erdos633

theorem euler_product_square_factors (ε u v : ℤ) (hε : ε ^ 2 = 1)
    (hu : 0 < u) (hv : 0 < v) (huv : IsCoprime u v) (hu3 : ¬ (3 : ℤ) ∣ u)
    (hsq : IsSquare (u * v * eulerQuadratic ε u v)) :
    IsSquare u ∧ IsSquare v ∧ IsSquare (eulerQuadratic ε u v) := by
  obtain ⟨hUQ, hVQ⟩ := eulerQuadratic_coprime ε u v huv hu3
  obtain ⟨hUV, hQ⟩ := int_coprime_square_factors (u * v) (eulerQuadratic ε u v)
    (mul_pos hu hv).le (eulerQuadratic_pos ε u v hε hv).le (hUQ.mul_left hVQ) hsq
  obtain ⟨hU, hV⟩ := int_coprime_square_factors u v hu.le hv.le huv hUV
  exact ⟨hU, hV, hQ⟩

theorem euler_three_divisible_reduction (ε c n : ℤ) (hε : ε ^ 2 = 1)
    (hc : 0 < c) (hn : 0 < n) (hcn : IsCoprime c n) (hc3 : (3 : ℤ) ∣ c)
    (hsq : IsSquare (c * n * eulerQuadratic ε c n)) :
    ∃ d : ℤ, 0 < d ∧ c = 3 * d ∧ IsCoprime n d ∧ ¬ (3 : ℤ) ∣ n ∧
      IsSquare n ∧ IsSquare d ∧ IsSquare (eulerQuadratic ε n d) := by
  obtain ⟨d, hcd⟩ := hc3
  have hd : 0 < d := by nlinarith only [hc, hcd]
  have hnd : IsCoprime n d := hcn.symm.of_isCoprime_of_dvd_right ⟨3, by rw [hcd]; ring⟩
  have hn3 : ¬ (3 : ℤ) ∣ n := by
    intro hn3
    have hunit := hcn.isUnit_of_dvd' (show (3 : ℤ) ∣ c from ⟨d, hcd⟩) hn3
    norm_num [Int.isUnit_iff] at hunit
  have hs : IsSquare (n * d * eulerQuadratic ε n d) := by
    apply int_isSquare_of_sq_mul 3 _ (by norm_num)
    rw [show (3 : ℤ) ^ 2 * (n * d * eulerQuadratic ε n d) =
      c * n * eulerQuadratic ε c n by rw [hcd]; dsimp [eulerQuadratic]; ring]
    exact hsq
  obtain ⟨hN, hD, hQ⟩ := euler_product_square_factors ε n d hε hn hd hnd hn3 hs
  exact ⟨d, hd, hcd, hnd, hn3, hN, hD, hQ⟩

theorem euler_plus_product_impossible (c n : ℤ) (hc : 0 < c) (hn : 0 < n)
    (hcn : IsCoprime c n) (hsq : IsSquare (c * n * eulerQuadratic 1 c n)) : False := by
  by_cases hc3 : (3 : ℤ) ∣ c
  · obtain ⟨d, hd, _, hnd, hn3, hN, hD, hQ⟩ :=
      euler_three_divisible_reduction 1 c n (by norm_num) hc hn hcn hc3 hsq
    exact euler_plus_no_solution n d hn hd hnd hn3 hN hD hQ
  · obtain ⟨hC, hN, hQ⟩ := euler_product_square_factors 1 c n
      (by norm_num) hc hn hcn hc3 hsq
    exact euler_plus_no_solution c n hc hn hcn hc3 hC hN hQ

theorem euler_minus_product_cases (c n : ℤ) (hc : 0 < c) (hn : 0 < n)
    (hcn : IsCoprime c n) (hsq : IsSquare (c * n * eulerQuadratic (-1) c n)) :
    (c = 1 ∧ n = 1) ∨ (c = 3 ∧ n = 1) := by
  by_cases hc3 : (3 : ℤ) ∣ c
  · obtain ⟨d, hd, hcd, hnd, hn3, hN, hD, hQ⟩ :=
      euler_three_divisible_reduction (-1) c n (by norm_num) hc hn hcn hc3 hsq
    obtain ⟨hn1, hd1⟩ := euler_minus_only_one n d hn hd hnd hn3 hN hD hQ
    right
    exact ⟨by rw [hcd, hd1]; norm_num, hn1⟩
  · obtain ⟨hC, hN, hQ⟩ := euler_product_square_factors (-1) c n
      (by norm_num) hc hn hcn hc3 hsq
    exact Or.inl (euler_minus_only_one c n hc hn hcn hc3 hC hN hQ)

end Erdos633
