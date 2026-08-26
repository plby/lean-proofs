import ErdosProblems.Erdos633.EulerStep

/-!
# Completion of the two Euler descents

Strong induction on the positive second coordinate excludes the plus sign
and leaves only `(1, 1)` for the minus sign. No rational-point theorem or
elliptic-curve computation is assumed.
-/

namespace Erdos633

theorem euler_plus_no_solution_nat (u : ℤ) (v : ℕ)
    (hu : 0 < u) (hv : 0 < (v : ℤ)) (huv : IsCoprime u (v : ℤ))
    (hu3 : ¬ (3 : ℤ) ∣ u) (husq : IsSquare u) (hvsq : IsSquare (v : ℤ))
    (hQ : IsSquare (eulerQuadratic 1 u v)) : False := by
  induction v using Nat.strong_induction_on generalizing u with
  | h v ih =>
    obtain ⟨D⟩ := exists_euler_descent_data 1 u v (by norm_num) hu hv huv hu3 husq hvsq hQ
    have hcast : (D.V.natAbs : ℤ) = D.V := Int.natAbs_of_nonneg D.V_pos.le
    have hlt : D.V.natAbs < v := by
      have h : (D.V.natAbs : ℤ) < v := by
        simpa only [hcast] using D.plus_strict hu hv
      exact_mod_cast h
    apply ih D.V.natAbs hlt D.U D.U_pos
    · simpa only [hcast] using D.V_pos
    · simpa only [hcast] using D.coprime_UV
    · exact D.U_three
    · exact D.U_square
    · simpa only [hcast] using D.V_square
    · simpa only [hcast] using D.quadratic_square

theorem euler_minus_only_one_nat (u : ℤ) (v : ℕ)
    (hu : 0 < u) (hv : 0 < (v : ℤ)) (huv : IsCoprime u (v : ℤ))
    (hu3 : ¬ (3 : ℤ) ∣ u) (husq : IsSquare u) (hvsq : IsSquare (v : ℤ))
    (hQ : IsSquare (eulerQuadratic (-1) u v)) : u = 1 ∧ (v : ℤ) = 1 := by
  induction v using Nat.strong_induction_on generalizing u with
  | h v ih =>
    obtain ⟨D⟩ := exists_euler_descent_data (-1) u v (by norm_num) hu hv huv hu3 husq hvsq hQ
    by_cases hstrict : D.V < v
    · have hcast : (D.V.natAbs : ℤ) = D.V := Int.natAbs_of_nonneg D.V_pos.le
      have hlt : D.V.natAbs < v := by
        have h : (D.V.natAbs : ℤ) < v := by simpa only [hcast] using hstrict
        exact_mod_cast h
      have hone : D.U = 1 ∧ (D.V.natAbs : ℤ) = 1 := by
        apply ih D.V.natAbs hlt D.U D.U_pos
        · simpa only [hcast] using D.V_pos
        · simpa only [hcast] using D.coprime_UV
        · exact D.U_three
        · exact D.U_square
        · simpa only [hcast] using D.V_square
        · simpa only [hcast] using D.quadratic_square
      exact D.minus_preimage_one hone.1 (by simpa only [hcast] using hone.2)
    · exact D.minus_eq_one_of_not_strict hv hstrict

theorem euler_plus_no_solution (u v : ℤ)
    (hu : 0 < u) (hv : 0 < v) (huv : IsCoprime u v)
    (hu3 : ¬ (3 : ℤ) ∣ u) (husq : IsSquare u) (hvsq : IsSquare v)
    (hQ : IsSquare (eulerQuadratic 1 u v)) : False := by
  lift v to ℕ using hv.le
  exact euler_plus_no_solution_nat u v hu hv huv hu3 husq hvsq hQ

theorem euler_minus_only_one (u v : ℤ)
    (hu : 0 < u) (hv : 0 < v) (huv : IsCoprime u v)
    (hu3 : ¬ (3 : ℤ) ∣ u) (husq : IsSquare u) (hvsq : IsSquare v)
    (hQ : IsSquare (eulerQuadratic (-1) u v)) : u = 1 ∧ v = 1 := by
  lift v to ℕ using hv.le
  exact euler_minus_only_one_nat u v hu hv huv hu3 husq hvsq hQ

end Erdos633
