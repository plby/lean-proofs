import ErdosProblems.Erdos556.FiniteRamsey
import ErdosProblems.Erdos556.Sharpness

/-!
# The numerical Ramsey number and its sharp lower bound
-/

namespace Erdos556

theorem ramseyNumber_spec (n : ℕ) : IsRamseyOrder n (ramseyNumber n) := by
  exact csInf_mem (isRamseyOrder_exists n)

theorem ramseyNumber_le_of_isRamseyOrder {n m : ℕ} (h : IsRamseyOrder n m) :
    ramseyNumber n ≤ m := by
  exact csInf_le (OrderBot.bddBelow _) h

theorem isRamseyOrder_iff_ramseyNumber_le {n m : ℕ} :
    IsRamseyOrder n m ↔ ramseyNumber n ≤ m := by
  constructor
  · exact ramseyNumber_le_of_isRamseyOrder
  · exact (ramseyNumber_spec n).mono

/-- The four-clique construction gives the lower bound for every odd `n > 2`. -/
theorem four_mul_sub_three_le_ramseyNumber (n : ℕ) (hn : 2 < n) (ho : Odd n) :
    4 * n - 3 ≤ ramseyNumber n := by
  by_contra h
  have hsmall : ramseyNumber n ≤ 4 * n - 4 := by omega
  exact not_isRamseyOrder_four_mul_sub_four n hn ho
    ((ramseyNumber_spec n).mono hsmall)

#print axioms ramseyNumber_spec
#print axioms four_mul_sub_three_le_ramseyNumber

end Erdos556
