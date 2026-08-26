import Mathlib.Data.Nat.Totient
import Mathlib.Tactic

/-!
# The orders with totient at most four

Strong induction removes one prime divisor. Totient divisibility bounds
that prime by five and transfers the same bound to the smaller quotient.
Only twenty-seven explicit products remain; all are checked in the kernel.
-/

namespace Erdos633

theorem prime_dvd_le_five_of_totient_le_four (n p : ℕ) (hn : 0 < n)
    (hphi : n.totient ≤ 4) (hp : p.Prime) (hpn : p ∣ n) :
    p = 2 ∨ p = 3 ∨ p = 5 := by
  have hle := Nat.le_of_dvd (Nat.totient_pos.mpr hn) (Nat.totient_dvd_of_dvd hpn)
  rw [Nat.totient_prime hp] at hle
  have hp2 := hp.two_le
  have hp5 : p ≤ 5 := by omega
  interval_cases p <;> norm_num at hp <;> norm_num

theorem totient_le_four_orders (n : ℕ) (hn : 0 < n) (hphi : n.totient ≤ 4) :
    n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 8 ∨ n = 10 ∨ n = 12 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn1 : n = 1
    · exact Or.inl hn1
    obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd hn1
    have hpchoices := prime_dvd_le_five_of_totient_le_four n p hn hphi hp hpn
    obtain ⟨m, hnm⟩ := hpn
    have hm : 0 < m := by nlinarith only [hn, hnm]
    have hmn : m < n := by
      have hp2 := hp.two_le
      nlinarith only [hnm, hm, hp2]
    have hmdvd : m ∣ n := ⟨p, by rw [hnm]; ring⟩
    have hmphi : m.totient ≤ 4 :=
      (Nat.le_of_dvd (Nat.totient_pos.mpr hn) (Nat.totient_dvd_of_dvd hmdvd)).trans hphi
    have hmchoices := ih m hmn hm hmphi
    rw [hnm] at hphi ⊢
    rcases hpchoices with rfl | rfl | rfl <;>
      rcases hmchoices with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num at hphi ⊢
    all_goals
      exfalso
      revert hphi
      decide

end Erdos633
