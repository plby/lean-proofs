import ErdosProblems.Erdos587.SecondDerivativePartition

/-! Exact forward-difference identities and the third-to-second-difference transfer. -/

namespace Erdos587

lemma phaseIncrement_neg (f : ℕ → ℝ) (n : ℕ) :
    phaseIncrement (fun n => -f n) n = -phaseIncrement f n := by
  unfold phaseIncrement
  ring

lemma phaseIncrement_twice_neg (f : ℕ → ℝ) (n : ℕ) :
    phaseIncrement (phaseIncrement (fun n => -f n)) n = -phaseIncrement (phaseIncrement f) n := by
  have heq : phaseIncrement (fun n => -f n) = fun n => -phaseIncrement f n :=
    funext (phaseIncrement_neg f)
  rw [heq, phaseIncrement_neg]

lemma phaseIncrement_sub_shift (f : ℕ → ℝ) (r n : ℕ) :
    phaseIncrement (fun n => f (n + r) - f n) n = phaseIncrement f (n + r) - phaseIncrement f n := by
  change (f (n + 1 + r) - f (n + 1)) - (f (n + r) - f n) =
    (f (n + r + 1) - f (n + r)) - (f (n + 1) - f n)
  rw [show n + 1 + r = n + r + 1 by omega]
  ring

lemma phaseIncrement_twice_sub_shift (f : ℕ → ℝ) (r n : ℕ) :
    phaseIncrement (phaseIncrement (fun n => f (n + r) - f n)) n =
      phaseIncrement (phaseIncrement f) (n + r) - phaseIncrement (phaseIncrement f) n := by
  have heq : phaseIncrement (fun n => f (n + r) - f n) =
      fun n => phaseIncrement f (n + r) - phaseIncrement f n :=
    funext (phaseIncrement_sub_shift f r)
  rw [heq]
  exact phaseIncrement_sub_shift (phaseIncrement f) r n

theorem correlation_second_difference_bounds (f : ℕ → ℝ) (N r : ℕ) {lam C : ℝ}
    (hlo : ∀ n, n + 2 < N → lam ≤ phaseIncrement (phaseIncrement (phaseIncrement f)) n)
    (hhi : ∀ n, n + 2 < N → phaseIncrement (phaseIncrement (phaseIncrement f)) n ≤ C * lam) :
    ∀ n, n + 1 < N - r →
      (r : ℝ) * lam ≤ phaseIncrement (phaseIncrement (fun n => f (n + r) - f n)) n ∧
      phaseIncrement (phaseIncrement (fun n => f (n + r) - f n)) n ≤ C * ((r : ℝ) * lam) := by
  intro n hn
  have hn0 : n < N - 1 := by omega
  have hnr : n + r < N - 1 := by omega
  have hlow := increment_lower_separation (phaseIncrement (phaseIncrement f)) (N - 1) lam
    (fun k hk => hlo k (by omega)) hn0 hnr (by omega : n ≤ n + r)
  have hhigh := increment_upper_separation (phaseIncrement (phaseIncrement f)) (N - 1) (C * lam)
    (fun k hk => hhi k (by omega)) hn0 hnr (by omega : n ≤ n + r)
  simp only [Nat.cast_add, add_sub_cancel_left] at hlow hhigh
  rw [phaseIncrement_twice_sub_shift]
  constructor <;> nlinarith

end Erdos587
