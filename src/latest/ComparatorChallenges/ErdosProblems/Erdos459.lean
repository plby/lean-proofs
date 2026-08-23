import Mathlib

namespace Erdos459

def f (u : ℕ) : ℕ :=
  if h : u < 2 then 0
  else Nat.find (show ∃ v, u < v ∧ v.primeFactors ⊆ u.primeFactors by

    obtain ⟨p, hp⟩ : ∃ p, Nat.Prime p ∧ p ∣ u := by
      exact Nat.exists_prime_and_dvd ( by linarith )

    use u * p
    exact ⟨
      lt_mul_of_one_lt_right ( by linarith ) hp.1.one_lt,
      fun x hx => by
        rw [ Nat.primeFactors_mul ] at * <;> aesop⟩)

end Erdos459


namespace Erdos459

open scoped Classical in
theorem main_theorem (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
  ∃ x₀ : ℝ, ∀ x ≥ x₀,
    (Finset.filter (fun n => (f n : ℝ) < (1 + ε) * n)
      (Finset.range (⌊x⌋₊ + 1))).card ≥ (1 - δ) * x := by
  sorry

end Erdos459
