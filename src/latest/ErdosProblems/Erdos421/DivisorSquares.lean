import ErdosProblems.Erdos421.DivisorTuples

/-! # A pointwise square majorant for divisor coefficients -/

namespace Erdos421

theorem multichoose_succ_mul {r : ℕ} (hr : 0 < r) (e : ℕ) :
    (e + 1) * r.multichoose (e + 1) = (e + r) * r.multichoose e := by
  rw [Nat.multichoose_eq, Nat.multichoose_eq]
  have h₁ : r + e - 1 + 1 = r + e := by omega
  have h₂ : r + (e + 1) - 1 = r + e := by omega
  have h := Nat.add_one_mul_choose_eq (r + e - 1) e
  rw [h₁] at h
  rw [h₂]
  simpa only [Nat.add_comm r e, Nat.mul_comm] using h.symm

theorem multichoose_square_le (r e : ℕ) :
    (r.multichoose e) ^ 2 ≤ (r ^ 2).multichoose e := by
  by_cases hr : r = 0
  · subst r
    cases e <;> simp
  have hrpos : 0 < r := Nat.pos_of_ne_zero hr
  have hr2pos : 0 < r ^ 2 := pow_pos hrpos _
  induction e with
  | zero => simp
  | succ e ih =>
    have hfactor : (e + r) ^ 2 ≤ (e + 1) * (e + r ^ 2) := by
      obtain ⟨s, hs⟩ := Nat.exists_eq_succ_of_ne_zero hr
      subst r
      have heq : (e + s.succ) ^ 2 + e * s ^ 2 = (e + 1) * (e + s.succ ^ 2) := by
        simp only [Nat.succ_eq_add_one]
        ring
      omega
    have hstep := multichoose_succ_mul hrpos e
    have hstep₂ := multichoose_succ_mul hr2pos e
    have hbound : (e + 1) ^ 2 * (r.multichoose (e + 1)) ^ 2 ≤
        (e + 1) ^ 2 * (r ^ 2).multichoose (e + 1) := by
      calc
        _ = ((e + 1) * r.multichoose (e + 1)) ^ 2 := by ring
        _ = ((e + r) * r.multichoose e) ^ 2 := by rw [hstep]
        _ = (e + r) ^ 2 * (r.multichoose e) ^ 2 := by ring
        _ ≤ ((e + 1) * (e + r ^ 2)) * (r ^ 2).multichoose e :=
          Nat.mul_le_mul hfactor ih
        _ = (e + 1) * ((e + r ^ 2) * (r ^ 2).multichoose e) := by ring
        _ = (e + 1) * ((e + 1) * (r ^ 2).multichoose (e + 1)) := by rw [hstep₂]
        _ = _ := by ring
    exact (mul_le_mul_iff_right₀ (pow_pos (Nat.succ_pos e) 2)).mp hbound

theorem divisorTuples_square_le (k n : ℕ) :
    (divisorTuples k n) ^ 2 ≤ divisorTuples (k ^ 2) n := by
  by_cases hn : n = 0
  · subst n
    simp [divisorTuples]
  have hk := (ArithmeticFunction.isMultiplicative_zeta.pow (k := k))
  have hk₂ := (ArithmeticFunction.isMultiplicative_zeta.pow (k := k ^ 2))
  unfold divisorTuples
  rw [hk.multiplicative_factorization _ hn, hk₂.multiplicative_factorization _ hn]
  change (∏ p ∈ n.primeFactors, divisorTuples k (p ^ n.factorization p)) ^ 2 ≤
    ∏ p ∈ n.primeFactors, divisorTuples (k ^ 2) (p ^ n.factorization p)
  rw [← Finset.prod_pow]
  apply Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _)
  intro p hp
  rw [divisorTuples_prime_pow (Nat.prime_of_mem_primeFactors hp),
    divisorTuples_prime_pow (Nat.prime_of_mem_primeFactors hp)]
  exact multichoose_square_le k _

end Erdos421
