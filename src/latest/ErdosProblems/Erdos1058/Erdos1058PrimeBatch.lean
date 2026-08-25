import ErdosProblems.Erdos1058.Erdos1058Core
import ErdosProblems.Erdos1058.Erdos1058PrimeGapBase
import Mathlib.Data.Nat.GCD.BigOperators

namespace Erdos1058.PrimeGap210Certificate

/-- A common multiple of every possible small prime divisor in the bounded
range.  Reusing it lets one modular inverse certify a whole batch of primes. -/
def trialPrimorial : ℕ :=
  2 * (cubicTrialDivisorChunks.map List.prod).prod

lemma trial_divisor_dvd_trialPrimorial {chunk : List ℕ}
    (hc : chunk ∈ cubicTrialDivisorChunks) {d : ℕ} (hd : d ∈ chunk) :
    d ∣ trialPrimorial := by
  have h₁ : d ∣ chunk.prod := List.dvd_prod hd
  have h₂ : chunk.prod ∣ (cubicTrialDivisorChunks.map List.prod).prod :=
    List.dvd_prod (List.mem_map.mpr ⟨chunk, hc, rfl⟩)
  exact dvd_mul_of_dvd_right (h₁.trans h₂) 2

lemma prime_of_coprime_trialPrimorial {p : ℕ} (hp : 433 < p)
    (hbound : p < 36012001) (hcoprime : p.Coprime trialPrimorial) : p.Prime := by
  apply prime_of_cubicPrimeTableFast hp hbound
  have hnot : ∀ d, 1 < d → d ∣ trialPrimorial → ¬d ∣ p := by
    intro d hd hdM hdp
    have h := Nat.dvd_gcd hdp hdM
    rw [hcoprime.gcd_eq_one] at h
    have := Nat.dvd_one.mp h
    omega
  simp only [cubicPrimeTableFast, if_neg (by omega : p ≠ 2),
    Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨by omega, hnot 2 (by omega) (by exact dvd_mul_right 2 _), ?_⟩
  rw [List.all_eq_true]
  intro chunk hc
  rw [List.all_eq_true]
  intro d hd
  split_ifs
  · apply decide_eq_true
    exact hnot d (by have := three_le_of_mem_cubicTrialDivisorChunks hc hd; omega)
      (trial_divisor_dvd_trialPrimorial hc hd)
  · rfl

/-- A single modular-inverse identity replaces separate primality certificates
for every entry in a batch.  The witness is untrusted data: the identity is
checked by the kernel using ordinary natural-number arithmetic. -/
lemma primes_of_product_inverse {xs : List ℕ} {u : ℕ}
    (hbounds : ∀ p ∈ xs, 433 < p ∧ p < 36012001)
    (hinverse : xs.prod * u % trialPrimorial = 1 % trialPrimorial) :
    xs.Forall Nat.Prime := by
  have hc : xs.prod.Coprime trialPrimorial :=
    Nat.coprime_of_mul_modEq_one u hinverse
  rw [List.forall_iff_forall_mem]
  intro p hp
  exact prime_of_coprime_trialPrimorial (hbounds p hp).1 (hbounds p hp).2
    (Nat.coprime_list_prod_left_iff.mp hc p hp)

end Erdos1058.PrimeGap210Certificate
