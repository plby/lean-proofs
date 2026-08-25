import Util.Bernays.PrimeSupportIndicator
import Mathlib.Data.Nat.Factorization.Basic

/-!
# The arithmetic function supported on inert-prime squares
-/

open scoped Classical

namespace Bernays

noncomputable def localParityAF (S : ℕ → Prop) : ArithmeticFunction ℂ :=
  ⟨fun n => (localParity S n : ℂ), by simp⟩

theorem localParityAF_isMultiplicative (S : ℕ → Prop) : (localParityAF S).IsMultiplicative := by
  constructor
  · simp [localParityAF]
  · intro m n hmn
    change (localParity S (m * n) : ℂ) = (localParity S m : ℂ) * (localParity S n : ℂ)
    rw [localParity_mul S hmn, Complex.ofReal_mul]

theorem parity_all_primes_isSquare {n : ℕ} (hn : 0 < n)
    (h : ParityAdmissible (fun _ => True) n) : ∃ k : ℕ, k ^ 2 = n := by
  let k := ∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2)
  refine ⟨k, ?_⟩
  conv_rhs => rw [n.prod_primeFactors_pow_factorization hn.ne']
  dsimp only [k]
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have heven : Even (n.factorization p) := by
    rw [n.factorization_def hprime]
    exact h p hprime trivial
  rw [← pow_mul]
  congr 1
  obtain ⟨j, hj⟩ := heven
  omega

noncomputable def squareSupportAF (S : ℕ → Prop) : ArithmeticFunction ℂ :=
  (localParityAF (fun _ => True)).pmul (primeSupportAF S)

theorem squareSupportAF_isMultiplicative (S : ℕ → Prop) : (squareSupportAF S).IsMultiplicative :=
  (localParityAF_isMultiplicative _).pmul (primeSupportAF_isMultiplicative S)

theorem squareSupportAF_eq (S : ℕ → Prop) (n : ℕ) :
    squareSupportAF S n =
      if 0 < n ∧ ParityAdmissible (fun _ => True) n ∧ PrimeSupported S n then 1 else 0 := by
  rw [squareSupportAF, ArithmeticFunction.pmul_apply]
  change (localParity (fun _ => True) n : ℂ) *
    (if 0 < n ∧ PrimeSupported S n then (1 : ℂ) else 0) = _
  rw [localParity]
  split_ifs <;> simp_all

theorem squareSupportAF_nonzero_isSquare (S : ℕ → Prop) {n : ℕ} (hn : squareSupportAF S n ≠ 0) :
    ∃ k : ℕ, k ^ 2 = n := by
  rw [squareSupportAF_eq] at hn
  split_ifs at hn with h
  · exact parity_all_primes_isSquare h.1 h.2.1
  · exact False.elim (hn rfl)

theorem squareSupportAF_primePower (S : ℕ → Prop) {p : ℕ} (hp : p.Prime) {e : ℕ} (he : 0 < e) :
    squareSupportAF S (p ^ e) = if S p ∧ Even e then 1 else 0 := by
  rw [squareSupportAF, ArithmeticFunction.pmul_apply, primeSupportAF_primePower S hp he]
  change (localParity (fun _ => True) (p ^ e) : ℂ) * (if S p then 1 else 0) = _
  rw [localParity_prime_pow _ hp]
  by_cases hS : S p <;> by_cases hE : Even e <;>
    simp [hS, hE, Nat.not_odd_iff_even, ← Nat.not_even_iff_odd]

end Bernays
