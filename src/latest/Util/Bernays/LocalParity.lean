import Util.Bernays.DirichletTauberian
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.EulerProduct.Basic

/-!
# The multiplicative local norm indicator

For an arbitrary set of obstruction primes, the admissible positive integers
are those having even valuation at each obstruction prime. The construction
does not restrict the discriminant or the quadratic form.
-/

open Filter Topology Real
open scoped Classical

namespace Bernays

def ParityAdmissible (S : ℕ → Prop) (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → S p → Even (padicValNat p n)

theorem parityAdmissible_prime_pow_iff (S : ℕ → Prop) {p k : ℕ} (hp : p.Prime) :
    ParityAdmissible S (p ^ k) ↔ ¬ S p ∨ Even k := by
  let : Fact p.Prime := ⟨hp⟩
  constructor
  · intro h
    by_cases hS : S p
    · exact Or.inr (by simpa only [padicValNat.prime_pow] using h p hp hS)
    · exact Or.inl hS
  · intro h q hq hSq
    by_cases hqp : q = p
    · subst q
      have hk : Even k := h.resolve_left (not_not.mpr hSq)
      simpa only [padicValNat.prime_pow] using hk
    · have hnot : ¬ q ∣ p ^ k := by
        intro hdvd
        exact hqp ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hdvd))
      rw [padicValNat.eq_zero_of_not_dvd hnot]
      exact Even.zero

theorem parityAdmissible_mul_iff (S : ℕ → Prop) {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hmn : m.Coprime n) :
    ParityAdmissible S (m * n) ↔ ParityAdmissible S m ∧ ParityAdmissible S n := by
  have left {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m.Coprime n)
      (h : ParityAdmissible S (m * n)) : ParityAdmissible S m := by
    intro p hp hS
    let : Fact p.Prime := ⟨hp⟩
    by_cases hpm : p ∣ m
    · have hpn : ¬ p ∣ n := by
        intro hdvd
        exact hp.not_dvd_one (hmn.gcd_eq_one ▸ Nat.dvd_gcd hpm hdvd)
      have hsum := h p hp hS
      rwa [padicValNat.mul hm.ne' hn.ne', padicValNat.eq_zero_of_not_dvd hpn, add_zero] at hsum
    · rw [padicValNat.eq_zero_of_not_dvd hpm]
      exact Even.zero
  constructor
  · intro h
    exact ⟨left hm hn hmn h, left hn hm hmn.symm (by simpa only [mul_comm] using h)⟩
  · rintro ⟨h₁, h₂⟩ p hp hS
    let : Fact p.Prime := ⟨hp⟩
    rw [padicValNat.mul hm.ne' hn.ne']
    exact (h₁ p hp hS).add (h₂ p hp hS)

noncomputable def localParity (S : ℕ → Prop) (n : ℕ) : ℝ := by
  classical
  exact if 0 < n ∧ ParityAdmissible S n then 1 else 0

@[simp] theorem localParity_zero (S : ℕ → Prop) : localParity S 0 = 0 := by
  simp [localParity]

@[simp] theorem localParity_one (S : ℕ → Prop) : localParity S 1 = 1 := by
  simp [localParity, ParityAdmissible]

theorem localParity_nonneg (S : ℕ → Prop) (n : ℕ) : 0 ≤ localParity S n := by
  unfold localParity
  split_ifs <;> norm_num

theorem localParity_le_one (S : ℕ → Prop) (n : ℕ) : localParity S n ≤ 1 := by
  unfold localParity
  split_ifs <;> norm_num

theorem localParity_mul (S : ℕ → Prop) {m n : ℕ} (hmn : m.Coprime n) :
    localParity S (m * n) = localParity S m * localParity S n := by
  classical
  by_cases hm : 0 < m
  · by_cases hn : 0 < n
    · simp only [localParity, hm, hn, Nat.mul_pos hm hn, true_and,
        parityAdmissible_mul_iff S hm hn hmn]
      by_cases h₁ : ParityAdmissible S m <;> by_cases h₂ : ParityAdmissible S n <;> simp [h₁, h₂]
    · have hn₀ : n = 0 := Nat.eq_zero_of_not_pos hn
      simp [hn₀]
  · have hm₀ : m = 0 := Nat.eq_zero_of_not_pos hm
    simp [hm₀]

theorem localParity_prime_pow (S : ℕ → Prop) {p k : ℕ} (hp : p.Prime) :
    localParity S (p ^ k) = if S p ∧ Odd k then 0 else 1 := by
  classical
  simp only [localParity, pow_pos hp.pos k, true_and, parityAdmissible_prime_pow_iff S hp]
  by_cases hS : S p
  · by_cases hk : Even k
    · simp [hS, hk, Nat.not_odd_iff_even.mpr hk]
    · simp [hS, hk, Nat.not_even_iff_odd.mp hk]
  · simp [hS]

noncomputable def localDirichletTerm (S : ℕ → Prop) (s : ℝ) (n : ℕ) : ℝ :=
  localParity S n / (n : ℝ) ^ s

theorem localDirichletTerm_mul (S : ℕ → Prop) (s : ℝ) {m n : ℕ} (hmn : m.Coprime n) :
    localDirichletTerm S s (m * n) = localDirichletTerm S s m * localDirichletTerm S s n := by
  rw [localDirichletTerm, localDirichletTerm, localDirichletTerm,
    localParity_mul S hmn, Nat.cast_mul, mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
  ring

theorem localDirichletTerm_nonneg (S : ℕ → Prop) (s : ℝ) (n : ℕ) :
    0 ≤ localDirichletTerm S s n :=
  div_nonneg (localParity_nonneg S n) (rpow_nonneg (Nat.cast_nonneg n) s)

theorem localDirichletTerm_summable (S : ℕ → Prop) {s : ℝ} (hs : 1 < s) :
    Summable (localDirichletTerm S s) := by
  apply Summable.of_nonneg_of_le (localDirichletTerm_nonneg S s) _
    (summable_one_div_nat_rpow.mpr hs)
  intro n
  exact div_le_div_of_nonneg_right (localParity_le_one S n) (by positivity)

theorem localDirichletTerm_tsum (S : ℕ → Prop) {s : ℝ} (hs : 1 < s) :
    (∑' n : ℕ, localDirichletTerm S s n) = realDirichlet (localParity S) s := by
  rw [(localDirichletTerm_summable S hs).tsum_eq_zero_add]
  simp only [localDirichletTerm, localParity_zero, zero_div, zero_add, realDirichlet]

theorem localParity_eulerProduct (S : ℕ → Prop) {s : ℝ} (hs : 1 < s) :
    HasProd (fun p : Nat.Primes => ∑' k : ℕ, localDirichletTerm S s (p ^ k))
      (realDirichlet (localParity S) s) := by
  rw [← localDirichletTerm_tsum S hs]
  apply EulerProduct.eulerProduct_hasProd
    (by simp [localDirichletTerm]) (fun {_ _} h => localDirichletTerm_mul S s h)
    (localDirichletTerm_summable S hs).norm
  simp [localDirichletTerm]

end Bernays
