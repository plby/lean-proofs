import ErdosProblems.Erdos697.Erdos697PrimeWindow
import ErdosProblems.Erdos697.Erdos697Smooth

/-!
# Prime-factor decomposition for the density-zero half of Erdős 697
-/

open scoped BigOperators

namespace Erdos697.Factorization

noncomputable section

/-- Factorization supported on primes at most `R`. -/
def smallFactorization (R d : ℕ) : ℕ →₀ ℕ :=
  d.factorization.filter (fun p ↦ p ≤ R)

/-- Factorization supported on primes greater than `R`. -/
def roughFactorization (R d : ℕ) : ℕ →₀ ℕ :=
  d.factorization.filter (fun p ↦ R < p)

def smallPart (R d : ℕ) : ℕ :=
  (smallFactorization R d).prod (fun p e ↦ p ^ e)

def roughPart (R d : ℕ) : ℕ :=
  (roughFactorization R d).prod (fun p e ↦ p ^ e)

/-- Distinct prime factors of `d` above `R`. -/
def roughPrimes (R d : ℕ) : Finset ℕ :=
  d.factorization.support.filter (fun p ↦ R < p)

theorem smallFactorization_le (R d : ℕ) :
    smallFactorization R d ≤ d.factorization := by
  intro p
  simp only [smallFactorization, Finsupp.filter_apply]
  split <;> simp

theorem roughFactorization_le (R d : ℕ) :
    roughFactorization R d ≤ d.factorization := by
  intro p
  simp only [roughFactorization, Finsupp.filter_apply]
  split <;> simp

theorem factorization_smallPart (R d : ℕ) :
    (smallPart R d).factorization = smallFactorization R d :=
  Nat.factorization_prod_pow_eq_self_of_le_factorization
    (smallFactorization_le R d)

theorem factorization_roughPart (R d : ℕ) :
    (roughPart R d).factorization = roughFactorization R d :=
  Nat.factorization_prod_pow_eq_self_of_le_factorization
    (roughFactorization_le R d)

theorem smallPart_mul_roughPart {R d : ℕ} (hd : d ≠ 0) :
    smallPart R d * roughPart R d = d := by
  rw [smallPart, roughPart, smallFactorization, roughFactorization]
  have hsplit := d.factorization.prod_filter_mul_prod_filter_not
    (fun p ↦ p ≤ R) (fun p e ↦ p ^ e)
  simpa only [not_le] using hsplit.trans (Nat.prod_factorization_pow_eq_self hd)

theorem smallPart_pos {R d : ℕ} (hd : 0 < d) : 0 < smallPart R d := by
  have h := smallPart_mul_roughPart (R := R) hd.ne'
  exact pos_of_mul_pos_left (h ▸ hd) (Nat.zero_le _)

theorem roughPart_pos {R d : ℕ} (hd : 0 < d) : 0 < roughPart R d := by
  have h := smallPart_mul_roughPart (R := R) hd.ne'
  exact pos_of_mul_pos_right (h ▸ hd) (Nat.zero_le _)

theorem smallPart_dvd {R d : ℕ} (hd : 0 < d) : smallPart R d ∣ d :=
  ⟨roughPart R d, (smallPart_mul_roughPart hd.ne').symm⟩

theorem roughPart_dvd {R d : ℕ} (hd : 0 < d) : roughPart R d ∣ d :=
  ⟨smallPart R d, by
    rw [Nat.mul_comm]
    exact (smallPart_mul_roughPart hd.ne').symm⟩

theorem smallPart_smooth {R d : ℕ} (hd : 0 < d) :
    smallPart R d ∈ (R + 1).smoothNumbers := by
  rw [Nat.mem_smoothNumbers']
  intro p hp hpdvd
  have hpos := hp.factorization_pos_of_dvd (smallPart_pos (R := R) hd).ne' hpdvd
  rw [factorization_smallPart, smallFactorization,
    Finsupp.filter_apply] at hpos
  split at hpos
  · omega
  · simp at hpos

theorem smallPart_coprime {R d m : ℕ} (hd : 0 < d)
    (hcop : d.Coprime m) : (smallPart R d).Coprime m :=
  hcop.of_dvd_left (smallPart_dvd hd)

theorem smallPart_coprime_prime_gt
    {R d p : ℕ} (hd : 0 < d) (hp : p.Prime) (hRp : R < p) :
    (smallPart R d).Coprime p := by
  rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
  intro hpa
  have hsmooth := smallPart_smooth (R := R) hd
  have hlt := (Nat.mem_smoothNumbers'.mp hsmooth) p hp hpa
  omega

@[simp] theorem mem_roughPrimes {R d p : ℕ} (hd : d ≠ 0) :
    p ∈ roughPrimes R d ↔ R < p ∧ p.Prime ∧ p ∣ d := by
  simp only [roughPrimes, Finset.mem_filter, Nat.support_factorization,
    Nat.mem_primeFactors]
  aesop

theorem roughPart_eq_prod_roughPrimes
    {R d : ℕ}
    (hfac : ∀ p ∈ roughPrimes R d, d.factorization p = 1) :
    roughPart R d = ∏ p ∈ roughPrimes R d, p := by
  unfold roughPart roughFactorization roughPrimes
  rw [Finsupp.prod, Finsupp.support_filter]
  apply Finset.prod_congr rfl
  intro p hp
  have hp' : p ∈ d.factorization.support.filter (fun p ↦ R < p) := hp
  simp only [Finsupp.filter_apply, (Finset.mem_filter.mp hp').2, if_true,
    hfac p hp', pow_one]

theorem roughPrimes_subset_window
    {R U d : ℕ} (hd : 0 < d) (hdU : d ≤ U) :
    roughPrimes R d ⊆ PrimeWindow.primes R U := by
  intro p hp
  have hp' := (mem_roughPrimes hd.ne').mp hp
  exact PrimeWindow.mem_primes.mpr
    ⟨hp'.1, (Nat.le_of_dvd hd hp'.2.2).trans hdU, hp'.2.1⟩

theorem roughPrimes_dvd
    {R d n : ℕ} (hdn : d ∣ n) {p : ℕ} (hp : p ∈ roughPrimes R d) :
    p ∣ n := by
  have hd : d ≠ 0 := by
    intro h
    subst d
    simp [roughPrimes] at hp
  exact ((mem_roughPrimes hd).mp hp).2.2.trans hdn

theorem factorization_eq_one_of_no_square
    {R d n : ℕ} (hd : 0 < d) (hdn : d ∣ n)
    (hsq : ∀ p ∈ PrimeWindow.primes R d, ¬ p ^ 2 ∣ n) :
    ∀ p ∈ roughPrimes R d, d.factorization p = 1 := by
  intro p hp
  have hpdata := (mem_roughPrimes hd.ne').mp hp
  have hpwin : p ∈ PrimeWindow.primes R d :=
    PrimeWindow.mem_primes.mpr
      ⟨hpdata.1, Nat.le_of_dvd hd hpdata.2.2, hpdata.2.1⟩
  have hpos := hpdata.2.1.factorization_pos_of_dvd hd.ne' hpdata.2.2
  have hle : d.factorization p ≤ 1 := by
    by_contra hnot
    have htwo : 2 ≤ d.factorization p := by omega
    have hp2d : p ^ 2 ∣ d :=
      (hpdata.2.1.pow_dvd_iff_le_factorization hd.ne').2 htwo
    exact hsq p hpwin (hp2d.trans hdn)
  omega

/-- The squarefree rough factor is the product of its distinct primes. -/
theorem smallPart_mul_prod_roughPrimes
    {R d n : ℕ} (hd : 0 < d) (hdn : d ∣ n)
    (hsq : ∀ p ∈ PrimeWindow.primes R d, ¬ p ^ 2 ∣ n) :
    smallPart R d * (∏ p ∈ roughPrimes R d, p) = d := by
  rw [← roughPart_eq_prod_roughPrimes
    (factorization_eq_one_of_no_square hd hdn hsq)]
  exact smallPart_mul_roughPart hd.ne'

end

end Erdos697.Factorization
