import ErdosProblems.Erdos327.Analytic.PrimeRangeWeight
import ErdosProblems.Erdos327.Analytic.Mertens
import Mathlib.Data.Nat.Totient

namespace Erdos327.Analytic

open Finset

/-- All primes strictly below `L`. -/
def primesBelow (L : ℕ) : Finset ℕ :=
  Nat.primesLE (L - 1)

theorem mem_primesBelow {L p : ℕ} :
    p ∈ primesBelow L ↔ p.Prime ∧ p < L := by
  simp only [primesBelow, Nat.mem_primesLE]
  constructor
  · rintro ⟨hpL, hpPrime⟩
    exact ⟨hpPrime, by
      have hpPos := hpPrime.pos
      omega⟩
  · rintro ⟨hpPrime, hpL⟩
    exact ⟨by omega, hpPrime⟩

/-- An integer with no prime factor below `L`. -/
def Rough (L n : ℕ) : Prop :=
  ∀ p, p.Prime → p < L → ¬p ∣ n

theorem Rough.of_dvd
    {L n d : ℕ} (hn : Rough L n) (hd : d ∣ n) :
    Rough L d := by
  intro p hp hpL hpd
  exact hn p hp hpL (hpd.trans hd)

noncomputable instance roughDecidable (L n : ℕ) : Decidable (Rough L n) :=
  Classical.propDecidable _

/-- Squarefree modulus formed from all primes below `L`. -/
def roughPrimeModulus (L : ℕ) : ℕ :=
  ∏ p ∈ primesBelow L, p

theorem roughPrimeModulus_pos (L : ℕ) :
    0 < roughPrimeModulus L := by
  unfold roughPrimeModulus
  apply Finset.prod_pos
  intro p hp
  exact (mem_primesBelow.mp hp).1.pos

theorem rough_iff_coprime {L n : ℕ} :
    Rough L n ↔ (roughPrimeModulus L).Coprime n := by
  unfold roughPrimeModulus
  rw [Nat.coprime_prod_left_iff]
  constructor
  · intro h p hpMem
    have hp := mem_primesBelow.mp hpMem
    exact hp.1.coprime_iff_not_dvd.mpr (h p hp.1 hp.2)
  · intro h p hpPrime hpL
    exact hpPrime.coprime_iff_not_dvd.mp
      (h p (mem_primesBelow.mpr ⟨hpPrime, hpL⟩))

theorem odd_of_rough {L n : ℕ} (hL : 2 < L) (hn : Rough L n) :
    Odd n := by
  rw [← Nat.not_even_iff_odd]
  intro heven
  exact hn 2 Nat.prime_two hL (even_iff_two_dvd.mp heven)

/-- Odd primes strictly below `L`. -/
def oddPrimesBelow (L : ℕ) : Finset ℕ :=
  (Nat.primesLE (L - 1)).erase 2

theorem mem_oddPrimesBelow {L p : ℕ} :
    p ∈ oddPrimesBelow L ↔ p.Prime ∧ 2 < p ∧ p < L := by
  simp only [oddPrimesBelow, mem_erase, Nat.mem_primesLE]
  constructor
  · rintro ⟨hp2, hpL, hpPrime⟩
    have hpge : 2 ≤ p := hpPrime.two_le
    exact ⟨hpPrime, by omega, by omega⟩
  · rintro ⟨hpPrime, hp2, hpL⟩
    exact ⟨by omega, by omega, hpPrime⟩

/-- Squarefree odd-prime cutoff modulus. -/
def oddPrimeModulus (L : ℕ) : ℕ :=
  ∏ p ∈ oddPrimesBelow L, p

theorem oddPrimeModulus_pos (L : ℕ) :
    0 < oddPrimeModulus L := by
  unfold oddPrimeModulus
  apply Finset.prod_pos
  intro p hp
  exact (mem_oddPrimesBelow.mp hp).1.pos

/-- The paper's odd-roughness predicate is exactly coprimality to the
finite cutoff modulus. -/
theorem oddRough_iff_coprime {L n : ℕ} :
    OddRough L n ↔ (oddPrimeModulus L).Coprime n := by
  unfold oddPrimeModulus
  rw [Nat.coprime_prod_left_iff]
  constructor
  · intro h p hpMem
    have hp := mem_oddPrimesBelow.mp hpMem
    exact hp.1.coprime_iff_not_dvd.mpr (h p hp.1 hp.2.1 hp.2.2)
  · intro h p hpPrime hp2 hpL
    exact hpPrime.coprime_iff_not_dvd.mp
      (h p (mem_oddPrimesBelow.mpr ⟨hpPrime, hp2, hpL⟩))

/-- Euler's totient of a product of distinct primes. -/
theorem totient_primeModulus
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime) :
    (∏ p ∈ P, p).totient = ∏ p ∈ P, (p - 1) := by
  induction P using Finset.induction with
  | empty => simp
  | @insert p P hpP ih =>
      have hpPrime : p.Prime := hprime p (by simp)
      have hprimeP : ∀ q ∈ P, q.Prime := by
        intro q hq
        exact hprime q (by simp [hq])
      have hcop : p.Coprime (∏ q ∈ P, q) := by
        rw [Nat.coprime_prod_right_iff]
        intro q hq
        exact (Nat.coprime_primes hpPrime (hprimeP q hq)).2
          (by
            intro hpq
            subst q
            exact hpP hq)
      rw [prod_insert hpP, Nat.totient_mul hcop,
        Nat.totient_prime hpPrime, ih hprimeP, prod_insert hpP]

/-- Real Euler-product form of `totient_primeModulus`. -/
theorem totient_div_primeModulus_eq_product
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime) :
    (((∏ p ∈ P, p).totient : ℕ) : ℝ) / (∏ p ∈ P, p) =
      ∏ p ∈ P, (1 - (1 : ℝ) / p) := by
  rw [totient_primeModulus P hprime]
  push_cast
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hpPrime := hprime p hp
  have hp0 : (p : ℝ) ≠ 0 := by
    exact_mod_cast hpPrime.ne_zero
  rw [Nat.cast_sub hpPrime.one_le]
  field_simp
  ring

/-- A periodic coprimality condition has exactly `q * φ(a)` solutions in
an interval consisting of `q` complete periods. -/
theorem card_filter_coprime_Ico_mul
    (a k q : ℕ) :
    ((Ico k (k + a * q)).filter fun n ↦ a.Coprime n).card =
      q * a.totient := by
  induction q with
  | zero => simp
  | succ q ih =>
      have h₁ : k ≤ k + a * q := by omega
      have h₂ : k + a * q ≤ k + a * q + a := by omega
      have hend : k + a * (q + 1) = k + a * q + a := by
        simp [Nat.mul_succ, add_assoc]
      have hsplit :
          Ico k (k + a * (q + 1)) =
            Ico k (k + a * q) ∪
              Ico (k + a * q) (k + a * q + a) := by
        rw [hend]
        exact (Finset.Ico_union_Ico_eq_Ico h₁ h₂).symm
      rw [hsplit, filter_union]
      rw [card_union_of_disjoint]
      · rw [ih, Nat.filter_coprime_Ico_eq_totient]
        simp [Nat.succ_mul]
      · exact (Finset.Ico_disjoint_Ico_consecutive k
          (k + a * q) (k + a * q + a)).mono
            (filter_subset _ _) (filter_subset _ _)

/-- Lower periodic count in an arbitrary interval: discard the final
incomplete period. -/
theorem totient_mul_div_le_card_filter_coprime_Ico
    (a k n : ℕ) :
    (n / a) * a.totient ≤
      ((Ico k (k + n)).filter fun x ↦ a.Coprime x).card := by
  let q := n / a
  have hlen : a * q ≤ n := by
    dsimp [q]
    exact Nat.mul_div_le n a
  have hsub :
      (Ico k (k + a * q)).filter (fun x ↦ a.Coprime x) ⊆
        (Ico k (k + n)).filter (fun x ↦ a.Coprime x) := by
    intro x hx
    rw [mem_filter, mem_Ico] at hx ⊢
    exact ⟨⟨hx.1.1, hx.1.2.trans_le (by omega)⟩, hx.2⟩
  calc
    (n / a) * a.totient =
        ((Ico k (k + a * q)).filter fun x ↦ a.Coprime x).card := by
          symm
          simpa [q] using card_filter_coprime_Ico_mul a k q
    _ ≤ ((Ico k (k + n)).filter fun x ↦ a.Coprime x).card :=
      card_le_card hsub

/-- Real form of the periodic lower bound, with an explicit one-period
boundary loss. -/
theorem card_filter_coprime_Ico_ge_real
    {a : ℕ} (ha : 0 < a) (k n : ℕ) :
    (n : ℝ) * (a.totient : ℝ) / a - a.totient ≤
      (((Ico k (k + n)).filter fun x ↦ a.Coprime x).card : ℝ) := by
  have hnat := totient_mul_div_le_card_filter_coprime_Ico a k n
  have hcast :
      (((n / a) * a.totient : ℕ) : ℝ) ≤
        (((Ico k (k + n)).filter fun x ↦ a.Coprime x).card : ℝ) := by
    exact_mod_cast hnat
  refine le_trans ?_ hcast
  push_cast
  have hdiv : (n : ℝ) / a - 1 ≤ ((n / a : ℕ) : ℝ) := by
    have hmod : n % a < a := Nat.mod_lt n ha
    have hnlt : n < a * (n / a + 1) := by
      calc
        n = n % a + a * (n / a) := (Nat.mod_add_div n a).symm
        _ < a + a * (n / a) := Nat.add_lt_add_right hmod _
        _ = a * (n / a + 1) := by ring
    have haReal : (0 : ℝ) < a := by exact_mod_cast ha
    have hnltReal :
        (n : ℝ) < (a : ℝ) * (((n / a : ℕ) : ℝ) + 1) := by
      exact_mod_cast hnlt
    have hratio :
        (n : ℝ) / a < ((n / a : ℕ) : ℝ) + 1 :=
      (div_lt_iff₀ haReal).2 (by
        simpa [mul_comm] using hnltReal)
    linarith
  have htot : (0 : ℝ) ≤ a.totient := by positivity
  calc
    (n : ℝ) * (a.totient : ℝ) / a - a.totient =
        ((n : ℝ) / a - 1) * a.totient := by ring
    _ ≤ (n / a : ℕ) * a.totient :=
      mul_le_mul_of_nonneg_right hdiv htot

/-- Odd-rough integers in the source interval `[N/2, N]`. -/
noncomputable def roughSourceInterval (L N : ℕ) : Finset ℕ :=
  (Icc (N / 2) N).filter fun n ↦ Rough L n

@[simp] theorem mem_roughSourceInterval {L N n : ℕ} :
    n ∈ roughSourceInterval L N ↔
      N / 2 ≤ n ∧ n ≤ N ∧ Rough L n := by
  simp only [roughSourceInterval, mem_filter, mem_Icc]
  tauto

/-- Completely explicit positive-density lower bound for the rough source.
The density is the finite Euler product attached to the cutoff modulus. -/
theorem roughSourceInterval_card_lower
    {L N : ℕ} (hN : 4 * roughPrimeModulus L ≤ N) :
    (N : ℝ) / 4 *
        ((roughPrimeModulus L).totient : ℝ) / roughPrimeModulus L ≤
      ((roughSourceInterval L N).card : ℝ) := by
  let D := roughPrimeModulus L
  let k := N / 2
  let len := N + 1 - k
  have hD : 0 < D := roughPrimeModulus_pos L
  have hk : k ≤ N + 1 := by
    dsimp [k]
    omega
  have hend : k + len = N + 1 := by
    dsimp [len]
    omega
  have heq :
      roughSourceInterval L N =
        (Ico k (k + len)).filter fun n ↦ D.Coprime n := by
    ext n
    simp only [roughSourceInterval, mem_filter, mem_Icc, mem_Ico]
    rw [hend]
    simp only [Nat.lt_succ_iff]
    rw [rough_iff_coprime]
  have hlower :=
    card_filter_coprime_Ico_ge_real hD k len
  rw [← heq] at hlower
  have hlenReal : (N : ℝ) / 2 ≤ (len : ℝ) := by
    have hlen2Nat : N ≤ 2 * len := by
      dsimp [len, k]
      omega
    have hlen2Real : (N : ℝ) ≤ 2 * (len : ℝ) := by
      exact_mod_cast hlen2Nat
    nlinarith
  let ρ : ℝ := (D.totient : ℝ) / D
  have hρ : 0 ≤ ρ := by
    dsimp [ρ]
    positivity
  have hDρ : (D : ℝ) * ρ = D.totient := by
    dsimp [ρ]
    field_simp
  have hNreal : 4 * (D : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hN
  have hphi_le_quarter :
      (D.totient : ℝ) ≤ (N : ℝ) / 4 * ρ := by
    rw [← hDρ]
    exact mul_le_mul_of_nonneg_right (by linarith) hρ
  have hhalf :
      (N : ℝ) / 2 * ρ ≤ (len : ℝ) * ρ :=
    mul_le_mul_of_nonneg_right hlenReal hρ
  have hlower' :
      (len : ℝ) * ρ - D.totient ≤
        (roughSourceInterval L N).card := by
    convert hlower using 1; dsimp [ρ]; ring
  calc
    (N : ℝ) / 4 *
          ((roughPrimeModulus L).totient : ℝ) / roughPrimeModulus L =
        (N : ℝ) / 4 * ρ := by
          dsimp [ρ, D]
          ring
    _ ≤ ((roughSourceInterval L N).card : ℝ) := by
      nlinarith

/-- The density in `roughSourceInterval_card_lower` is precisely the
Mertens product over odd primes below `L`. -/
theorem oddPrimeTotientDensity_eq_product (L : ℕ) :
    ((oddPrimeModulus L).totient : ℝ) / oddPrimeModulus L =
      ∏ p ∈ oddPrimesBelow L, (1 - (1 : ℝ) / p) := by
  unfold oddPrimeModulus
  exact totient_div_primeModulus_eq_product _ fun p hp ↦
    (mem_oddPrimesBelow.mp hp).1

theorem roughPrimeTotientDensity_eq_product (L : ℕ) :
    ((roughPrimeModulus L).totient : ℝ) / roughPrimeModulus L =
      ∏ p ∈ primesBelow L, (1 - (1 : ℝ) / p) := by
  unfold roughPrimeModulus
  exact totient_div_primeModulus_eq_product _ fun p hp ↦
    (mem_primesBelow.mp hp).1

/-- Uniform Mertens lower bound for the density of `L`-rough integers. -/
theorem mertensLowerConstant_div_log_le_roughDensity
    {L : ℕ} (hL : 3 ≤ L) :
    mertensLowerConstant / Real.log L ≤
      ((roughPrimeModulus L).totient : ℝ) / roughPrimeModulus L := by
  have hLm1 : 2 ≤ L - 1 := by omega
  have hprod :=
    mertensLowerConstant_div_log_le_primeProduct hLm1
  rw [roughPrimeTotientDensity_eq_product]
  change mertensLowerConstant / Real.log (L : ℝ) ≤
    ∏ p ∈ Nat.primesLE (L - 1), (1 - (1 : ℝ) / p)
  refine le_trans ?_ hprod
  have hlogLm1 : 0 < Real.log ((L - 1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < L - 1))
  have hlogMono :
      Real.log ((L - 1 : ℕ) : ℝ) ≤ Real.log (L : ℝ) := by
    apply Real.log_le_log
    · positivity
    · exact_mod_cast Nat.sub_le L 1
  have hinv :
      1 / Real.log (L : ℝ) ≤
        1 / Real.log ((L - 1 : ℕ) : ℝ) :=
    one_div_le_one_div_of_le hlogLm1 hlogMono
  have hc : 0 ≤ mertensLowerConstant :=
    mertensLowerConstant_pos.le
  simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hinv hc

end Erdos327.Analytic
