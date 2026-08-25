import ErdosProblems.Erdos1141.QuadraticCRT
import Mathlib.Combinatorics.Enumerative.InclusionExclusion
import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Counting the admissible Burgess denominators

These inclusion-exclusion estimates are extracted from the elementary sieve
in `Erdos587.NVDevelopment`, independently of its fourth-moment results.
-/

namespace Pollack17.Burgess

open scoped BigOperators

def coprimeDenominators (s : Finset ℕ) (U : ℕ) : Finset ℕ :=
  (Finset.Icc 1 U).filter fun u ↦ u.Coprime (primeModulus s)

/-- Multiples of `p` in the finite interval used to count admissible
Burgess denominators. -/
def primeSetMultiplesInIcc (U p : ℕ) : Finset ↥(Finset.Icc 1 U) :=
  Finset.univ.filter fun u ↦ p ∣ (u : ℕ)

lemma prod_dvd_iff_all_prime_dvd
    (t : Finset ℕ) (ht : ∀ p ∈ t, p.Prime) (n : ℕ) :
    (∏ p ∈ t, p) ∣ n ↔ ∀ p ∈ t, p ∣ n := by
  constructor
  · intro h p hp
    exact (Finset.dvd_prod_of_mem id hp).trans h
  · intro h
    induction t using Finset.induction_on with
    | empty => simp
    | @insert p t hpt ih =>
        rw [Finset.prod_insert hpt]
        have hp : p.Prime := ht p (Finset.mem_insert_self p t)
        have hcop : p.Coprime (∏ r ∈ t, r) := by
          apply Nat.Coprime.prod_right
          intro r hr
          exact (Nat.coprime_primes hp
            (ht r (Finset.mem_insert_of_mem hr))).mpr
            (Ne.symm (ne_of_mem_of_not_mem hr hpt))
        exact hcop.mul_dvd_of_dvd_of_dvd
          (h p (Finset.mem_insert_self p t))
          (ih (fun r hr ↦ ht r (Finset.mem_insert_of_mem hr))
            (fun r hr ↦ h r (Finset.mem_insert_of_mem hr)))

lemma card_inf_primeSetMultiplesInIcc
    (t : Finset ℕ) (ht : ∀ p ∈ t, p.Prime) (U : ℕ) :
    (t.inf (primeSetMultiplesInIcc U)).card =
      U / (∏ p ∈ t, p) := by
  rw [← Nat.Ioc_filter_dvd_card_eq_div]
  refine Finset.card_bij
    (s := t.inf (primeSetMultiplesInIcc U))
    (t := (Finset.Ioc 0 U).filter fun n ↦ (∏ p ∈ t, p) ∣ n)
    (fun (u : ↥(Finset.Icc 1 U)) _hu ↦ (u : ℕ)) ?_ ?_ ?_
  · intro u hu
    rw [Finset.mem_filter]
    constructor
    · exact Finset.mem_Ioc.mpr (Finset.mem_Icc.mp u.property)
    · rw [prod_dvd_iff_all_prime_dvd t ht]
      intro p hp
      have hu' : ∀ p ∈ t, u ∈ primeSetMultiplesInIcc U p := by
        simpa only [Finset.mem_inf] using hu
      have hup : u ∈ primeSetMultiplesInIcc U p := hu' p hp
      simpa [primeSetMultiplesInIcc] using hup
  · intro u₁ h₁ u₂ h₂ huv
    exact Subtype.ext huv
  · intro n hn
    have hnIoc := (Finset.mem_filter.mp hn).1
    let u : ↥(Finset.Icc 1 U) :=
      ⟨n, Finset.mem_Icc.mpr (Finset.mem_Ioc.mp hnIoc)⟩
    refine ⟨u, ?_, rfl⟩
    simp only [Finset.mem_inf]
    intro p hp
    simp only [primeSetMultiplesInIcc, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact (prod_dvd_iff_all_prime_dvd t ht n).mp
      (Finset.mem_filter.mp hn).2 p hp

lemma inf_compl_primeSetMultiples_eq_coprime
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (U : ℕ) :
    s.inf (fun p ↦ (primeSetMultiplesInIcc U p)ᶜ) =
      (Finset.univ : Finset ↥(Finset.Icc 1 U)).filter
        (fun (u : ↥(Finset.Icc 1 U)) ↦
          (u : ℕ).Coprime (primeModulus s)) := by
  ext u
  simp only [Finset.mem_inf, Finset.mem_compl,
    primeSetMultiplesInIcc, Finset.mem_filter, Finset.mem_univ,
    true_and, primeModulus, Nat.coprime_prod_right_iff]
  constructor
  · intro h p hp
    rw [Nat.coprime_comm, (hs p hp).coprime_iff_not_dvd]
    exact h p hp
  · intro h p hp hdiv
    have hpco := h p hp
    rw [Nat.coprime_comm, (hs p hp).coprime_iff_not_dvd] at hpco
    exact hpco hdiv

/-- Inclusion--exclusion formula for the positive denominators coprime to a
squarefree prime-set conductor. -/
lemma card_coprimeDenominators_eq_alternating
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (U : ℕ) :
    ((coprimeDenominators s U).card : ℤ) =
      ∑ t ∈ s.powerset,
        (-1 : ℤ) ^ t.card * (U / (∏ p ∈ t, p) : ℕ) := by
  have hIE := Finset.inclusion_exclusion_card_inf_compl s
    (primeSetMultiplesInIcc U)
  calc
    ((coprimeDenominators s U).card : ℤ) =
        (((Finset.univ : Finset ↥(Finset.Icc 1 U)).filter
          (fun (u : ↥(Finset.Icc 1 U)) ↦
            (u : ℕ).Coprime (primeModulus s))).card : ℤ) := by
      apply congrArg (fun n : ℕ ↦ (n : ℤ))
      refine Finset.card_bij
        (s := coprimeDenominators s U)
        (t := (Finset.univ : Finset ↥(Finset.Icc 1 U)).filter
          (fun (u : ↥(Finset.Icc 1 U)) ↦
            (u : ℕ).Coprime (primeModulus s)))
        (fun n hn ↦ ⟨n, ?_⟩) ?_ ?_ ?_
      · exact (Finset.mem_filter.mp hn).1
      · intro n hn
        simpa [coprimeDenominators] using
          (Finset.mem_filter.mp hn).2
      · intro a ha b hb hab
        exact congrArg Subtype.val hab
      · intro u hu
        refine ⟨u, ?_, Subtype.ext rfl⟩
        simpa [coprimeDenominators] using
          (Finset.mem_filter.mp hu).2
    _ = ((s.inf fun p ↦ (primeSetMultiplesInIcc U p)ᶜ).card : ℤ) := by
      rw [inf_compl_primeSetMultiples_eq_coprime s hs U]
    _ = ∑ t ∈ s.powerset,
          (-1 : ℤ) ^ t.card *
            ((t.inf (primeSetMultiplesInIcc U)).card : ℤ) := hIE
    _ = ∑ t ∈ s.powerset,
          (-1 : ℤ) ^ t.card * (U / (∏ p ∈ t, p) : ℕ) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [card_inf_primeSetMultiplesInIcc t
        (fun p hp ↦ hs p (Finset.mem_powerset.mp ht hp)) U]

lemma alternating_prime_reciprocal_eq
    (s : Finset ℕ) (U : ℕ) :
    (∑ t ∈ s.powerset,
        (-1 : ℝ) ^ t.card *
          ((U : ℝ) / (∏ p ∈ t, p : ℕ))) =
      (U : ℝ) * ∏ p ∈ s, (1 - (p : ℝ)⁻¹) := by
  rw [Finset.prod_sub]
  simp only [Finset.prod_const_one, mul_one]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.prod_inv_distrib]
  simp only [Nat.cast_prod]
  ring

lemma half_le_one_sub_prime_inv {p : ℕ} (hp : p.Prime) :
    (1 / 2 : ℝ) ≤ 1 - (p : ℝ)⁻¹ := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hinv : (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ :=
    inv_anti₀ (by norm_num) hp2
  norm_num at hinv ⊢
  linarith

lemma prod_one_sub_prime_inv_lower
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    (1 / 2 : ℝ) ^ s.card ≤ ∏ p ∈ s, (1 - (p : ℝ)⁻¹) := by
  rw [← Finset.prod_const]
  exact Finset.prod_le_prod (fun p hp ↦ by positivity)
    (fun p hp ↦ half_le_one_sub_prime_inv (hs p hp))

lemma abs_natCast_div_sub_div_lt_one (U d : ℕ) :
    |((U / d : ℕ) : ℝ) - (U : ℝ) / (d : ℝ)| < 1 := by
  have hle : ((U / d : ℕ) : ℝ) ≤ (U : ℝ) / (d : ℝ) :=
    Nat.cast_div_le
  have hlt : (U : ℝ) / (d : ℝ) < ((U / d : ℕ) : ℝ) + 1 := by
    simpa only [Nat.floor_div_eq_div] using
      (Nat.lt_floor_add_one ((U : ℝ) / (d : ℝ)))
  rw [abs_of_nonpos (sub_nonpos.mpr hle)]
  linarith

lemma alternating_prime_floor_sum_error
    (s : Finset ℕ) (U : ℕ) :
    |(∑ t ∈ s.powerset,
        (-1 : ℝ) ^ t.card * ((U / (∏ p ∈ t, p) : ℕ) : ℝ)) -
      ∑ t ∈ s.powerset,
        (-1 : ℝ) ^ t.card *
          ((U : ℝ) / (∏ p ∈ t, p : ℕ))| ≤
        (2 : ℝ) ^ s.card := by
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ t ∈ s.powerset,
        ((-1 : ℝ) ^ t.card * ((U / (∏ p ∈ t, p) : ℕ) : ℝ) -
          (-1 : ℝ) ^ t.card *
            ((U : ℝ) / (∏ p ∈ t, p : ℕ)))| ≤
        ∑ t ∈ s.powerset,
          |((-1 : ℝ) ^ t.card * ((U / (∏ p ∈ t, p) : ℕ) : ℝ) -
            (-1 : ℝ) ^ t.card *
              ((U : ℝ) / (∏ p ∈ t, p : ℕ)))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t ∈ s.powerset, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro t ht
      rw [← mul_sub, abs_mul, abs_neg_one_pow]
      simpa only [one_mul] using
        (abs_natCast_div_sub_div_lt_one U (∏ p ∈ t, p)).le
    _ = (2 : ℝ) ^ s.card := by simp

/-- Crude uniform lower bound for the number of Burgess denominators.  The
main term loses at most one half per conductor prime; the
inclusion--exclusion floor errors cost at most the number of subsets. -/
lemma card_coprimeDenominators_lower
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (U : ℕ) :
    (U : ℝ) * (1 / 2 : ℝ) ^ s.card - (2 : ℝ) ^ s.card ≤
      (coprimeDenominators s U).card := by
  let F : ℝ := ∑ t ∈ s.powerset,
    (-1 : ℝ) ^ t.card * ((U / (∏ p ∈ t, p) : ℕ) : ℝ)
  let R : ℝ := ∑ t ∈ s.powerset,
    (-1 : ℝ) ^ t.card * ((U : ℝ) / (∏ p ∈ t, p : ℕ))
  have hcount : ((coprimeDenominators s U).card : ℝ) = F := by
    have h := congrArg (fun z : ℤ ↦ (z : ℝ))
      (card_coprimeDenominators_eq_alternating s hs U)
    simpa only [Int.cast_natCast, Int.cast_sum, Int.cast_mul,
      Int.cast_pow, Int.cast_neg, Int.cast_one] using h
  have herror : |F - R| ≤ (2 : ℝ) ^ s.card :=
    alternating_prime_floor_sum_error s U
  have hR : (U : ℝ) * ∏ p ∈ s, (1 - (p : ℝ)⁻¹) = R :=
    (alternating_prime_reciprocal_eq s U).symm
  have hprod : (U : ℝ) * (1 / 2 : ℝ) ^ s.card ≤ R := by
    rw [← hR]
    exact mul_le_mul_of_nonneg_left
      (prod_one_sub_prime_inv_lower s hs) (by positivity)
  have hRF : R - F ≤ (2 : ℝ) ^ s.card := by
    calc
      R - F ≤ |R - F| := le_abs_self _
      _ = |F - R| := abs_sub_comm _ _
      _ ≤ (2 : ℝ) ^ s.card := herror
  rw [hcount]
  linarith


end Pollack17.Burgess
