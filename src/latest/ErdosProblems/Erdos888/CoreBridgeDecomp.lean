import ErdosProblems.Erdos888.CoreFibers
import ErdosProblems.Erdos888.BlockEncoding

/-!
# Extracting the largest prime from a squarefree core

This file is the arithmetic bridge between the dyadic core expression and
`CoreEstimate.squarefreeCorePairSum`.  A nontrivial squarefree core is written
canonically as `c = d * r`, where `r` is its largest prime factor.  The
dyadic representative `rho` of `r` then differs from `r` by a factor at most
two.  The last lemma records the corresponding comparison of the exact real
weights used by the two sums.
-/

namespace Erdos888
namespace CoreBridgeDecomp

noncomputable section

/-- The largest prime factor of a nontrivial core. -/
abbrev largestPrime (c : ℕ) : ℕ := Erdos469.largestPrimeFactor c

/-- The old core remaining after its largest prime factor is removed. -/
def oldCore (c : ℕ) : ℕ := c / largestPrime c

/-- The lower endpoint of the canonical dyadic block containing the largest
prime factor of `c`. -/
def dyadicRepresentative (c : ℕ) : ℕ :=
  2 ^ dyadicIndex (largestPrime c)

lemma largestPrime_spec {c : ℕ} (hc : 1 < c) :
    Erdos469.IsLargestPrimeFactor c (largestPrime c) :=
  Erdos469.largestPrimeFactor_spec hc

lemma largestPrime_prime {c : ℕ} (hc : 1 < c) :
    Nat.Prime (largestPrime c) :=
  (largestPrime_spec hc).prime

lemma largestPrime_dvd {c : ℕ} (hc : 1 < c) : largestPrime c ∣ c :=
  (largestPrime_spec hc).dvd

lemma oldCore_mul_largestPrime {c : ℕ} (hc : 1 < c) :
    oldCore c * largestPrime c = c := by
  exact Nat.div_mul_cancel (largestPrime_dvd hc)

lemma largestPrime_mul_oldCore {c : ℕ} (hc : 1 < c) :
    largestPrime c * oldCore c = c := by
  rw [Nat.mul_comm, oldCore_mul_largestPrime hc]

lemma oldCore_pos {c : ℕ} (hc : 1 < c) : 0 < oldCore c := by
  unfold oldCore
  exact Nat.div_pos (Nat.le_of_dvd (by omega) (largestPrime_dvd hc))
    (largestPrime_prime hc).pos

lemma one_le_oldCore {c : ℕ} (hc : 1 < c) : 1 ≤ oldCore c :=
  oldCore_pos hc

lemma oldCore_dvd {c : ℕ} (hc : 1 < c) : oldCore c ∣ c := by
  exact ⟨largestPrime c, oldCore_mul_largestPrime hc |>.symm⟩

lemma oldCore_squarefree {c : ℕ} (hc : 1 < c) (hsf : Squarefree c) :
    Squarefree (oldCore c) :=
  hsf.squarefree_of_dvd (oldCore_dvd hc)

lemma largestPrime_not_dvd_oldCore {c : ℕ} (hc : 1 < c)
    (hsf : Squarefree c) : ¬ largestPrime c ∣ oldCore c := by
  intro hdiv
  have hsquare : largestPrime c ^ 2 ∣ c := by
    obtain ⟨k, hk⟩ := hdiv
    refine ⟨k, ?_⟩
    calc
      c = oldCore c * largestPrime c := (oldCore_mul_largestPrime hc).symm
      _ = (largestPrime c * k) * largestPrime c := by rw [hk]
      _ = largestPrime c ^ 2 * k := by ring
  exact (Nat.squarefree_iff_prime_squarefree.mp hsf _
    (largestPrime_prime hc)) (by simpa [pow_two] using hsquare)

/-- Every prime in the old core is strictly smaller than the extracted
largest prime. -/
lemma primeFactor_oldCore_lt_largestPrime {c p : ℕ} (hc : 1 < c)
    (hsf : Squarefree c) (hp : p ∈ (oldCore c).primeFactors) :
    p < largestPrime c := by
  have hpprime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have hpd : p ∣ c :=
    (Nat.dvd_of_mem_primeFactors hp).trans (oldCore_dvd hc)
  have hple : p ≤ largestPrime c := (largestPrime_spec hc).2.2 p hpprime hpd
  exact lt_of_le_of_ne hple fun hpr ↦ by
    subst p
    exact largestPrime_not_dvd_oldCore hc hsf
      (Nat.dvd_of_mem_primeFactors hp)

lemma dyadicRepresentative_lt_largestPrime {c : ℕ} (hc : 1 < c) :
    dyadicRepresentative c < largestPrime c := by
  have hm := prime_mem_dyadicPrimeBlock (largestPrime_prime hc)
  exact lower_lt_of_mem_dyadicPrimeBlock hm

lemma dyadicRepresentative_le_largestPrime {c : ℕ} (hc : 1 < c) :
    dyadicRepresentative c ≤ largestPrime c :=
  (dyadicRepresentative_lt_largestPrime hc).le

lemma largestPrime_le_two_mul_dyadicRepresentative {c : ℕ} (hc : 1 < c) :
    largestPrime c ≤ 2 * dyadicRepresentative c := by
  have hm := prime_mem_dyadicPrimeBlock (largestPrime_prime hc)
  have hu := le_upper_of_mem_dyadicPrimeBlock hm
  simpa [dyadicRepresentative, pow_succ, Nat.mul_comm] using hu

lemma dyadicRepresentative_pos (c : ℕ) : 0 < dyadicRepresentative c := by
  simp [dyadicRepresentative]

/-- Replacing the dyadic representative by the actual largest prime costs
at most the factor four in the cubic size condition. -/
lemma oldCore_mul_largestPrime_pow_three_le_four_mul {c n : ℕ}
    (hc : 1 < c)
    (hsize : c * dyadicRepresentative c ^ 2 ≤ n) :
    oldCore c * largestPrime c ^ 3 ≤ 4 * n := by
  have hrho := largestPrime_le_two_mul_dyadicRepresentative hc
  have hrsq : largestPrime c ^ 2 ≤ 4 * dyadicRepresentative c ^ 2 := by
    nlinarith
  calc
    oldCore c * largestPrime c ^ 3 =
        c * largestPrime c ^ 2 := by
      rw [show largestPrime c ^ 3 = largestPrime c * largestPrime c ^ 2 by ring,
        ← Nat.mul_assoc, oldCore_mul_largestPrime hc]
    _ ≤ c * (4 * dyadicRepresentative c ^ 2) :=
      Nat.mul_le_mul_left c hrsq
    _ = 4 * (c * dyadicRepresentative c ^ 2) := by ring
    _ ≤ 4 * n := Nat.mul_le_mul_left 4 hsize

/-- Both logarithmic arguments in `coreWeight_le` are at least one under
the natural core-size hypothesis. -/
lemma one_le_core_log_arguments {c n : ℕ} (hc : 1 < c)
    (hsize : oldCore c * largestPrime c ^ 2 ≤ n) :
    (1 : ℝ) ≤ (n : ℝ) /
        ((c : ℝ) * dyadicRepresentative c) ∧
      (1 : ℝ) ≤ (n : ℝ) /
        ((oldCore c : ℝ) * (largestPrime c : ℝ) ^ 2) := by
  have hdpos := oldCore_pos hc
  have hrpos := (largestPrime_prime hc).pos
  have hrho := dyadicRepresentative_le_largestPrime hc
  have hleftNat : c * dyadicRepresentative c ≤ n := by
    calc
      c * dyadicRepresentative c =
          oldCore c * largestPrime c * dyadicRepresentative c := by
        rw [oldCore_mul_largestPrime hc]
      _ ≤ oldCore c * largestPrime c * largestPrime c := by
        exact Nat.mul_le_mul_left (oldCore c * largestPrime c) hrho
      _ = oldCore c * largestPrime c ^ 2 := by ring
      _ ≤ n := hsize
  constructor
  · rw [le_div_iff₀]
    · norm_num
      exact_mod_cast hleftNat
    · exact mul_pos (by exact_mod_cast (lt_trans zero_lt_one hc))
        (by exact_mod_cast dyadicRepresentative_pos c)
  · rw [le_div_iff₀]
    · norm_num
      exact_mod_cast hsize
    · positivity

/-- Comparison of the dyadic core weight with the weight after extracting
the largest prime factor.  This is the pointwise inequality used to reindex
the core sum. -/
theorem coreWeight_le {c n : ℕ} (hc : 1 < c)
    (hsize : oldCore c * largestPrime c ^ 2 ≤ n) :
    1 / ((c : ℝ) * dyadicRepresentative c *
        lambda ((n : ℝ) / ((c : ℝ) * dyadicRepresentative c))) ≤
      2 * (1 / (largestPrime c : ℝ) ^ 2) *
        (1 / ((oldCore c : ℝ) *
          lambda ((n : ℝ) /
            ((oldCore c : ℝ) * (largestPrime c : ℝ) ^ 2)))) := by
  have hargs := one_le_core_log_arguments hc hsize
  have hdposNat := oldCore_pos hc
  have hrposNat := (largestPrime_prime hc).pos
  have hρposNat := dyadicRepresentative_pos c
  have hdpos : (0 : ℝ) < oldCore c := by exact_mod_cast hdposNat
  have hrpos : (0 : ℝ) < largestPrime c := by exact_mod_cast hrposNat
  have hρpos : (0 : ℝ) < dyadicRepresentative c := by exact_mod_cast hρposNat
  have hnposNat : 0 < n := by
    have hprod : 0 < oldCore c * largestPrime c ^ 2 := by positivity
    exact hprod.trans_le hsize
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hnposNat
  have hLleft : 0 < lambda ((n : ℝ) /
      ((c : ℝ) * dyadicRepresentative c)) := lambda_pos hargs.1
  have hLright : 0 < lambda ((n : ℝ) /
      ((oldCore c : ℝ) * (largestPrime c : ℝ) ^ 2)) :=
    lambda_pos hargs.2
  have hdenomNat : c * dyadicRepresentative c ≤
      oldCore c * largestPrime c ^ 2 := by
    calc
      c * dyadicRepresentative c =
          oldCore c * largestPrime c * dyadicRepresentative c := by
        rw [oldCore_mul_largestPrime hc]
      _ ≤ oldCore c * largestPrime c * largestPrime c :=
        Nat.mul_le_mul_left (oldCore c * largestPrime c)
          (dyadicRepresentative_le_largestPrime hc)
      _ = oldCore c * largestPrime c ^ 2 := by ring
  have hargmono :
      (n : ℝ) / ((oldCore c : ℝ) * (largestPrime c : ℝ) ^ 2) ≤
        (n : ℝ) / ((c : ℝ) * dyadicRepresentative c) := by
    apply div_le_div_of_nonneg_left (by positivity)
    · positivity
    · exact_mod_cast hdenomNat
  have hLmono : lambda ((n : ℝ) /
      ((oldCore c : ℝ) * (largestPrime c : ℝ) ^ 2)) ≤
      lambda ((n : ℝ) / ((c : ℝ) * dyadicRepresentative c)) := by
    exact lambda_mono (by positivity) hargmono
  have hrhoR : (largestPrime c : ℝ) ≤
      2 * dyadicRepresentative c := by
    exact_mod_cast largestPrime_le_two_mul_dyadicRepresentative hc
  have hcR : (c : ℝ) = (oldCore c : ℝ) * largestPrime c := by
    exact_mod_cast (oldCore_mul_largestPrime hc).symm
  rw [hcR] at hLleft hLmono
  rw [hcR]
  let L₁ : ℝ := lambda ((n : ℝ) /
    (((oldCore c : ℝ) * largestPrime c) * dyadicRepresentative c))
  let L₂ : ℝ := lambda ((n : ℝ) /
    ((oldCore c : ℝ) * (largestPrime c : ℝ) ^ 2))
  have hL₁ : 0 < L₁ := by simpa [L₁, mul_assoc] using hLleft
  have hL₂ : 0 < L₂ := by simpa [L₂] using hLright
  have hL₂L₁ : L₂ ≤ L₁ := by simpa [L₁, L₂, hcR] using hLmono
  have hdenomCompare :
      (oldCore c : ℝ) * (largestPrime c : ℝ) ^ 2 * L₂ ≤
        2 * ((oldCore c : ℝ) * largestPrime c *
          dyadicRepresentative c * L₁) := by
    calc
      (oldCore c : ℝ) * (largestPrime c : ℝ) ^ 2 * L₂ ≤
          (oldCore c : ℝ) * (largestPrime c : ℝ) ^ 2 * L₁ :=
        mul_le_mul_of_nonneg_left hL₂L₁ (by positivity)
      _ = ((oldCore c : ℝ) * largestPrime c * L₁) * largestPrime c := by ring
      _ ≤ ((oldCore c : ℝ) * largestPrime c * L₁) *
          (2 * dyadicRepresentative c) :=
        mul_le_mul_of_nonneg_left hrhoR (by positivity)
      _ = 2 * ((oldCore c : ℝ) * largestPrime c *
          dyadicRepresentative c * L₁) := by ring
  have hleftDen : 0 < (oldCore c : ℝ) * largestPrime c *
      dyadicRepresentative c * L₁ := by positivity
  have hrightDen : 0 < (oldCore c : ℝ) *
      (largestPrime c : ℝ) ^ 2 * L₂ := by positivity
  have hfrac :
      1 / ((oldCore c : ℝ) * largestPrime c *
        dyadicRepresentative c * L₁) ≤
      2 / ((oldCore c : ℝ) * (largestPrime c : ℝ) ^ 2 * L₂) := by
    rw [div_le_div_iff₀ hleftDen hrightDen]
    simpa using hdenomCompare
  calc
    1 / ((oldCore c : ℝ) * largestPrime c * dyadicRepresentative c * L₁) ≤
        2 / ((oldCore c : ℝ) * (largestPrime c : ℝ) ^ 2 * L₂) := hfrac
    _ = 2 * (1 / (largestPrime c : ℝ) ^ 2) *
        (1 / ((oldCore c : ℝ) * L₂)) := by
      field_simp

end

end CoreBridgeDecomp
end Erdos888
