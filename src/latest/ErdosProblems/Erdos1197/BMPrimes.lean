import ErdosProblems.Erdos1197.BMDefinitions

namespace Erdos1197

open Chebyshev
open MeasureTheory Set
open scoped Asymptotics BigOperators Chebyshev ENNReal

noncomputable section

/-- Left endpoint of the `j`-th BM prime interval. -/
def bmPrimeLeft (k ν : ℕ) (j : PrimeIdx k) : ℝ :=
  (((23 : ℝ) / 16) + (j : ℝ) / (2 : ℝ) ^ (k + 5)) * (2 : ℝ) ^ ν

/-- Right endpoint of the `j`-th BM prime interval. -/
def bmPrimeRight (k ν : ℕ) (j : PrimeIdx k) : ℝ :=
  (((23 : ℝ) / 16) + ((j : ℝ) + 1) / (2 : ℝ) ^ (k + 5)) * (2 : ℝ) ^ ν

lemma bmPrimeLeft_lt_right (k ν : ℕ) (j : PrimeIdx k) :
    bmPrimeLeft k ν j < bmPrimeRight k ν j := by
  unfold bmPrimeLeft bmPrimeRight
  have hpow : 0 < (2 : ℝ) ^ ν := by positivity
  have hinner : (j : ℝ) / (2 : ℝ) ^ (k + 5) < ((j : ℝ) + 1) / (2 : ℝ) ^ (k + 5) := by
    have hden : ((2 : ℝ) ^ (k + 5)) ≠ 0 := by positivity
    field_simp [hden]
    linarith
  have hinner' :
      (23 / 16 : ℝ) + (j : ℝ) / (2 : ℝ) ^ (k + 5) <
        (23 / 16 : ℝ) + ((j : ℝ) + 1) / (2 : ℝ) ^ (k + 5) := by
    linarith
  exact mul_lt_mul_of_pos_right hinner' hpow

lemma bmPrimeLeft_lower_mem (k ν : ℕ) (j : PrimeIdx k) :
    ((23 : ℝ) / 16) * (2 : ℝ) ^ ν ≤ bmPrimeLeft k ν j := by
  unfold bmPrimeLeft
  have hpow : 0 ≤ (2 : ℝ) ^ ν := by positivity
  have hfrac : 0 ≤ (j : ℝ) / (2 : ℝ) ^ (k + 5) := by positivity
  nlinarith

lemma bmPrimeRight_lt_upper (k ν : ℕ) (j : PrimeIdx k) :
    bmPrimeRight k ν j < ((3 : ℝ) / 2) * (2 : ℝ) ^ ν := by
  unfold bmPrimeRight
  have hpow : 0 < (2 : ℝ) ^ ν := by positivity
  have hval : ((j : ℝ) + 1) / (2 : ℝ) ^ (k + 5) ≤ (1 : ℝ) / 32 := by
    have hj_nat : j.1 + 1 ≤ 2 ^ k := Nat.succ_le_of_lt j.2
    have hj_cast : (j : ℝ) + 1 ≤ (2 : ℝ) ^ k := by
      exact_mod_cast hj_nat
    have hmul : (2 : ℝ) ^ (k + 5) = (2 : ℝ) ^ k * 32 := by
      rw [pow_add]
      norm_num
    rw [hmul]
    have hkpow : ((2 : ℝ) ^ k) ≠ 0 := by positivity
    have htmp :
        ((j : ℝ) + 1) / ((2 : ℝ) ^ k * 32) ≤
          ((2 : ℝ) ^ k) / ((2 : ℝ) ^ k * 32) := by
      field_simp [hkpow]
      nlinarith
    have hcancel : ((2 : ℝ) ^ k) / ((2 : ℝ) ^ k * 32) = (1 : ℝ) / 32 := by
      field_simp [hkpow]
    simpa [hcancel] using htmp
  have hinner : ((23 : ℝ) / 16) + (((j : ℝ) + 1) / (2 : ℝ) ^ (k + 5)) < (3 : ℝ) / 2 := by
    nlinarith
  nlinarith

lemma bmPrimeRight_le_bmPrimeLeft_of_lt {k ν : ℕ} {i j : PrimeIdx k} (hij : i < j) :
    bmPrimeRight k ν i ≤ bmPrimeLeft k ν j := by
  unfold bmPrimeRight bmPrimeLeft
  have hpow : 0 ≤ (2 : ℝ) ^ ν := by positivity
  have hij_nat : i.1 + 1 ≤ j.1 := Nat.succ_le_of_lt hij
  have hij_cast : (i : ℝ) + 1 ≤ (j : ℝ) := by
    exact_mod_cast hij_nat
  have hfrac :
      ((i : ℝ) + 1) / (2 : ℝ) ^ (k + 5) ≤ (j : ℝ) / (2 : ℝ) ^ (k + 5) := by
    have hden : ((2 : ℝ) ^ (k + 5)) ≠ 0 := by positivity
    field_simp [hden]
    nlinarith
  nlinarith

lemma eventually_theta_increment_pos_mul_pow
    (a b ε : ℝ) (ha : 0 < a) (hb : 0 < b) (hgap : ε * (a + b) < b - a) (hε : 0 < ε) :
    ∀ᶠ ν : ℕ in Filter.atTop, θ (b * (2 : ℝ) ^ ν) - θ (a * (2 : ℝ) ^ ν) > 0 := by
  have hpow : Filter.Tendsto (fun ν : ℕ ↦ (2 : ℝ) ^ ν) Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt one_lt_two
  have hta : Filter.Tendsto (fun ν : ℕ ↦ a * (2 : ℝ) ^ ν) Filter.atTop Filter.atTop :=
    hpow.const_mul_atTop ha
  have htb : Filter.Tendsto (fun ν : ℕ ↦ b * (2 : ℝ) ^ ν) Filter.atTop Filter.atTop :=
    hpow.const_mul_atTop hb
  have hLittle : (θ - id) =o[Filter.atTop] id := chebyshev_asymptotic.isLittleO
  have hA :
      ∀ᶠ ν : ℕ in Filter.atTop,
        ‖(θ (a * (2 : ℝ) ^ ν) - a * (2 : ℝ) ^ ν)‖ ≤ ε * ‖a * (2 : ℝ) ^ ν‖ := by
    simpa [sub_eq_add_neg, Function.comp_def] using (hLittle.comp_tendsto hta).def hε
  have hB :
      ∀ᶠ ν : ℕ in Filter.atTop,
        ‖(θ (b * (2 : ℝ) ^ ν) - b * (2 : ℝ) ^ ν)‖ ≤ ε * ‖b * (2 : ℝ) ^ ν‖ := by
    simpa [sub_eq_add_neg, Function.comp_def] using (hLittle.comp_tendsto htb).def hε
  filter_upwards [hA, hB] with ν hAν hBν
  have hpow_pos : 0 < (2 : ℝ) ^ ν := by positivity
  have haν_pos : 0 < a * (2 : ℝ) ^ ν := mul_pos ha hpow_pos
  have hbν_pos : 0 < b * (2 : ℝ) ^ ν := mul_pos hb hpow_pos
  have hAν' := abs_le.mp hAν
  have hBν' := abs_le.mp hBν
  have hA_upper : θ (a * (2 : ℝ) ^ ν) ≤ a * (2 : ℝ) ^ ν + ε * (a * (2 : ℝ) ^ ν) := by
    rw [Real.norm_eq_abs, abs_of_pos haν_pos] at hAν'
    linarith
  have hB_lower : b * (2 : ℝ) ^ ν - ε * (b * (2 : ℝ) ^ ν) ≤ θ (b * (2 : ℝ) ^ ν) := by
    rw [Real.norm_eq_abs, abs_of_pos hbν_pos] at hBν'
    linarith
  have hgapν : (ε * (a + b)) * (2 : ℝ) ^ ν < (b - a) * (2 : ℝ) ^ ν := by
    gcongr
  nlinarith

/-- BM prime supply: for large dyadic scales, there are `2^k` distinct primes in the BM window. -/
theorem bm_many_primes (k : ℕ) :
    ∃ N, ∀ ν ≥ N,
      ∃ p : PrimeIdx k → ℕ,
        Pairwise (fun i j => p i ≠ p j) ∧
        (∀ i, Nat.Prime (p i)) ∧
        (∀ i, ((23 : ℝ) / 16) * (2 : ℝ) ^ ν < (p i : ℝ) ∧
              (p i : ℝ) < ((3 : ℝ) / 2) * (2 : ℝ) ^ ν) := by
  let a : PrimeIdx k → ℝ := fun j => (23 : ℝ) / 16 + (j : ℝ) / (2 : ℝ) ^ (k + 5)
  let b : PrimeIdx k → ℝ := fun j => (23 : ℝ) / 16 + ((j : ℝ) + 1) / (2 : ℝ) ^ (k + 5)
  have h_event :
      ∀ᶠ ν : ℕ in Filter.atTop,
        ∀ j : PrimeIdx k, θ (b j * (2 : ℝ) ^ ν) - θ (a j * (2 : ℝ) ^ ν) > 0 := by
    rw [Filter.eventually_all]
    intro j
    have ha_pos : 0 < a j := by
      dsimp [a]
      positivity
    have hb_pos : 0 < b j := by
      dsimp [b]
      positivity
    have hgap :
        ((1 : ℝ) / (2 : ℝ) ^ (k + 8)) * (a j + b j) < b j - a j := by
      have hsum : a j + b j < 3 := by
        dsimp [a, b]
        have hval : ((j : ℝ) + 1) / (2 : ℝ) ^ (k + 5) ≤ (1 : ℝ) / 32 := by
          have hj_nat : j.1 + 1 ≤ 2 ^ k := Nat.succ_le_of_lt j.2
          have hj_cast : (j : ℝ) + 1 ≤ (2 : ℝ) ^ k := by
            exact_mod_cast hj_nat
          have hmul : (2 : ℝ) ^ (k + 5) = (2 : ℝ) ^ k * 32 := by
            rw [pow_add]
            norm_num
          rw [hmul]
          have hkpow : ((2 : ℝ) ^ k) ≠ 0 := by positivity
          field_simp [hkpow]
          nlinarith [hj_cast]
        have hval' : (j : ℝ) / (2 : ℝ) ^ (k + 5) ≤ (1 : ℝ) / 32 := by
          have hj_le : (j : ℝ) ≤ (j : ℝ) + 1 := by linarith
          have hfrac :
              (j : ℝ) / (2 : ℝ) ^ (k + 5) ≤ ((j : ℝ) + 1) / (2 : ℝ) ^ (k + 5) := by
            gcongr
          exact le_trans hfrac hval
        nlinarith [hval, hval']
      have hdiff : b j - a j = (1 : ℝ) / (2 : ℝ) ^ (k + 5) := by
        dsimp [a, b]
        ring_nf
      rw [hdiff]
      have hkpow8 : 0 < (2 : ℝ) ^ (k + 8) := by positivity
      have hmul :
          ((1 : ℝ) / (2 : ℝ) ^ (k + 8)) * (a j + b j) <
            ((1 : ℝ) / (2 : ℝ) ^ (k + 8)) * 3 := by
        gcongr
      have htarget :
          ((1 : ℝ) / (2 : ℝ) ^ (k + 8)) * 3 < (1 : ℝ) / (2 : ℝ) ^ (k + 5) := by
        have hpow5 : 0 < (2 : ℝ) ^ (k + 5) := by positivity
        field_simp [hkpow8.ne', hpow5.ne']
        have hpow_split : (2 : ℝ) ^ (k + 8) = 8 * (2 : ℝ) ^ (k + 5) := by
          rw [pow_add]
          ring_nf
        nlinarith [hpow_split, hpow5]
      exact lt_trans hmul htarget
    have hε : 0 < (1 : ℝ) / (2 : ℝ) ^ (k + 8) := by positivity
    simpa [a, b] using
      eventually_theta_increment_pos_mul_pow
        (a := a j) (b := b j) (ε := (1 : ℝ) / (2 : ℝ) ^ (k + 8))
        ha_pos hb_pos hgap hε
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h_event
  refine ⟨N, fun ν hν => ?_⟩
  have hν_all := hN ν hν
  have hPrimeExists :
      ∀ j : PrimeIdx k, ∃ p : ℕ, Nat.Prime p ∧
        bmPrimeLeft k ν j < (p : ℝ) ∧ (p : ℝ) ≤ bmPrimeRight k ν j := by
    intro j
    have hleft_lt_right : bmPrimeLeft k ν j < bmPrimeRight k ν j :=
      bmPrimeLeft_lt_right k ν j
    have htheta :
        θ (bmPrimeRight k ν j) - θ (bmPrimeLeft k ν j) > 0 := by
      simpa [bmPrimeLeft, bmPrimeRight] using hν_all j
    simpa [HasPrimeInInterval, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      theta_pos_implies_prime_in_interval hleft_lt_right htheta
  choose p hpPrime hpLower hpUpper using hPrimeExists
  refine ⟨p, ?_, hpPrime, ?_⟩
  · intro i j hij
    rcases lt_or_gt_of_ne hij with hij' | hij'
    · have hsep : bmPrimeRight k ν i ≤ bmPrimeLeft k ν j :=
        bmPrimeRight_le_bmPrimeLeft_of_lt hij'
      have hlt : (p i : ℝ) < p j := by
        exact lt_of_le_of_lt ((hpUpper i).trans hsep) (hpLower j)
      exact fun hEq => by
        exact (ne_of_lt hlt) (by exact_mod_cast hEq)
    · have hsep : bmPrimeRight k ν j ≤ bmPrimeLeft k ν i :=
        bmPrimeRight_le_bmPrimeLeft_of_lt hij'
      have hlt : (p j : ℝ) < p i := by
        exact lt_of_le_of_lt ((hpUpper j).trans hsep) (hpLower i)
      exact fun hEq => by
        exact (ne_of_gt hlt) (by exact_mod_cast hEq)
  · intro j
    constructor
    · exact lt_of_le_of_lt (bmPrimeLeft_lower_mem k ν j) (hpLower j)
    · exact lt_of_le_of_lt (hpUpper j) (bmPrimeRight_lt_upper k ν j)

end

end Erdos1197
