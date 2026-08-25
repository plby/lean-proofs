import ErdosProblems.Erdos258b.HighPowerTail
import ErdosProblems.Erdos248.TailAssembly

/-!
# Simultaneous linear bounds with prime multiplicities

Combine the two existing distinct-prime tails with the new higher-power tail.
The three exceptional masses have total less than the positive sieve mass.
Outside the finite shift range, the elementary bound `2^Ω(m) ≤ m` applies.
-/

open Erdos248 Filter
open scoped BigOperators ArithmeticFunction.omega ArithmeticFunction.Omega

namespace Erdos258b

noncomputable def multiplicityBadMass (K C k : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico (intervalStart K) (2 * intervalStart K),
    if C * k < Ω (n + k) then sieveWeight K n else 0

theorem multiplicityBadMass_le {K C T k : ℕ} (hK : 0 < K)
    (hk : 1 ≤ k) (hkM : k ≤ intervalExponent K) :
    multiplicityBadMass K (1010 * (C + T)) k ≤
      weightedBadMass K C k + highPowerBadMass K T k := by
  classical
  unfold multiplicityBadMass weightedBadMass highPowerBadMass natBadAt
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro n hn
  have hnrange := Finset.mem_Ico.mp hn
  have hsize : n + k ≤ shiftRadius K 1 ^ 101 :=
    ((add_lt_three_intervalStart hnrange.2 hkM).trans
      (three_intervalStart_lt_largestRadius_pow_101 hK)).le
  have hfac := cardFactors_le_omega_add_highPrimePowerExcess (by norm_num : 1 ≤ 101) hsize
  have hcount := highPrimePowerExcess_le_count (R := shiftRadius K 1) (by omega : n + k ≠ 0)
  have hfac' : Ω (n + k) ≤
      1010 * (ω (n + k) + highPrimePowerCount (n + k) (shiftRadius K 1)) := by
    exact hfac.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_left hcount _))
  have hw := sieveWeight_nonneg K n
  by_cases hb : 1010 * (C + T) * k < Ω (n + k)
  · rw [if_pos hb]
    by_cases hω : C * k < ω (n + k)
    · rw [if_pos hω]
      split_ifs <;> linarith
    · have hhigh : T * k < highPrimePowerCount (n + k) (shiftRadius K 1) := by
        by_contra hnot
        have hωle : ω (n + k) ≤ C * k := by omega
        have hhle : highPrimePowerCount (n + k) (shiftRadius K 1) ≤ T * k := by omega
        have hle := Nat.mul_le_mul_left 1010 (Nat.add_le_add hωle hhle)
        have hid : 1010 * (C * k + T * k) = 1010 * (C + T) * k := by ring
        rw [hid] at hle
        omega
      rw [if_neg hω, if_pos hhigh, zero_add]
  · rw [if_neg hb]
    split_ifs <;> linarith

theorem exists_uniform_multiplicity_badMass : ∃ C : ℕ, 2 ≤ C ∧
    ∀ {A : ℝ} {K : ℕ}, HasUniformWirsingBound A → NormalizationRegular A K →
      (∑ k ∈ Finset.Icc 1 (intervalExponent K), multiplicityBadMass K C k) < sieveMass K := by
  obtain ⟨Tm, hm⟩ := exists_uniform_mediumPrimeBadMass_tail
  obtain ⟨Tl, hl⟩ := exists_uniform_largePrimeBadMass_tail
  obtain ⟨Th, hTh, hh⟩ := exists_uniform_highPower_tail
  let T := max Tm Tl
  have hmedium : HasUniformMediumPrimeTail T := by
    intro A K hA hreg k hk1 hkK
    exact (mediumPrimeBadMass_anti_threshold (Nat.le_max_left Tm Tl)).trans
      (hm hA hreg k hk1 hkK)
  have hlarge : HasUniformLargePrimeTail T := by
    intro A K hA hreg k hk1 hkM
    exact (largePrimeBadMass_anti_threshold (Nat.le_max_right Tm Tl)).trans
      (hl hA hreg k hk1 hkM)
  refine ⟨1010 * ((2 * T + 102) + Th), by omega, ?_⟩
  intro A K hA hreg
  have hmass : 0 < sieveMass K := sieveMass_pos hA hreg
  have hpoint (k : ℕ) (hk : k ∈ Finset.Icc 1 (intervalExponent K)) :
      multiplicityBadMass K (1010 * ((2 * T + 102) + Th)) k ≤
        3 * (sieveMass K * (1 / (16 * (k : ℝ) ^ 2))) := by
    obtain ⟨hk1, hkM⟩ := Finset.mem_Icc.mp hk
    have hωraw := weightedBadMass_le_primeRangeBadMasses
      (K := K) (C := 2 * T + 102) (T := T) hreg.1 le_rfl hk1 hkM
    have hω : weightedBadMass K (2 * T + 102) k ≤
        2 * (sieveMass K * (1 / (16 * (k : ℝ) ^ 2))) := by
      have hlk := hlarge hA hreg k hk1 hkM
      by_cases hkK : k ≤ K
      · rw [if_pos hkK] at hωraw
        have hmk := hmedium hA hreg k hk1 hkK
        linarith
      · rw [if_neg hkK, add_zero] at hωraw
        have hnonneg : 0 ≤ sieveMass K * (1 / (16 * (k : ℝ) ^ 2)) := by positivity
        linarith
    have hhk := hh hA hreg k hk1
    have hraw := multiplicityBadMass_le (C := 2 * T + 102) (T := Th) hreg.1 hk1 hkM
    linarith
  calc
    (∑ k ∈ Finset.Icc 1 (intervalExponent K),
        multiplicityBadMass K (1010 * ((2 * T + 102) + Th)) k) ≤
        ∑ k ∈ Finset.Icc 1 (intervalExponent K),
          3 * (sieveMass K * (1 / (16 * (k : ℝ) ^ 2))) := Finset.sum_le_sum hpoint
    _ = (3 * sieveMass K / 16) *
        (∑ k ∈ Finset.Icc 1 (intervalExponent K), (1 : ℝ) / (k : ℝ) ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ (3 * sieveMass K / 16) * 2 :=
      mul_le_mul_of_nonneg_left (sum_Icc_one_div_sq_le_two _) (by positivity)
    _ < sieveMass K := by linarith

theorem exists_avoids_multiplicity_bad_shifts {K C : ℕ}
    (hbad : (∑ k ∈ Finset.Icc 1 (intervalExponent K), multiplicityBadMass K C k) < sieveMass K) :
    ∃ n ∈ Finset.Ico (intervalStart K) (2 * intervalStart K),
      ∀ k ∈ Finset.Icc 1 (intervalExponent K), Ω (n + k) ≤ C * k := by
  classical
  by_contra hnot
  push Not at hnot
  have hpoint (n : ℕ) (hn : n ∈ Finset.Ico (intervalStart K) (2 * intervalStart K)) :
      sieveWeight K n ≤ ∑ k ∈ Finset.Icc 1 (intervalExponent K),
        if C * k < Ω (n + k) then sieveWeight K n else 0 := by
    obtain ⟨k, hk, hkbad⟩ := hnot n hn
    have hsingle : sieveWeight K n =
        (if C * k < Ω (n + k) then sieveWeight K n else 0) := by simp [hkbad]
    nth_rw 1 [hsingle]
    apply Finset.single_le_sum _ hk
    intro j hj
    split_ifs
    · exact sieveWeight_nonneg K n
    · exact le_rfl
  have hsum := Finset.sum_le_sum hpoint
  rw [Finset.sum_comm] at hsum
  change sieveMass K ≤ ∑ k ∈ Finset.Icc 1 (intervalExponent K), multiplicityBadMass K C k at hsum
  exact (not_lt_of_ge hsum) hbad

theorem exists_all_multiplicity_bounds {K C : ℕ} (hC : 2 ≤ C)
    (hbad : (∑ k ∈ Finset.Icc 1 (intervalExponent K), multiplicityBadMass K C k) < sieveMass K) :
    ∃ n : ℕ, intervalStart K ≤ n ∧ ∀ k ≥ 1, Ω (n + k) ≤ C * k := by
  obtain ⟨n, hnrange, hgood⟩ := exists_avoids_multiplicity_bad_shifts hbad
  have hn := Finset.mem_Ico.mp hnrange
  refine ⟨n, hn.1, ?_⟩
  intro k hk1
  by_cases hkM : k ≤ intervalExponent K
  · exact hgood k (Finset.mem_Icc.mpr ⟨hk1, hkM⟩)
  · have hnPow : n ≤ 2 ^ (intervalExponent K + 1) := by
      have hid : 2 * intervalStart K = 2 ^ (intervalExponent K + 1) := by
        rw [intervalStart, pow_succ]
        ring
      omega
    exact (cardFactors_add_le_two_mul_of_le_pow hnPow (by omega) hk1).trans
      (Nat.mul_le_mul_right k hC)

/-- The multiplicity form of the Tao--Teräväinen bound, obtained without a
project-local axiom. -/
theorem cardFactors_le_linear_frequently : ∃ C : ℝ, 0 < C ∧
    (∃ᶠ n in atTop, ∀ k : ℕ, 0 < k → (Ω (n + k) : ℝ) ≤ C * k) := by
  obtain ⟨C, hC, hbad⟩ := exists_uniform_multiplicity_badMass
  refine ⟨C, by exact_mod_cast (show 0 < C by omega), frequently_atTop.mpr ?_⟩
  intro B
  obtain ⟨A, _, hA⟩ := exists_positive_uniformWirsingBound
  obtain ⟨J : ℕ, hAJ⟩ := exists_nat_gt A
  let K := B + J + 1
  have hK : 0 < K := by dsimp [K]; omega
  have hAK : A ≤ K := by
    calc
      A ≤ J := hAJ.le
      _ ≤ K := by exact_mod_cast (show J ≤ K by dsimp [K]; omega)
  have hreg := normalizationRegular_of_le_dimension hK hAK
  obtain ⟨n, hn, hgood⟩ := exists_all_multiplicity_bounds hC (hbad hA hreg)
  refine ⟨n, ?_, ?_⟩
  · exact ((intervalStart_gt_of_lt_dimension (B := B) (K := K)
      (by dsimp [K]; omega)).trans_le hn).le
  · intro k hk
    exact_mod_cast hgood k hk

#print axioms cardFactors_le_linear_frequently

/-- A direct prime-multiplicity bound for the divisor-tail proof, using the
high-power second moment rather than the development in `Util.TaoTeravainen`. -/
theorem prime_multiplicity_bound : ∃ C : ℝ, 0 < C ∧
    (∃ᶠ N in atTop, ∀ k : ℕ, 0 < k →
      (N + k).factorization.support.card ≤
          (N + k).factorization.sum (fun _ e => e) ∧
        (N + k).factorization.sum (fun _ e => e) ≤ C * k) := by
  obtain ⟨C, hC, hgood⟩ := cardFactors_le_linear_frequently
  refine ⟨C, hC, hgood.mono fun N hN k hk => ⟨?_, ?_⟩⟩
  · rw [Finsupp.sum]
    calc
      (N + k).factorization.support.card =
          ∑ _p ∈ (N + k).factorization.support, 1 := by simp
      _ ≤ ∑ p ∈ (N + k).factorization.support, (N + k).factorization p := by
        apply Finset.sum_le_sum
        intro p hp
        exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
  · simpa only [ArithmeticFunction.cardFactors_eq_sum_factorization] using hN k hk

#print axioms prime_multiplicity_bound

end Erdos258b
