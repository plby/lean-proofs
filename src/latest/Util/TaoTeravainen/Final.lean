import Util.TaoTeravainen.BadMassAssembly
import Util.TaoTeravainen.PrimePowerTruncatedMoment

/-!
# Tao--Teräväinen: unconditional final assembly

The truncated proper-prime-power moment is summable over all relevant shifts.
The deterministic truncation inequality then upgrades the existing distinct
prime-factor argument to the full multiplicity function.
-/

noncomputable section

open scoped ArithmeticFunction.omega ArithmeticFunction.Omega BigOperators
open Filter

namespace TaoTeravainen

local instance finalDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- If the full multiplicity is too large, then either the distinct-prime
count is exceptional or the truncated proper-power count is exceptional. -/
theorem natOmegaBadAt_imp_omega_or_truncated
    {K Cω T k n : ℕ}
    (hK : 0 < K)
    (hn : n ∈ sieveInterval K)
    (hk1 : 1 ≤ k) (hkM : k ≤ Erdos248.intervalExponent K)
    (hbad : natOmegaBadAt (303 * (Cω + T)) k n) :
    Erdos248.natBadAt Cω k n ∨
      T * k <
        truncatedProperPrimePowerCount (Erdos248.shiftRadius K 1) (n + k) := by
  have hn' : n ∈ Finset.Ico (Erdos248.intervalStart K)
      (2 * Erdos248.intervalStart K) := by simpa [sieveInterval] using hn
  have hsize : n + k < Erdos248.shiftRadius K 1 ^ 101 := by
    exact (Erdos248.add_lt_three_intervalStart (Finset.mem_Ico.mp hn').2 hkM).trans
      (Erdos248.three_intervalStart_lt_largestRadius_pow_101 hK)
  have hbound := Omega_le_omega_add_truncatedProperPrimePowerCount
    (J := Erdos248.shiftRadius K 1) (n := n + k) (by omega)
    (Erdos248.one_lt_shiftRadius K 1) hsize
  by_contra hnot
  push Not at hnot
  unfold Erdos248.natBadAt at hnot
  unfold natOmegaBadAt at hbad
  have homega : ω (n + k) ≤ Cω * k := Nat.le_of_not_gt hnot.1
  have htrunc :
      truncatedProperPrimePowerCount (Erdos248.shiftRadius K 1) (n + k) ≤
        T * k := hnot.2
  have htotal :
      Ω (n + k) ≤ 303 * (Cω + T) * k := by
    calc
      Ω (n + k) ≤ 303 * ω (n + k) +
          303 * truncatedProperPrimePowerCount
            (Erdos248.shiftRadius K 1) (n + k) := hbound
      _ ≤ 303 * (Cω * k) + 303 * (T * k) := by gcongr
      _ = 303 * (Cω + T) * k := by ring
  omega

/-- Pointwise weighted union bound for the exact multiplicity exception. -/
theorem weightedOmegaBadMass_le_omega_add_truncated
    {K Cω T k : ℕ} (hK : 0 < K)
    (hk1 : 1 ≤ k) (hkM : k ≤ Erdos248.intervalExponent K) :
    weightedOmegaBadMass K (303 * (Cω + T)) k ≤
      Erdos248.weightedBadMass K Cω k +
        weightedTruncatedPrimePowerBadMass K (Erdos248.shiftRadius K 1) T k := by
  unfold weightedOmegaBadMass Erdos248.weightedBadMass
    weightedTruncatedPrimePowerBadMass Erdos248.weightedMass
    Erdos248.weightedSum sieveInterval
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro n hn
  by_cases hw : Erdos248.sieveWeight K n = 0
  · simp [hw]
  by_cases hbad : natOmegaBadAt (303 * (Cω + T)) k n
  · rw [if_pos hbad]
    rcases natOmegaBadAt_imp_omega_or_truncated hK
      (by simpa [sieveInterval] using hn)
      hk1 hkM hbad with homega | htrunc
    · rw [if_pos homega]
      exact le_add_of_nonneg_right
        (mul_nonneg (Erdos248.sieveWeight_nonneg K n)
          (Erdos248.realIndicator_nonneg _))
    · change Erdos248.sieveWeight K n ≤
        (if Erdos248.natBadAt Cω k n then Erdos248.sieveWeight K n else 0) +
          Erdos248.sieveWeight K n *
            Erdos248.realIndicator
              (T * k < truncatedProperPrimePowerCount
                (Erdos248.shiftRadius K 1) (n + k))
      rw [Erdos248.realIndicator_of_true htrunc]
      split_ifs <;> nlinarith [Erdos248.sieveWeight_nonneg K n]
  · rw [if_neg hbad]
    apply add_nonneg
    · split_ifs
      · exact Erdos248.sieveWeight_nonneg K n
      · exact le_rfl
    · apply mul_nonneg
      · exact Erdos248.sieveWeight_nonneg K n
      · exact Erdos248.realIndicator_nonneg _

/-- The two already-unconditional tails together spend strictly less than
the available sieve mass for full multiplicity. -/
theorem sum_weightedOmegaBadMass_lt_sieveMass_of_primeRange_tails
    {A : ℝ} (hA : Erdos248.HasUniformWirsingBound A)
    {K Tω : ℕ} (hreg : Erdos248.NormalizationRegular A K)
    (hmedium : ∀ k, 1 ≤ k → k ≤ K →
      Erdos248.mediumPrimeBadMass K Tω k ≤
        Erdos248.sieveMass K * ((1 : ℝ) / (16 * (k : ℝ) ^ 2)))
    (hlarge : ∀ k, 1 ≤ k → k ≤ Erdos248.intervalExponent K →
      Erdos248.largePrimeBadMass K Tω k ≤
        Erdos248.sieveMass K * ((1 : ℝ) / (16 * (k : ℝ) ^ 2))) :
    (∑ k ∈ Finset.Icc 1 (Erdos248.intervalExponent K),
      weightedOmegaBadMass K (303 * (2 * Tω + 102 + 1000000)) k) <
        Erdos248.sieveMass K := by
  have homega := sum_weightedBadMass_le_quarter_of_primeRange_tails hA hreg
    hmedium hlarge
  have htrunc := sum_weightedTruncatedPrimePowerBadMass_le_eighth hA hreg
  have hunion :
      (∑ k ∈ Finset.Icc 1 (Erdos248.intervalExponent K),
        weightedOmegaBadMass K (303 * (2 * Tω + 102 + 1000000)) k) ≤
        (∑ k ∈ Finset.Icc 1 (Erdos248.intervalExponent K),
          Erdos248.weightedBadMass K (2 * Tω + 102) k) +
        ∑ k ∈ Finset.Icc 1 (Erdos248.intervalExponent K),
          weightedTruncatedPrimePowerBadMass K (Erdos248.shiftRadius K 1)
            1000000 k := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro k hk
    have hk' := Finset.mem_Icc.mp hk
    exact weightedOmegaBadMass_le_omega_add_truncated hreg.1 hk'.1 hk'.2
  have hSpos := Erdos248.sieveMass_pos hA hreg
  calc
    (∑ k ∈ Finset.Icc 1 (Erdos248.intervalExponent K),
      weightedOmegaBadMass K (303 * (2 * Tω + 102 + 1000000)) k) ≤
        (∑ k ∈ Finset.Icc 1 (Erdos248.intervalExponent K),
          Erdos248.weightedBadMass K (2 * Tω + 102) k) +
        ∑ k ∈ Finset.Icc 1 (Erdos248.intervalExponent K),
          weightedTruncatedPrimePowerBadMass K (Erdos248.shiftRadius K 1)
            1000000 k := hunion
    _ ≤ Erdos248.sieveMass K / 4 + Erdos248.sieveMass K / 8 :=
      add_le_add homega htrunc
    _ < Erdos248.sieveMass K := by nlinarith

/-- Unconditional proof of the exact Tao--Teräväinen statement previously
recorded as an analytic-number-theory axiom. -/
theorem tao_teravainen_unconditional : ∃ C : ℝ, 0 < C ∧
    (∃ᶠ N in atTop, ∀ k : ℕ, 0 < k →
      (N + k).factorization.support.card ≤
          (N + k).factorization.sum (fun _ e => e) ∧
        (N + k).factorization.sum (fun _ e => e) ≤ C * k) := by
  obtain ⟨Tω, hmedium⟩ := Erdos248.exists_uniform_mediumPrimeBadMass_tail
  obtain ⟨Tl, hlarge⟩ := Erdos248.exists_uniform_largePrimeBadMass_tail
  let T := max Tω Tl
  have hmediumT : Erdos248.HasUniformMediumPrimeTail T := by
    intro A K hA' hreg' k hk1 hkK
    exact (Erdos248.mediumPrimeBadMass_anti_threshold
      (Nat.le_max_left Tω Tl)).trans (hmedium hA' hreg' k hk1 hkK)
  have hlargeT : Erdos248.HasUniformLargePrimeTail T := by
    intro A K hA' hreg' k hk1 hkM
    exact (Erdos248.largePrimeBadMass_anti_threshold
      (Nat.le_max_right Tω Tl)).trans (hlarge hA' hreg' k hk1 hkM)
  apply tao_teravainen_of_uniform_weightedOmegaBadMass
    (303 * (2 * T + 102 + 1000000)) (by omega)
  intro A K hA hreg
  exact sum_weightedOmegaBadMass_lt_sieveMass_of_primeRange_tails hA hreg
    (hmediumT hA hreg) (hlargeT hA hreg)

end TaoTeravainen
