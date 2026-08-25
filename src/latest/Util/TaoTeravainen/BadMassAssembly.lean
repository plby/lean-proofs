import ErdosProblems.Erdos248.TailAssembly
import Util.TaoTeravainen.Extraction
import Util.TaoTeravainen.PrimePowerMoment

/-!
# Tao--Teräväinen: combining ω and excess-multiplicity tails

The exact Ω bad event is contained in the union of the already-formalized
distinct-prime bad event and the new excess-multiplicity bad event. This file
keeps the final union bound separate from the analytic second-moment work.
-/

noncomputable section

open scoped ArithmeticFunction.omega ArithmeticFunction.Omega BigOperators

namespace TaoTeravainen

local instance badMassAssemblyDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- Exact decomposition of Ω into ω plus factorization excess at a positive
integer. -/
theorem Omega_eq_omega_add_factorizationExcess {n : ℕ} (hn : n ≠ 0) :
    Ω n = ω n + factorizationExcess n := by
  rw [← factorization_sum_eq_Omega,
    factorization_sum_eq_support_card_add_excess]
  rw [Nat.support_factorization, Erdos248.omega_eq_primeFactors_card]

/-- If Ω exceeds the sum of two thresholds, either ω exceeds its threshold
or excess multiplicity exceeds the other. -/
theorem natOmegaBadAt_imp_omega_or_excess
    {Cω Ce k n : ℕ} (hk : 1 ≤ k)
    (hbad : natOmegaBadAt (Cω + Ce) k n) :
    Erdos248.natBadAt Cω k n ∨ Ce * k < factorizationExcess (n + k) := by
  have hdecomp : Ω (n + k) = ω (n + k) + factorizationExcess (n + k) :=
    Omega_eq_omega_add_factorizationExcess (by omega)
  by_contra hnot
  push Not at hnot
  unfold Erdos248.natBadAt at hnot
  unfold natOmegaBadAt at hbad
  rw [hdecomp] at hbad
  rw [Nat.add_mul] at hbad
  omega

/-- Pointwise weighted union bound for one Ω-exceptional shift. -/
theorem weightedOmegaBadMass_le_omega_add_excess
    {K Cω Ce k : ℕ} (hk : 1 ≤ k) :
    weightedOmegaBadMass K (Cω + Ce) k ≤
      Erdos248.weightedBadMass K Cω k + weightedExcessBadMass K Ce k := by
  unfold weightedOmegaBadMass Erdos248.weightedBadMass
    weightedExcessBadMass Erdos248.weightedMass Erdos248.weightedSum
    sieveInterval
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro n hn
  by_cases hw : Erdos248.sieveWeight K n = 0
  · simp [hw]
  by_cases hbad : natOmegaBadAt (Cω + Ce) k n
  · rw [if_pos hbad]
    rcases natOmegaBadAt_imp_omega_or_excess hk hbad with homega | hexcess
    · rw [if_pos homega]
      exact le_add_of_nonneg_right
        (mul_nonneg (Erdos248.sieveWeight_nonneg K n)
          (Erdos248.realIndicator_nonneg _))
    · change Erdos248.sieveWeight K n ≤
        (if Erdos248.natBadAt Cω k n then Erdos248.sieveWeight K n else 0) +
          Erdos248.sieveWeight K n *
            Erdos248.realIndicator (Ce * k < factorizationExcess (n + k))
      rw [Erdos248.realIndicator_of_true hexcess]
      split_ifs <;> nlinarith [Erdos248.sieveWeight_nonneg K n]
  · rw [if_neg hbad]
    apply add_nonneg
    · split_ifs
      · exact Erdos248.sieveWeight_nonneg K n
      · exact le_rfl
    · apply mul_nonneg
      · exact Erdos248.sieveWeight_nonneg K n
      · exact Erdos248.realIndicator_nonneg _

/-- Summing the pointwise union bound over all relevant shifts. -/
theorem sum_weightedOmegaBadMass_le_omega_add_excess
    {K Cω Ce : ℕ} :
    (∑ k ∈ Finset.Icc 1 (Erdos248.intervalExponent K),
      weightedOmegaBadMass K (Cω + Ce) k) ≤
      (∑ k ∈ Finset.Icc 1 (Erdos248.intervalExponent K),
        Erdos248.weightedBadMass K Cω k) +
      ∑ k ∈ Finset.Icc 1 (Erdos248.intervalExponent K),
        weightedExcessBadMass K Ce k := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k hk
  exact weightedOmegaBadMass_le_omega_add_excess (Finset.mem_Icc.mp hk).1

/-- One fixed threshold controlling the excess-multiplicity tail at every
regular sieve dimension and every relevant shift. -/
def HasUniformExcessTail (T : ℕ) : Prop :=
  ∀ {A : ℝ} {K : ℕ}, Erdos248.HasUniformWirsingBound A →
    Erdos248.NormalizationRegular A K →
    ∀ k, 1 ≤ k → k ≤ Erdos248.intervalExponent K →
      weightedExcessBadMass K T k ≤
        Erdos248.sieveMass K * ((1 : ℝ) / (16 * (k : ℝ) ^ 2))

/-- The existing ω argument actually spends at most one quarter of the
sieve mass, leaving room for the multiplicity tail. -/
theorem sum_weightedBadMass_le_quarter_of_primeRange_tails
    {A : ℝ} (hA : Erdos248.HasUniformWirsingBound A)
    {K T : ℕ} (hreg : Erdos248.NormalizationRegular A K)
    (hmedium : ∀ k, 1 ≤ k → k ≤ K →
      Erdos248.mediumPrimeBadMass K T k ≤
        Erdos248.sieveMass K * ((1 : ℝ) / (16 * (k : ℝ) ^ 2)))
    (hlarge : ∀ k, 1 ≤ k → k ≤ Erdos248.intervalExponent K →
      Erdos248.largePrimeBadMass K T k ≤
        Erdos248.sieveMass K * ((1 : ℝ) / (16 * (k : ℝ) ^ 2))) :
    (∑ k ∈ Finset.Icc 1 (Erdos248.intervalExponent K),
      Erdos248.weightedBadMass K (2 * T + 102) k) ≤
        Erdos248.sieveMass K / 4 := by
  have hpoint : ∀ k ∈ Finset.Icc 1 (Erdos248.intervalExponent K),
      Erdos248.weightedBadMass K (2 * T + 102) k ≤
        2 * (Erdos248.sieveMass K *
          ((1 : ℝ) / (16 * (k : ℝ) ^ 2))) := by
    intro k hk
    have hk' := Finset.mem_Icc.mp hk
    have hraw := Erdos248.weightedBadMass_le_primeRangeBadMasses
      (K := K) (C := 2 * T + 102) (T := T) (k := k) hreg.1
      le_rfl hk'.1 hk'.2
    by_cases hkK : k ≤ K
    · rw [if_pos hkK] at hraw
      calc
        Erdos248.weightedBadMass K (2 * T + 102) k ≤
            Erdos248.largePrimeBadMass K T k +
              Erdos248.mediumPrimeBadMass K T k := hraw
        _ ≤ Erdos248.sieveMass K * ((1 : ℝ) / (16 * (k : ℝ) ^ 2)) +
            Erdos248.sieveMass K * ((1 : ℝ) / (16 * (k : ℝ) ^ 2)) :=
          add_le_add (hlarge k hk'.1 hk'.2) (hmedium k hk'.1 hkK)
        _ = 2 * (Erdos248.sieveMass K *
            ((1 : ℝ) / (16 * (k : ℝ) ^ 2))) := by ring
    · rw [if_neg hkK, add_zero] at hraw
      calc
        Erdos248.weightedBadMass K (2 * T + 102) k ≤
            Erdos248.largePrimeBadMass K T k := hraw
        _ ≤ Erdos248.sieveMass K * ((1 : ℝ) / (16 * (k : ℝ) ^ 2)) :=
          hlarge k hk'.1 hk'.2
        _ ≤ 2 * (Erdos248.sieveMass K *
            ((1 : ℝ) / (16 * (k : ℝ) ^ 2))) := by
          have : 0 ≤ Erdos248.sieveMass K *
              ((1 : ℝ) / (16 * (k : ℝ) ^ 2)) := by
            apply mul_nonneg (Erdos248.sieveMass_pos hA hreg).le
            positivity
          linarith
  calc
    (∑ k ∈ Finset.Icc 1 (Erdos248.intervalExponent K),
      Erdos248.weightedBadMass K (2 * T + 102) k) ≤
        ∑ k ∈ Finset.Icc 1 (Erdos248.intervalExponent K),
          2 * (Erdos248.sieveMass K *
            ((1 : ℝ) / (16 * (k : ℝ) ^ 2))) :=
      Finset.sum_le_sum hpoint
    _ = (Erdos248.sieveMass K / 8) *
        (∑ k ∈ Finset.Icc 1 (Erdos248.intervalExponent K),
          (1 : ℝ) / (k : ℝ) ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ (Erdos248.sieveMass K / 8) * 2 := by
      exact mul_le_mul_of_nonneg_left
        (Erdos248.sum_Icc_one_div_sq_le_two (Erdos248.intervalExponent K))
        (div_nonneg (Erdos248.sieveMass_pos hA hreg).le (by norm_num))
    _ = Erdos248.sieveMass K / 4 := by ring

/-- A pointwise reciprocal-square excess tail spends at most one eighth of
the sieve mass after summing over all relevant shifts. -/
theorem sum_weightedExcessBadMass_le_eighth
    {A : ℝ} (hA : Erdos248.HasUniformWirsingBound A)
    {K T : ℕ} (hreg : Erdos248.NormalizationRegular A K)
    (hexcess : ∀ k, 1 ≤ k → k ≤ Erdos248.intervalExponent K →
      weightedExcessBadMass K T k ≤
        Erdos248.sieveMass K * ((1 : ℝ) / (16 * (k : ℝ) ^ 2))) :
    (∑ k ∈ Finset.Icc 1 (Erdos248.intervalExponent K),
      weightedExcessBadMass K T k) ≤ Erdos248.sieveMass K / 8 := by
  calc
    (∑ k ∈ Finset.Icc 1 (Erdos248.intervalExponent K),
      weightedExcessBadMass K T k) ≤
        ∑ k ∈ Finset.Icc 1 (Erdos248.intervalExponent K),
          Erdos248.sieveMass K * ((1 : ℝ) / (16 * (k : ℝ) ^ 2)) := by
      apply Finset.sum_le_sum
      intro k hk
      exact hexcess k (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2
    _ = (Erdos248.sieveMass K / 16) *
        (∑ k ∈ Finset.Icc 1 (Erdos248.intervalExponent K),
          (1 : ℝ) / (k : ℝ) ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ (Erdos248.sieveMass K / 16) * 2 := by
      exact mul_le_mul_of_nonneg_left
        (Erdos248.sum_Icc_one_div_sq_le_two (Erdos248.intervalExponent K))
        (div_nonneg (Erdos248.sieveMass_pos hA hreg).le (by norm_num))
    _ = Erdos248.sieveMass K / 8 := by ring

/-- Existing ω tails together with one excess tail imply the exact
Tao--Teräväinen conclusion. -/
theorem tao_teravainen_of_uniform_excess_tail
    (Tω Te : ℕ)
    (hmedium : Erdos248.HasUniformMediumPrimeTail Tω)
    (hlarge : Erdos248.HasUniformLargePrimeTail Tω)
    (hexcess : HasUniformExcessTail Te) :
    ∃ C : ℝ, 0 < C ∧
      (∃ᶠ N in Filter.atTop, ∀ k : ℕ, 0 < k →
        (N + k).factorization.support.card ≤
            (N + k).factorization.sum (fun _ e => e) ∧
          (N + k).factorization.sum (fun _ e => e) ≤ C * k) := by
  apply tao_teravainen_of_uniform_weightedOmegaBadMass
    (2 * Tω + 102 + Te) (by omega)
  intro A K hA hreg
  have homega := sum_weightedBadMass_le_quarter_of_primeRange_tails hA hreg
    (hmedium hA hreg) (hlarge hA hreg)
  have hex := sum_weightedExcessBadMass_le_eighth hA hreg
    (hexcess hA hreg)
  have hunion := sum_weightedOmegaBadMass_le_omega_add_excess
    (K := K) (Cω := 2 * Tω + 102) (Ce := Te)
  calc
    (∑ k ∈ Finset.Icc 1 (Erdos248.intervalExponent K),
      weightedOmegaBadMass K (2 * Tω + 102 + Te) k) ≤
        (∑ k ∈ Finset.Icc 1 (Erdos248.intervalExponent K),
          Erdos248.weightedBadMass K (2 * Tω + 102) k) +
        ∑ k ∈ Finset.Icc 1 (Erdos248.intervalExponent K),
          weightedExcessBadMass K Te k := hunion
    _ ≤ Erdos248.sieveMass K / 4 + Erdos248.sieveMass K / 8 :=
      add_le_add homega hex
    _ < Erdos248.sieveMass K := by
      have hmass := Erdos248.sieveMass_pos hA hreg
      nlinarith

end TaoTeravainen
