import ErdosProblems.Erdos248.FinalReduction
import Util.TaoTeravainen.Arithmetic

/-!
# Tao--Teräväinen: extraction from Ω bad-mass bounds

The analytic prime-power argument only has to bound a finite sum of weighted
Ω-exceptional events. This module turns that estimate into one simultaneous
witness, handles all larger shifts deterministically, and packages the exact
factorization statement used by the public theorem.
-/

noncomputable section

open scoped ArithmeticFunction.Omega BigOperators
open Filter

namespace TaoTeravainen

local instance extractionDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- Simultaneous linear control of the number of prime factors with
multiplicity. -/
def IsOmegaGood (C : ℝ) (n : ℕ) : Prop :=
  ∀ k ≥ 1, Ω (n + k) ≤ C * k

/-- Failure of the natural-valued Ω estimate at one relevant shift. -/
def natOmegaBadAt (C k n : ℕ) : Prop :=
  C * k < Ω (n + k)

/-- Unnormalized weighted mass of one Ω-exceptional shift. -/
def weightedOmegaBadMass (K C k : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico (Erdos248.intervalStart K)
      (2 * Erdos248.intervalStart K),
    if natOmegaBadAt C k n then Erdos248.sieveWeight K n else 0

theorem weightedOmegaBadMass_nonneg (K C k : ℕ) :
    0 ≤ weightedOmegaBadMass K C k := by
  unfold weightedOmegaBadMass
  apply Finset.sum_nonneg
  intro n hn
  split_ifs
  · exact Erdos248.sieveWeight_nonneg K n
  · exact le_rfl

/-- If the total weighted mass of the finitely many relevant Ω-exceptions is
smaller than the sieve mass, one positive-weight point avoids them all. -/
theorem exists_avoids_relevantOmegaBad_shifts {K C : ℕ}
    (hbad :
      (∑ k ∈ Finset.Icc 1 (Erdos248.intervalExponent K),
          weightedOmegaBadMass K C k) <
        Erdos248.sieveMass K) :
    ∃ n ∈ Finset.Ico (Erdos248.intervalStart K)
        (2 * Erdos248.intervalStart K),
      Erdos248.sieveWeight K n ≠ 0 ∧
        ∀ k ∈ Finset.Icc 1 (Erdos248.intervalExponent K),
          Ω (n + k) ≤ C * k := by
  classical
  by_contra hnot
  push Not at hnot
  have hpoint : ∀ n ∈ Finset.Ico (Erdos248.intervalStart K)
      (2 * Erdos248.intervalStart K),
      Erdos248.sieveWeight K n ≤
        ∑ k ∈ Finset.Icc 1 (Erdos248.intervalExponent K),
          if natOmegaBadAt C k n then Erdos248.sieveWeight K n else 0 := by
    intro n hn
    by_cases hw : Erdos248.sieveWeight K n = 0
    · simp [hw]
    · obtain ⟨k, hk, hkbad⟩ := hnot n hn hw
      have hterm :
          Erdos248.sieveWeight K n =
            (if natOmegaBadAt C k n then Erdos248.sieveWeight K n else 0) := by
        rw [if_pos]
        exact hkbad
      calc
        Erdos248.sieveWeight K n =
            (if natOmegaBadAt C k n then Erdos248.sieveWeight K n else 0) :=
          hterm
        _ ≤ ∑ j ∈ Finset.Icc 1 (Erdos248.intervalExponent K),
            if natOmegaBadAt C j n then Erdos248.sieveWeight K n else 0 := by
          exact Finset.single_le_sum
            (s := Finset.Icc 1 (Erdos248.intervalExponent K))
            (f := fun j =>
              if natOmegaBadAt C j n then Erdos248.sieveWeight K n else 0)
            (fun j hj => by
              split_ifs
              · exact Erdos248.sieveWeight_nonneg K n
              · exact le_rfl) hk
  have hsum : Erdos248.sieveMass K ≤
      ∑ n ∈ Finset.Ico (Erdos248.intervalStart K)
          (2 * Erdos248.intervalStart K),
        ∑ k ∈ Finset.Icc 1 (Erdos248.intervalExponent K),
          if natOmegaBadAt C k n then Erdos248.sieveWeight K n else 0 := by
    unfold Erdos248.sieveMass BoundedGaps.Maynard.sieveWeightSum
    exact Finset.sum_le_sum fun n hn => hpoint n hn
  have hswap :
      (∑ n ∈ Finset.Ico (Erdos248.intervalStart K)
          (2 * Erdos248.intervalStart K),
        ∑ k ∈ Finset.Icc 1 (Erdos248.intervalExponent K),
          if natOmegaBadAt C k n then Erdos248.sieveWeight K n else 0) =
      ∑ k ∈ Finset.Icc 1 (Erdos248.intervalExponent K),
        weightedOmegaBadMass K C k := by
    unfold weightedOmegaBadMass
    rw [Finset.sum_comm]
  rw [hswap] at hsum
  exact (not_lt_of_ge hsum) hbad

/-- The finite Ω-exceptional-mass estimate gives a point good at every
positive shift. -/
theorem exists_isOmegaGood_of_weightedOmegaBadMass {K C : ℕ}
    (hC : 2 ≤ C)
    (hbad :
      (∑ k ∈ Finset.Icc 1 (Erdos248.intervalExponent K),
          weightedOmegaBadMass K C k) <
        Erdos248.sieveMass K) :
    ∃ n : ℕ, Erdos248.intervalStart K ≤ n ∧
      n < 2 * Erdos248.intervalStart K ∧ IsOmegaGood (C : ℝ) n := by
  obtain ⟨n, hnrange, hnweight, hgood⟩ :=
    exists_avoids_relevantOmegaBad_shifts hbad
  have hn := Finset.mem_Ico.mp hnrange
  refine ⟨n, hn.1, hn.2, ?_⟩
  intro k hk1
  by_cases hkM : k ≤ Erdos248.intervalExponent K
  · have hknat := hgood k (Finset.mem_Icc.mpr ⟨hk1, hkM⟩)
    exact_mod_cast hknat
  · have hLk : Erdos248.intervalExponent K + 1 ≤ k := by omega
    have hnPow : n ≤ 2 ^ (Erdos248.intervalExponent K + 1) := by
      have : 2 * Erdos248.intervalStart K =
          2 ^ (Erdos248.intervalExponent K + 1) := by
        rw [Erdos248.intervalStart, pow_succ]
        ring
      omega
    have hfar := Omega_add_le_two_mul_of_le_pow hnPow hLk hk1
    have hCle : 2 * k ≤ C * k := Nat.mul_le_mul_right k hC
    exact_mod_cast hfar.trans hCle

/-- A uniform finite Ω-exceptional-mass estimate is exactly the remaining
analytic input needed for the Tao--Teräväinen statement. -/
theorem tao_teravainen_of_uniform_weightedOmegaBadMass
    (C : ℕ) (hC : 2 ≤ C)
    (hbad : ∀ {A : ℝ} {K : ℕ}, Erdos248.HasUniformWirsingBound A →
      Erdos248.NormalizationRegular A K →
      (∑ k ∈ Finset.Icc 1 (Erdos248.intervalExponent K),
          weightedOmegaBadMass K C k) <
        Erdos248.sieveMass K) :
    ∃ C' : ℝ, 0 < C' ∧
      (∃ᶠ N in atTop, ∀ k : ℕ, 0 < k →
        (N + k).factorization.support.card ≤
            (N + k).factorization.sum (fun _ e => e) ∧
          (N + k).factorization.sum (fun _ e => e) ≤ C' * k) := by
  refine ⟨(C : ℝ), by exact_mod_cast (show 0 < C by omega), ?_⟩
  rw [Filter.frequently_atTop]
  intro B
  obtain ⟨A, _hApos, hA⟩ := Erdos248.exists_positive_uniformWirsingBound
  obtain ⟨J : ℕ, hAJ⟩ := exists_nat_gt A
  let K : ℕ := B + J + 1
  have hK : 0 < K := by dsimp [K]; omega
  have hAK : A ≤ K := by
    calc
      A ≤ J := hAJ.le
      _ ≤ K := by dsimp [K]; exact_mod_cast (show J ≤ B + J + 1 by omega)
  have hreg : Erdos248.NormalizationRegular A K :=
    Erdos248.normalizationRegular_of_le_dimension hK hAK
  obtain ⟨n, hnlow, _hnhigh, hgood⟩ :=
    exists_isOmegaGood_of_weightedOmegaBadMass hC (hbad hA hreg)
  refine ⟨n, ?_, ?_⟩
  · exact (Erdos248.intervalStart_gt_of_lt_dimension (B := B) (K := K)
      (by dsimp [K]; omega)).le.trans hnlow
  · intro k hk
    refine ⟨support_card_le_factorization_sum (n + k), ?_⟩
    rw [factorization_sum_eq_Omega]
    exact hgood k hk

end TaoTeravainen
