/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos946.WeightedAverage
import ErdosProblems.Erdos697.Erdos697PrimeWindow

/-! # The squarefree exception in the affine sieve -/

open scoped BigOperators

namespace Erdos946.SquarefreeSieve

open Erdos851 AffineSieve

noncomputable section

def affineDivisibleCandidates (a b X d : ℕ) : Finset ℕ :=
  (Finset.Ioc X (2 * X)).filter fun n ↦ d ∣ a * n + b

theorem affineRootResidues_card_le_one_of_coprime {a b d : ℕ}
    (had : a.Coprime d) : (Erdos822.affineRootResidues a b d).card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro r s hr hs
  have hr' := Erdos822.mem_affineRootResidues_iff.mp hr
  have hs' := Erdos822.mem_affineRootResidues_iff.mp hs
  have hzero : a * r + b ≡ 0 [MOD d] := hr'.2.modEq_zero_nat
  have hzero' : a * s + b ≡ 0 [MOD d] := hs'.2.modEq_zero_nat
  have hmul : a * r ≡ a * s [MOD d] :=
    Nat.ModEq.add_right_cancel' b (hzero.trans hzero'.symm)
  have hrs : r ≡ s [MOD d] := hmul.cancel_left_of_coprime had.symm.gcd_eq_one
  exact (Nat.mod_eq_of_lt hr'.1).symm.trans (Nat.mod_eq_of_modEq hrs hs'.1)

theorem affineDivisibleCandidates_eq_modularPreimage {a b X d : ℕ} (hd : 0 < d) :
    affineDivisibleCandidates a b X d =
      Erdos387.modularPreimageIoc X (2 * X) d (Erdos822.affineRootResidues a b d) := by
  ext n
  simp only [affineDivisibleCandidates, Erdos387.modularPreimageIoc,
    Finset.mem_filter, Erdos822.mem_affineRootResidues_iff]
  have hmod : (a * (n % d) + b) % d = (a * n + b) % d := by
    simp [Nat.add_mod, Nat.mul_mod]
  simp only [Nat.dvd_iff_mod_eq_zero, hmod, Nat.mod_lt n hd, true_and]

theorem affineDivisibleCandidates_card_le {a b X d : ℕ} (hd : 0 < d)
    (had : a.Coprime d) :
    ((affineDivisibleCandidates a b X d).card : ℝ) ≤ (X : ℝ) / d + 1 := by
  let R := Erdos822.affineRootResidues a b d
  have hcard : (R.card : ℝ) ≤ 1 := by
    exact_mod_cast affineRootResidues_card_le_one_of_coprime (b := b) had
  have hcount := Erdos851.ShiftSieve.abs_card_modularPreimageIoc_dyadic_sub_density
    (X := X) hd R (fun r hr ↦ (Erdos822.mem_affineRootResidues_iff.mp hr).1)
  rw [← affineDivisibleCandidates_eq_modularPreimage hd] at hcount
  have hmain : (R.card : ℝ) * X / d ≤ (X : ℝ) / d := by
    simpa only [one_mul, mul_div_assoc] using
      mul_le_mul_of_nonneg_right hcard (div_nonneg (Nat.cast_nonneg X) (Nat.cast_nonneg d))
  have hu := (abs_le.mp hcount).2
  linarith

def squarefreeCandidates (S : Finset ℕ) (F : ℕ → ℕ) : Finset ℕ :=
  S.filter fun n ↦ Squarefree (F n)

def nonsquarefreeCandidates (S : Finset ℕ) (F : ℕ → ℕ) : Finset ℕ :=
  S.filter fun n ↦ ¬Squarefree (F n)

theorem card_squarefree_add_nonsquarefree (S : Finset ℕ) (F : ℕ → ℕ) :
    (squarefreeCandidates S F).card + (nonsquarefreeCandidates S F).card = S.card := by
  exact Finset.card_filter_add_card_filter_not (s := S) (fun n ↦ Squarefree (F n))

theorem exists_prime_square_dvd_factor_of_not_squarefree
    {a b : Fin 16 → ℕ} {n : ℕ}
    (hpair : Pairwise fun i j ↦ (a i * n + b i).Coprime (a j * n + b j))
    (hnot : ¬Squarefree (affineProduct a b n)) :
    ∃ i : Fin 16, ∃ p : ℕ, p.Prime ∧ p ^ 2 ∣ a i * n + b i := by
  have hi : ∃ i : Fin 16, ¬Squarefree (a i * n + b i) := by
    by_contra h
    push Not at h
    apply hnot
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro i _ j _ hij
      exact Nat.coprime_iff_isRelPrime.mp (hpair hij)
    · intro i _
      exact h i
  obtain ⟨i, hi⟩ := hi
  have hp : ∃ p : ℕ, p.Prime ∧ p * p ∣ a i * n + b i := by
    by_contra h
    apply hi
    rw [Nat.squarefree_iff_prime_squarefree]
    intro p hp hdiv
    exact h ⟨p, hp, hdiv⟩
  obtain ⟨p, hp, hdiv⟩ := hp
  exact ⟨i, p, hp, by simpa only [pow_two] using hdiv⟩

/-- A finite bound for the nonsquarefree part of a rough affine family.
`B²` bounds each individual factor on the parameter set. -/
theorem nonsquarefreeCandidates_card_le
    (S : Finset ℕ) {a b : Fin 16 → ℕ} {X y B : ℕ}
    (hy : 1 ≤ y)
    (hI : S ⊆ Finset.Ioc X (2 * X))
    (hpos : ∀ n ∈ S, ∀ i, 0 < a i * n + b i)
    (hsize : ∀ n ∈ S, ∀ i, a i * n + b i ≤ B ^ 2)
    (hpair : ∀ n ∈ S, Pairwise fun i j ↦
      (a i * n + b i).Coprime (a j * n + b j))
    (hrough : ∀ n ∈ S, ∀ p : ℕ, p.Prime → p ≤ y → ¬p ∣ affineProduct a b n)
    (hcop : ∀ p : ℕ, p.Prime → y < p → ∀ i, (a i).Coprime p) :
    ((nonsquarefreeCandidates S (affineProduct a b)).card : ℝ) ≤
      16 * ((X : ℝ) / y + B) := by
  let P := sievePrimes y B
  let U := (Finset.univ : Finset (Fin 16)).biUnion fun i ↦
    P.biUnion fun p ↦ affineDivisibleCandidates (a i) (b i) X (p ^ 2)
  have hsub : nonsquarefreeCandidates S (affineProduct a b) ⊆ U := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    obtain ⟨i, p, hp, hpdiv⟩ :=
      exists_prime_square_dvd_factor_of_not_squarefree (hpair n hn'.1) hn'.2
    have hpFactor : p ∣ a i * n + b i :=
      (dvd_pow_self p (by norm_num : 2 ≠ 0)).trans hpdiv
    have hpF : p ∣ affineProduct a b n := hpFactor.trans
      (Finset.dvd_prod_of_mem (f := fun i ↦ a i * n + b i) (Finset.mem_univ i))
    have hyp : y < p := by
      by_contra h
      exact hrough n hn'.1 p hp (Nat.le_of_not_gt h) hpF
    have hpB : p ≤ B := by
      have hsq := (Nat.le_of_dvd (hpos n hn'.1 i) hpdiv).trans (hsize n hn'.1 i)
      nlinarith
    apply Finset.mem_biUnion.mpr
    refine ⟨i, Finset.mem_univ i, Finset.mem_biUnion.mpr ?_⟩
    exact ⟨p, mem_sievePrimes.mpr ⟨hyp, hpB, hp⟩,
      Finset.mem_filter.mpr ⟨hI hn'.1, hpdiv⟩⟩
  have hcard : (nonsquarefreeCandidates S (affineProduct a b)).card ≤
      ∑ i : Fin 16, ∑ p ∈ P,
        (affineDivisibleCandidates (a i) (b i) X (p ^ 2)).card := by
    calc
      _ ≤ U.card := Finset.card_le_card hsub
      _ ≤ ∑ i : Fin 16, (P.biUnion fun p ↦
          affineDivisibleCandidates (a i) (b i) X (p ^ 2)).card :=
        Finset.card_biUnion_le
      _ ≤ _ := Finset.sum_le_sum fun i _ ↦ Finset.card_biUnion_le
  have htail : (∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2) ≤ 1 / (y : ℝ) :=
    Erdos697.PrimeWindow.squareReciprocalMass_le hy
  have hPcard : (P.card : ℝ) ≤ B := by
    exact_mod_cast (Finset.card_filter_le (Finset.Ioc y B) Nat.Prime).trans
      (by simp : (Finset.Ioc y B).card ≤ B)
  calc
    ((nonsquarefreeCandidates S (affineProduct a b)).card : ℝ) ≤
        ∑ i : Fin 16, ∑ p ∈ P,
          ((affineDivisibleCandidates (a i) (b i) X (p ^ 2)).card : ℝ) := by
      exact_mod_cast hcard
    _ ≤ ∑ i : Fin 16, ∑ p ∈ P, ((X : ℝ) / (p : ℝ) ^ 2 + 1) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro p hp
      have hp' := mem_sievePrimes.mp hp
      simpa only [Nat.cast_pow] using affineDivisibleCandidates_card_le
        (b := b i) (X := X) (pow_pos hp'.2.2.pos 2)
        ((hcop p hp'.2.2 hp'.1 i).pow_right 2)
    _ = 16 * ((X : ℝ) * (∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2) + P.card) := by
      simp_rw [show ∀ p : ℕ, (X : ℝ) / (p : ℝ) ^ 2 + 1 =
        X * (1 / (p : ℝ) ^ 2) + 1 by intro p; ring]
      simp [Finset.sum_add_distrib, ← Finset.mul_sum]
      ring
    _ ≤ 16 * ((X : ℝ) / y + B) := by
      have hmul := mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg X)
      simp only [mul_one_div] at hmul
      nlinarith

end

end Erdos946.SquarefreeSieve
