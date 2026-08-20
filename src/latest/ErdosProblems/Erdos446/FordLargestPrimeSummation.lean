/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.FordClusterLogMoments

/-!
# Erdős Problem 446: summation by the largest prime

The final partial-summation step in Ford--Koukoulopoulos Lemma 3.3 can be
performed discretely by marking the largest prime factor.  Deleting that
factor leaves a support made only of smaller primes.  The cubic moment bound
at the smaller cutoff then cancels two powers of the largest-prime logarithm,
leaving the prime Mertens sum `sum log p / p`.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

/-- Maximum of a finite natural support, with value zero on the empty set. -/
def primeSupportMax (S : Finset ℕ) : ℕ := S.sup id

theorem primeSupportMax_eq_max' {S : Finset ℕ} (hS : S.Nonempty) :
    primeSupportMax S = S.max' hS := by
  rw [primeSupportMax, ← Finset.sup'_eq_sup hS id]
  rfl

theorem primeSupportMax_mem {S : Finset ℕ} (hS : S.Nonempty) :
    primeSupportMax S ∈ S := by
  rw [primeSupportMax_eq_max' hS]
  exact Finset.max'_mem S hS

theorem le_primeSupportMax {S : Finset ℕ} {p : ℕ} (hp : p ∈ S) :
    p ≤ primeSupportMax S := by
  exact Finset.le_sup (f := fun n : ℕ ↦ n) hp

/-- Nonempty squarefree supports at the cutoff. -/
def nonemptySmoothSupports (P : ℕ) : Finset (Finset ℕ) :=
  (primesUpTo P).powerset.filter Finset.Nonempty

/-- The dependent target of largest-prime deletion: a largest prime `p`
and an arbitrary support made of primes at most `p`. -/
def largestPrimeDeletionTargets (P : ℕ) :
    Finset ((p : ℕ) × Finset ℕ) :=
  (primesUpTo P).sigma fun p ↦ (primesUpTo p).powerset

/-- Delete the maximum from a nonempty support.  Proof irrelevance makes the
chosen nonemptiness witness immaterial. -/
def deleteSupportMaximum (S : Finset ℕ) : (p : ℕ) × Finset ℕ :=
  ⟨primeSupportMax S, S.erase (primeSupportMax S)⟩

private theorem deleteSupportMaximum_injective :
    Set.InjOn deleteSupportMaximum {S : Finset ℕ | S.Nonempty} := by
  intro S hS T hT hEq
  have hmax : primeSupportMax S = primeSupportMax T :=
    congrArg Sigma.fst hEq
  have herase : S.erase (primeSupportMax S) =
      T.erase (primeSupportMax T) := congrArg Sigma.snd hEq
  calc
    S = insert (primeSupportMax S) (S.erase (primeSupportMax S)) :=
      (Finset.insert_erase (primeSupportMax_mem hS)).symm
    _ = insert (primeSupportMax T) (T.erase (primeSupportMax T)) := by
      rw [herase, hmax]
    _ = T := Finset.insert_erase (primeSupportMax_mem hT)

private theorem erase_max_subset_primesUpTo
    {P : ℕ} {S : Finset ℕ} (hSP : S ⊆ primesUpTo P)
    (hS : S.Nonempty) :
    S.erase (primeSupportMax S) ⊆ primesUpTo (primeSupportMax S) := by
  intro q hq
  have hqS : q ∈ S := Finset.mem_of_mem_erase hq
  have hqPrime : q.Prime := prime_of_mem_primesUpTo (hSP hqS)
  rw [primesUpTo, Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨hqPrime.two_le, le_primeSupportMax hqS⟩, hqPrime⟩

theorem deleteSupportMaximum_mem_targets
    {P : ℕ} {S : Finset ℕ} (hS : S ∈ nonemptySmoothSupports P) :
    deleteSupportMaximum S ∈ largestPrimeDeletionTargets P := by
  have hSP : S ⊆ primesUpTo P :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
  have hSne : S.Nonempty := (Finset.mem_filter.mp hS).2
  rw [largestPrimeDeletionTargets, Finset.mem_sigma]
  exact ⟨hSP (primeSupportMax_mem hSne),
    Finset.mem_powerset.mpr (erase_max_subset_primesUpTo hSP hSne)⟩

/-- Cubic moment divided by the squared logarithm of the largest prime. -/
noncomputable def largestPrimeWeightedClusterMoment (P : ℕ) : ℝ :=
  ∑ S ∈ nonemptySmoothSupports P,
    primeSubsetClusterTerm S * Real.log ((S.prod id : ℕ) : ℝ) ^ 3 /
      Real.log (primeSupportMax S : ℝ) ^ 2

/-- The enlarged summand after deleting the largest prime. -/
noncomputable def largestPrimeDeletionTerm
    (z : (p : ℕ) × Finset ℕ) : ℝ :=
  (2 / (z.1 : ℝ)) * primeSubsetClusterTerm z.2 *
      (Real.log ((z.2.prod id : ℕ) : ℝ) + Real.log (z.1 : ℝ)) ^ 3 /
    Real.log (z.1 : ℝ) ^ 2

theorem largestPrimeDeletionTerm_nonneg
    {z : (p : ℕ) × Finset ℕ}
    (hp : z.1.Prime) (hT : z.2 ⊆ primesUpTo z.1) :
    0 ≤ largestPrimeDeletionTerm z := by
  have hTpos : 0 < z.2.prod id := primeSubset_product_pos hT
  have hlogT : 0 ≤ Real.log ((z.2.prod id : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hTpos)
  have hlogp : 0 < Real.log (z.1 : ℝ) := hp.log_pos
  unfold largestPrimeDeletionTerm
  apply div_nonneg
  · apply mul_nonneg
    · exact mul_nonneg (div_nonneg (by norm_num) (Nat.cast_nonneg _))
        (primeSubsetClusterTerm_nonneg z.2)
    · exact pow_nonneg (add_nonneg hlogT hlogp.le) _
  · exact sq_nonneg _

private theorem largestPrime_source_le_deleted
    {P : ℕ} {S : Finset ℕ} (hS : S ∈ nonemptySmoothSupports P) :
    primeSubsetClusterTerm S * Real.log ((S.prod id : ℕ) : ℝ) ^ 3 /
        Real.log (primeSupportMax S : ℝ) ^ 2 ≤
      largestPrimeDeletionTerm (deleteSupportMaximum S) := by
  have hSP : S ⊆ primesUpTo P :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
  have hSne : S.Nonempty := (Finset.mem_filter.mp hS).2
  let p := primeSupportMax S
  let T := S.erase p
  have hpS : p ∈ S := primeSupportMax_mem hSne
  have hpPrime : p.Prime := prime_of_mem_primesUpTo (hSP hpS)
  have hTsub : T ⊆ primesUpTo P := (Finset.erase_subset p S).trans hSP
  have hlogS :
      Real.log ((S.prod id : ℕ) : ℝ) =
        Real.log ((T.prod id : ℕ) : ℝ) + Real.log (p : ℝ) := by
    rw [log_primeSubset_product hSP, log_primeSubset_product hTsub,
      ← Finset.sum_erase_add _ _ hpS]
  have hdelete : primeSubsetClusterTerm S ≤
      (2 / (p : ℝ)) * primeSubsetClusterTerm T :=
    primeSubsetClusterTerm_le_delete hSP hpS
  have hden : 0 ≤ Real.log (p : ℝ) ^ 2 := sq_nonneg _
  have hpow : 0 ≤
      (Real.log ((T.prod id : ℕ) : ℝ) + Real.log (p : ℝ)) ^ 3 := by
    have hTpos : 0 < T.prod id := primeSubset_product_pos hTsub
    have hlogT : 0 ≤ Real.log ((T.prod id : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hTpos)
    have hlogp : 0 ≤ Real.log (p : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hpPrime.one_le)
    positivity
  rw [hlogS]
  unfold largestPrimeDeletionTerm deleteSupportMaximum
  dsimp only [Sigma.fst, Sigma.snd]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hdelete hpow) hden

/-- Largest-prime deletion embeds the weighted cubic moment into a dependent
sum over the remaining smaller-prime supports. -/
theorem largestPrimeWeightedClusterMoment_le_deletionSum (P : ℕ) :
    largestPrimeWeightedClusterMoment P ≤
      ∑ z ∈ largestPrimeDeletionTargets P, largestPrimeDeletionTerm z := by
  let Q := nonemptySmoothSupports P
  have hinj : Set.InjOn deleteSupportMaximum Q := by
    intro S hS T hT
    exact deleteSupportMaximum_injective
      (Finset.mem_filter.mp hS).2 (Finset.mem_filter.mp hT).2
  have himage : Q.image deleteSupportMaximum ⊆
      largestPrimeDeletionTargets P := by
    intro z hz
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hz
    exact deleteSupportMaximum_mem_targets hS
  calc
    largestPrimeWeightedClusterMoment P ≤
        ∑ S ∈ Q, largestPrimeDeletionTerm (deleteSupportMaximum S) := by
      unfold largestPrimeWeightedClusterMoment
      exact Finset.sum_le_sum fun S hS ↦ largestPrime_source_le_deleted hS
    _ = ∑ z ∈ Q.image deleteSupportMaximum,
        largestPrimeDeletionTerm z := by
      rw [Finset.sum_image hinj]
    _ ≤ ∑ z ∈ largestPrimeDeletionTargets P,
        largestPrimeDeletionTerm z :=
      Finset.sum_le_sum_of_subset_of_nonneg himage (by
        intro z hz hnot
        have hp : z.1.Prime := prime_of_mem_primesUpTo
          (Finset.mem_sigma.mp hz).1
        have hT : z.2 ⊆ primesUpTo z.1 :=
          Finset.mem_powerset.mp (Finset.mem_sigma.mp hz).2
        exact largestPrimeDeletionTerm_nonneg hp hT)

theorem squarefreeClusterMass_mono {p P : ℕ} (hpP : p ≤ P) :
    squarefreeClusterMass p ≤ squarefreeClusterMass P := by
  rw [squarefreeClusterMass_eq_powersetMoment_zero,
    squarefreeClusterMass_eq_powersetMoment_zero]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.powerset_mono.mpr (by
      intro q hq
      have hqData := Finset.mem_filter.mp hq
      exact Finset.mem_filter.mpr ⟨
        Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hqData.1).1,
          (Finset.mem_Icc.mp hqData.1).2.trans hpP⟩,
        hqData.2⟩)
  · intro S hS hnot
    simpa [powersetAdditiveMoment] using primeSubsetClusterTerm_nonneg S

/-- The largest-prime weighted cubic moment is only `O(log P)` times the
unweighted squarefree cluster mass.  This is the finite partial-summation
estimate used in Lemma 3.3. -/
theorem exists_pos_largestPrimeWeightedClusterMoment_le :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℕ, 2 ≤ P →
      largestPrimeWeightedClusterMoment P ≤
        C * Real.log (P : ℝ) * squarefreeClusterMass P := by
  obtain ⟨C₃, hC₃, hthird⟩ :=
    exists_pos_squarefreeClusterLogMoment_le
  obtain ⟨K, hK, hfirst⟩ := exists_pos_weightedPrimeLogMass_le_log
  let C : ℝ := 8 * (C₃ + 1) * K
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, fun P hP ↦ ?_⟩
  have hMassP : 0 ≤ squarefreeClusterMass P := by
    rw [squarefreeClusterMass_eq_powersetMoment_zero]
    exact Finset.sum_nonneg fun S hS ↦ by
      simpa [powersetAdditiveMoment] using primeSubsetClusterTerm_nonneg S
  calc
    largestPrimeWeightedClusterMoment P ≤
        ∑ z ∈ largestPrimeDeletionTargets P,
          largestPrimeDeletionTerm z :=
      largestPrimeWeightedClusterMoment_le_deletionSum P
    _ = ∑ p ∈ primesUpTo P,
        ∑ T ∈ (primesUpTo p).powerset,
          (2 / (p : ℝ)) * primeSubsetClusterTerm T *
              (Real.log ((T.prod id : ℕ) : ℝ) + Real.log (p : ℝ)) ^ 3 /
            Real.log (p : ℝ) ^ 2 := by
      rw [largestPrimeDeletionTargets, Finset.sum_sigma]
      rfl
    _ ≤ ∑ p ∈ primesUpTo P,
        (8 * (C₃ + 1)) *
          (Real.log (p : ℝ) / (p : ℝ)) * squarefreeClusterMass P := by
      apply Finset.sum_le_sum
      intro p hp
      have hpPrime : p.Prime := prime_of_mem_primesUpTo hp
      have hp2 : 2 ≤ p := hpPrime.two_le
      have hpP : p ≤ P := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
      have hlogp : 0 < Real.log (p : ℝ) := hpPrime.log_pos
      have hMassp : 0 ≤ squarefreeClusterMass p := by
        rw [squarefreeClusterMass_eq_powersetMoment_zero]
        exact Finset.sum_nonneg fun S hS ↦ by
          simpa [powersetAdditiveMoment] using primeSubsetClusterTerm_nonneg S
      have hsumCube :
          (∑ T ∈ (primesUpTo p).powerset,
            primeSubsetClusterTerm T *
              (Real.log ((T.prod id : ℕ) : ℝ) + Real.log (p : ℝ)) ^ 3) ≤
            4 * (C₃ + 1) * Real.log (p : ℝ) ^ 3 *
              squarefreeClusterMass p := by
        calc
          (∑ T ∈ (primesUpTo p).powerset,
            primeSubsetClusterTerm T *
              (Real.log ((T.prod id : ℕ) : ℝ) + Real.log (p : ℝ)) ^ 3) ≤
              ∑ T ∈ (primesUpTo p).powerset,
                4 * (primeSubsetClusterTerm T *
                    Real.log ((T.prod id : ℕ) : ℝ) ^ 3 +
                  primeSubsetClusterTerm T * Real.log (p : ℝ) ^ 3) := by
            apply Finset.sum_le_sum
            intro T hT
            have hTsub : T ⊆ primesUpTo p := Finset.mem_powerset.mp hT
            have hTpos : 0 < T.prod id := primeSubset_product_pos hTsub
            have hx : 0 ≤ Real.log ((T.prod id : ℕ) : ℝ) :=
              Real.log_nonneg (by exact_mod_cast hTpos)
            have hy : 0 ≤ Real.log (p : ℝ) := hlogp.le
            have hcube :
                (Real.log ((T.prod id : ℕ) : ℝ) + Real.log (p : ℝ)) ^ 3 ≤
                  4 * (Real.log ((T.prod id : ℕ) : ℝ) ^ 3 +
                    Real.log (p : ℝ) ^ 3) := by
              have hsum : 0 ≤ Real.log ((T.prod id : ℕ) : ℝ) +
                  Real.log (p : ℝ) := add_nonneg hx hy
              have hsq := sq_nonneg
                (Real.log ((T.prod id : ℕ) : ℝ) - Real.log (p : ℝ))
              have hcore :
                  Real.log ((T.prod id : ℕ) : ℝ) * Real.log (p : ℝ) *
                      (Real.log ((T.prod id : ℕ) : ℝ) + Real.log (p : ℝ)) ≤
                    Real.log ((T.prod id : ℕ) : ℝ) ^ 3 +
                      Real.log (p : ℝ) ^ 3 := by
                nlinarith [mul_nonneg hsum hsq]
              nlinarith
            calc
              primeSubsetClusterTerm T *
                    (Real.log ((T.prod id : ℕ) : ℝ) +
                      Real.log (p : ℝ)) ^ 3 ≤
                  primeSubsetClusterTerm T *
                    (4 * (Real.log ((T.prod id : ℕ) : ℝ) ^ 3 +
                      Real.log (p : ℝ) ^ 3)) :=
                mul_le_mul_of_nonneg_left hcube
                  (primeSubsetClusterTerm_nonneg T)
              _ = 4 * (primeSubsetClusterTerm T *
                    Real.log ((T.prod id : ℕ) : ℝ) ^ 3 +
                  primeSubsetClusterTerm T * Real.log (p : ℝ) ^ 3) := by
                ring
          _ = 4 * (squarefreeClusterLogMoment p +
                Real.log (p : ℝ) ^ 3 * squarefreeClusterMass p) := by
            rw [← Finset.mul_sum, Finset.sum_add_distrib]
            unfold squarefreeClusterLogMoment
            rw [squarefreeClusterMass_eq_powersetMoment_zero]
            simp only [powersetAdditiveMoment, pow_zero, mul_one]
            rw [← Finset.sum_mul]
            ring
          _ ≤ 4 * (C₃ * Real.log (p : ℝ) ^ 3 *
                squarefreeClusterMass p +
              Real.log (p : ℝ) ^ 3 * squarefreeClusterMass p) := by
            gcongr
            exact hthird p hp2
          _ = 4 * (C₃ + 1) * Real.log (p : ℝ) ^ 3 *
              squarefreeClusterMass p := by ring
      have hfactor :
          (∑ T ∈ (primesUpTo p).powerset,
            (2 / (p : ℝ)) * primeSubsetClusterTerm T *
                (Real.log ((T.prod id : ℕ) : ℝ) + Real.log (p : ℝ)) ^ 3 /
              Real.log (p : ℝ) ^ 2) =
            ((2 / (p : ℝ)) / Real.log (p : ℝ) ^ 2) *
              (∑ T ∈ (primesUpTo p).powerset,
                primeSubsetClusterTerm T *
                  (Real.log ((T.prod id : ℕ) : ℝ) +
                    Real.log (p : ℝ)) ^ 3) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro T hT
        ring
      rw [hfactor]
      calc
        ((2 / (p : ℝ)) / Real.log (p : ℝ) ^ 2) *
            (∑ T ∈ (primesUpTo p).powerset,
              primeSubsetClusterTerm T *
                (Real.log ((T.prod id : ℕ) : ℝ) + Real.log (p : ℝ)) ^ 3) ≤
            ((2 / (p : ℝ)) / Real.log (p : ℝ) ^ 2) *
              (4 * (C₃ + 1) * Real.log (p : ℝ) ^ 3 *
                squarefreeClusterMass p) := by
          gcongr
        _ = (8 * (C₃ + 1)) *
              (Real.log (p : ℝ) / (p : ℝ)) *
                squarefreeClusterMass p := by
          field_simp [hlogp.ne', (by exact_mod_cast hpPrime.ne_zero :
            (p : ℝ) ≠ 0)]
          <;> ring
        _ ≤ (8 * (C₃ + 1)) *
              (Real.log (p : ℝ) / (p : ℝ)) *
                squarefreeClusterMass P := by
          gcongr
          exact squarefreeClusterMass_mono hpP
    _ = (8 * (C₃ + 1)) * weightedPrimeLogMass P *
        squarefreeClusterMass P := by
      rw [weightedPrimeLogMass, Finset.mul_sum, Finset.sum_mul]
    _ ≤ (8 * (C₃ + 1)) * (K * Real.log (P : ℝ)) *
        squarefreeClusterMass P := by
      gcongr
      exact hfirst P hP
    _ = C * Real.log (P : ℝ) * squarefreeClusterMass P := by
      dsimp [C]
      ring

end Erdos446
