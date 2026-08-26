/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierFiniteIntegral

/-!
# Compact profile support and stabilization of the divisor cutoff

Compactness of the logarithmic profiles bounds every divisor coordinate
of a nonzero coefficient tensor. Extending the prime cutoff past these
coordinates changes neither compatibility nor the finite Selberg sum.
-/

namespace Erdos4b

noncomputable section

noncomputable local instance supportCutoffDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

open scoped BigOperators

theorem exists_logProfile_nat_bound (F : ℝ → ℂ) (hF : HasCompactSupport F)
    {L : ℝ} (hL : 0 < L) :
    ∃ N : ℕ, ∀ d : ℕ, 0 < d → F (Real.log d / L) ≠ 0 → d ≤ N := by
  obtain ⟨A, hA⟩ := hF.isCompact.bddAbove
  refine ⟨⌈Real.exp (L * A)⌉₊, ?_⟩
  intro d hd hFd
  have hlogL : Real.log (d : ℝ) / L ≤ A := hA (subset_tsupport F hFd)
  have hlog : Real.log (d : ℝ) ≤ L * A := by
    have h := (div_le_iff₀ hL).mp hlogL
    simpa only [mul_comm] using h
  have hdexp := (Real.log_le_iff_le_exp (by exact_mod_cast hd)).mp hlog
  exact_mod_cast hdexp.trans (Nat.le_ceil (Real.exp (L * A)))

theorem exists_doubledSelbergProfileTensor_bound {ι : Type*} [Fintype ι]
    (F : ((ι ⊕ ι) × Bool) → ℝ → ℂ) (hF : ∀ ib, HasCompactSupport (F ib))
    (L : (ι ⊕ ι) → Bool → ℝ) (hL : ∀ i b, 0 < L i b) :
    ∃ B : ℕ, ∀ d : (ι ⊕ ι) → Bool → ℕ,
      (∀ i b, 0 < d i b) → doubledSelbergProfileTensor F L d ≠ 0 → ∀ i b, d i b ≤ B := by
  classical
  choose N hN using fun ib : (ι ⊕ ι) × Bool ↦
    exists_logProfile_nat_bound (F ib) (hF ib) (hL ib.1 ib.2)
  refine ⟨∑ ib, N ib, ?_⟩
  intro d hd hcoef i b
  have hterm : (ArithmeticFunction.moebius (d i b) : ℂ) * F (i, b) (Real.log (d i b) / L i b) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hcoef) (i, b) (Finset.mem_univ _)
  exact (hN (i, b) (d i b) (hd i b) (mul_ne_zero_iff.mp hterm).2).trans
    (Finset.single_le_sum (fun ib hib ↦ Nat.zero_le (N ib)) (Finset.mem_univ (i, b)))

theorem doubledCutoffDivisorTuples_mono {ι : Type*} [Fintype ι]
    {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ p ∈ Q, p.Prime) (hPQ : P ⊆ Q) :
    doubledCutoffDivisorTuples ι P ⊆ doubledCutoffDivisorTuples ι Q := by
  intro d hd
  obtain ⟨hdiv, hcop⟩ := (mem_doubledCutoffDivisorTuples P hP d).mp hd
  exact (mem_doubledCutoffDivisorTuples Q hQ d).mpr
    ⟨fun i b ↦ (hdiv i b).trans (Finset.prod_dvd_prod_of_subset P Q id hPQ), hcop⟩

theorem doubledDivisorPrimeCompatible_cutoff_iff {ι : Type*} [Fintype ι]
    {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ p ∈ Q, p.Prime) (hPQ : P ⊆ Q)
    (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (d : (ι ⊕ ι) → Bool → ℕ) (hd : d ∈ doubledCutoffDivisorTuples ι P) :
    DoubledDivisorPrimeCompatible P edges companion d ↔
      DoubledDivisorPrimeCompatible Q edges companion d := by
  have hdiv := ((mem_doubledCutoffDivisorTuples P hP d).mp hd).1
  constructor
  · intro h p
    by_cases hpP : p.val ∈ P
    · exact h ⟨p.val, hpP⟩
    · have hnot (i : ι ⊕ ι) : ¬p.val ∣ Nat.lcm (d i false) (d i true) := by
        intro hpD
        exact hpP ((prime_dvd_primeFinsetProduct_iff P hP (hQ p p.property)).mp
          (hpD.trans (Nat.lcm_dvd (hdiv i false) (hdiv i true))))
      exact ⟨fun j hj ↦ (hnot (.inr j) hj).elim, fun i j hi hj ↦ (hnot (.inl i) hi).elim⟩
  · intro h p
    exact h ⟨p.val, hPQ p.property⟩

theorem cutoffSelbergProfileTensorSum_eq_of_capture {ι : Type*} [Fintype ι]
    {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ p ∈ Q, p.Prime) (hPQ : P ⊆ Q)
    (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (F : ((ι ⊕ ι) × Bool) → ℝ → ℂ) (L : (ι ⊕ ι) → Bool → ℝ)
    (hcapture : ∀ d ∈ doubledCutoffDivisorTuples ι Q,
      doubledSelbergProfileTensor F L d ≠ 0 → d ∈ doubledCutoffDivisorTuples ι P) :
    cutoffSelbergProfileTensorSum P edges companion F L =
      cutoffSelbergProfileTensorSum Q edges companion F L := by
  classical
  unfold cutoffSelbergProfileTensorSum
  calc
    _ = ∑ d ∈ doubledCutoffDivisorTuples ι P,
        if DoubledDivisorPrimeCompatible Q edges companion d then
          doubledSelbergProfileTensor F L d /
            ((Finset.univ : Finset ((ι ⊕ ι) × Bool)).lcm (fun ib ↦ d ib.1 ib.2) : ℕ)
        else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [doubledDivisorPrimeCompatible_cutoff_iff hP hQ hPQ edges companion d hd]
    _ = _ := by
      apply Finset.sum_subset (doubledCutoffDivisorTuples_mono hP hQ hPQ)
      intro d hd hdnot
      have hzero : doubledSelbergProfileTensor F L d = 0 := by
        by_contra hn
        exact hdnot (hcapture d hd hn)
      simp [hzero]

theorem bounded_squarefree_dvd_filteredPrimeProduct
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) {d B : ℕ}
    (hsq : Squarefree d) (hdiv : d ∣ ∏ p ∈ P, p) (hdB : d ≤ B) :
    d ∣ ∏ p ∈ P.filter (· ≤ B), p := by
  rw [← Nat.prod_primeFactors_of_squarefree hsq]
  apply Finset.prod_dvd_prod_of_subset
  intro p hp
  have hpData := Nat.mem_primeFactors.mp hp
  exact Finset.mem_filter.mpr
    ⟨(prime_dvd_primeFinsetProduct_iff P hP hpData.1).mp (hpData.2.1.trans hdiv),
      (Nat.le_of_dvd hsq.ne_zero.bot_lt hpData.2.1).trans hdB⟩

theorem exists_cutoffSelbergProfileTensorSum_stabilization {ι : Type*} [Fintype ι]
    (F : ((ι ⊕ ι) × Bool) → ℝ → ℂ) (hF : ∀ ib, HasCompactSupport (F ib))
    (L : (ι ⊕ ι) → Bool → ℝ) (hL : ∀ i b, 0 < L i b) :
    ∃ B : ℕ, ∀ (P : Finset ℕ), (∀ p ∈ P, p.Prime) →
      ∀ (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool),
        cutoffSelbergProfileTensorSum (P.filter (· ≤ B)) edges companion F L =
          cutoffSelbergProfileTensorSum P edges companion F L := by
  obtain ⟨B, hB⟩ := exists_doubledSelbergProfileTensor_bound F hF L hL
  refine ⟨B, ?_⟩
  intro P hP edges companion
  have hsmall : ∀ p ∈ P.filter (· ≤ B), p.Prime :=
    fun p hp ↦ hP p (Finset.mem_filter.mp hp).1
  apply cutoffSelbergProfileTensorSum_eq_of_capture hsmall hP (Finset.filter_subset _ _)
  intro d hd hne
  obtain ⟨hdiv, hcop⟩ := (mem_doubledCutoffDivisorTuples P hP d).mp hd
  have hsq (i) (b) := (primeFinsetProduct_squarefree P hP).squarefree_of_dvd (hdiv i b)
  have hdB := hB d (fun i b ↦ (hsq i b).ne_zero.bot_lt) hne
  exact (mem_doubledCutoffDivisorTuples _ hsmall d).mpr
    ⟨fun i b ↦
      bounded_squarefree_dvd_filteredPrimeProduct P hP (hsq i b) (hdiv i b) (hdB i b), hcop⟩

end

end Erdos4b
