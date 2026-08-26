/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierTotientFiniteIntegral
import ErdosProblems.Erdos4b.GeneralFourierSupportCutoff

/-!
# Compact support and stabilization of the totient divisor sum

The cutoff is chosen with an explicit coordinate-capture property.
This property is independent of the graph and of the arithmetic
denominator, so it can support a common pinned/unpinned cutoff.
-/

namespace Erdos4b

noncomputable section

noncomputable local instance totientSupportDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

open scoped BigOperators

theorem cutoffTotientSelbergProfileTensorSum_eq_of_capture
    {ι : Type*} [Fintype ι] {P Q : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ p ∈ Q, p.Prime) (hPQ : P ⊆ Q)
    (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (F : ((ι ⊕ ι) × Bool) → ℝ → ℂ) (L : (ι ⊕ ι) → Bool → ℝ)
    (hcapture : ∀ d ∈ doubledCutoffDivisorTuples ι Q,
      doubledSelbergProfileTensor F L d ≠ 0 → d ∈ doubledCutoffDivisorTuples ι P) :
    cutoffTotientSelbergProfileTensorSum P edges companion F L =
      cutoffTotientSelbergProfileTensorSum Q edges companion F L := by
  classical
  unfold cutoffTotientSelbergProfileTensorSum
  calc
    _ = ∑ d ∈ doubledCutoffDivisorTuples ι P,
        if DoubledDivisorPrimeCompatible Q edges companion d then
          doubledSelbergProfileTensor F L d /
            (Nat.totient ((Finset.univ : Finset ((ι ⊕ ι) × Bool)).lcm
              (fun ib ↦ d ib.1 ib.2)) : ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [doubledDivisorPrimeCompatible_cutoff_iff hP hQ hPQ edges companion d hd]
    _ = _ := by
      apply Finset.sum_subset (doubledCutoffDivisorTuples_mono hP hQ hPQ)
      intro d hd hdnot
      have hz : doubledSelbergProfileTensor F L d = 0 := by
        by_contra hn
        exact hdnot (hcapture d hd hn)
      simp [hz]

theorem exists_common_profileTensor_cutoff_stabilization
    {ι : Type*} [Fintype ι]
    (F : ((ι ⊕ ι) × Bool) → ℝ → ℂ) (hF : ∀ ib, HasCompactSupport (F ib))
    (L : (ι ⊕ ι) → Bool → ℝ) (hL : ∀ i b, 0 < L i b) :
    ∃ B : ℕ,
      (∀ d : (ι ⊕ ι) → Bool → ℕ,
        (∀ i b, 0 < d i b) → doubledSelbergProfileTensor F L d ≠ 0 → ∀ i b, d i b ≤ B) ∧
      ∀ (P : Finset ℕ), (∀ p ∈ P, p.Prime) →
        ∀ (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool),
          cutoffSelbergProfileTensorSum (P.filter (· ≤ B)) edges companion F L =
            cutoffSelbergProfileTensorSum P edges companion F L ∧
          cutoffTotientSelbergProfileTensorSum (P.filter (· ≤ B)) edges companion F L =
            cutoffTotientSelbergProfileTensorSum P edges companion F L := by
  obtain ⟨B, hB⟩ := exists_doubledSelbergProfileTensor_bound F hF L hL
  refine ⟨B, hB, ?_⟩
  intro P hP edges companion
  have hsmall : ∀ p ∈ P.filter (· ≤ B), p.Prime :=
    fun p hp ↦ hP p (Finset.mem_filter.mp hp).1
  have hcapture : ∀ d ∈ doubledCutoffDivisorTuples ι P,
      doubledSelbergProfileTensor F L d ≠ 0 →
        d ∈ doubledCutoffDivisorTuples ι (P.filter (· ≤ B)) := by
    intro d hd hne
    obtain ⟨hdiv, hcop⟩ := (mem_doubledCutoffDivisorTuples P hP d).mp hd
    have hsq (i) (b) := (primeFinsetProduct_squarefree P hP).squarefree_of_dvd (hdiv i b)
    have hdB := hB d (fun i b ↦ (hsq i b).ne_zero.bot_lt) hne
    exact (mem_doubledCutoffDivisorTuples _ hsmall d).mpr
      ⟨fun i b ↦ bounded_squarefree_dvd_filteredPrimeProduct P hP (hsq i b) (hdiv i b) (hdB i b),
        hcop⟩
  exact ⟨cutoffSelbergProfileTensorSum_eq_of_capture hsmall hP (Finset.filter_subset _ _)
    edges companion F L hcapture,
    cutoffTotientSelbergProfileTensorSum_eq_of_capture hsmall hP (Finset.filter_subset _ _)
      edges companion F L hcapture⟩

end

end Erdos4b
