/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierForcedFiniteIntegral
import ErdosProblems.Erdos4b.GeneralFourierCommonCutoff

/-!
# Stabilization of the forced profile sum at the common coordinate cutoff

The profile bound is unchanged by the extra prime or its local condition.
The arithmetic denominator remains the enlarged lcm in both finite sums.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

theorem cutoffForcedSelbergProfileTensorSum_eq_of_capture
    {ι : Type*} [Fintype ι] {P Q : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ p ∈ Q, p.Prime) (hPQ : P ⊆ Q)
    (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (p : ℕ) (R : ((ι ⊕ ι) → Bool → ℕ) → Prop)
    (F : ((ι ⊕ ι) × Bool) → ℝ → ℂ) (L : (ι ⊕ ι) → Bool → ℝ)
    (hcapture : ∀ d ∈ doubledCutoffDivisorTuples ι Q,
      doubledSelbergProfileTensor F L d ≠ 0 → d ∈ doubledCutoffDivisorTuples ι P) :
    cutoffForcedSelbergProfileTensorSum P edges companion p R F L =
      cutoffForcedSelbergProfileTensorSum Q edges companion p R F L := by
  classical
  unfold cutoffForcedSelbergProfileTensorSum
  calc
    _ = ∑ d ∈ doubledCutoffDivisorTuples ι P,
        if DoubledDivisorPrimeCompatible Q edges companion d ∧ R d then
          doubledSelbergProfileTensor F L d /
            (Nat.totient (Nat.lcm
              ((Finset.univ : Finset ((ι ⊕ ι) × Bool)).lcm (fun ib ↦ d ib.1 ib.2)) p) : ℂ)
        else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      simp only [doubledDivisorPrimeCompatible_cutoff_iff hP hQ hPQ edges companion d hd]
    _ = _ := by
      apply Finset.sum_subset (doubledCutoffDivisorTuples_mono hP hQ hPQ)
      intro d hd hn
      have hz : doubledSelbergProfileTensor F L d = 0 := by
        by_contra hne
        exact hn (hcapture d hd hne)
      simp [hz]

theorem cutoffForcedSelbergProfileTensorSum_filtered_eq
    {ι : Type*} [Fintype ι] (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (p : ℕ) (R : ((ι ⊕ ι) → Bool → ℕ) → Prop)
    (F : ((ι ⊕ ι) × Bool) → ℝ → ℂ) (hF : ∀ ib, HasCompactSupport (F ib))
    (L : (ι ⊕ ι) → Bool → ℝ) (hL : ∀ i b, 0 < L i b)
    {B : ℕ} (hB : compactProfileTensorCommonBound F L ≤ B) :
    cutoffForcedSelbergProfileTensorSum (P.filter (· ≤ B)) edges companion p R F L =
      cutoffForcedSelbergProfileTensorSum P edges companion p R F L := by
  have hsmall : ∀ r ∈ P.filter (· ≤ B), r.Prime :=
    fun r hr ↦ hP r (Finset.mem_filter.mp hr).1
  apply cutoffForcedSelbergProfileTensorSum_eq_of_capture hsmall hP (Finset.filter_subset _ _)
    edges companion p R F L
  intro d hd hne
  obtain ⟨hdiv, hcop⟩ := (mem_doubledCutoffDivisorTuples P hP d).mp hd
  have hsq i b := (primeFinsetProduct_squarefree P hP).squarefree_of_dvd (hdiv i b)
  have hcap := compactProfileTensorCommonBound_capture F hF L hL d
    (fun i b ↦ (hsq i b).ne_zero.bot_lt) hne
  exact (mem_doubledCutoffDivisorTuples _ hsmall d).mpr
    ⟨fun i b ↦ bounded_squarefree_dvd_filteredPrimeProduct P hP (hsq i b) (hdiv i b)
      ((hcap i b).trans hB), hcop⟩

end

end Erdos4b
