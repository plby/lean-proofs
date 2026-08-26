import ErdosProblems.Erdos394.GlobalDenominatorFinite
import ErdosProblems.Erdos394.LargePrimeProductEmbedding

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Summing the canonical denominator contributions injectively
-/

open Nat Finset

namespace Erdos394

/-- Nonempty selected subsets of cardinality at most `S`. -/
def denominatorSelectedSubsets (P : Finset ℕ) (S : ℕ) :
    Finset (Finset ℕ) :=
  (boundedCardSubsets P S).erase ∅

lemma mem_denominatorSelectedSubsets_iff {P T : Finset ℕ} {S : ℕ} :
    T ∈ denominatorSelectedSubsets P S ↔
      T ⊆ P ∧ T.card ≤ S ∧ T ≠ ∅ := by
  simp only [denominatorSelectedSubsets, Finset.mem_erase,
    boundedCardSubsets, Finset.mem_filter, Finset.mem_powerset]
  aesop

/-- The canonical fixed-modulus lower bounds can be summed over all nonempty
bounded-cardinality selected subsets: the associated large-prime products are
pairwise distinct and lie in the full summatory range. -/
theorem sum_canonical_selected_main_le_full_tSum
    (P : Finset ℕ) (K C0 X R y S : ℕ)
    (hK : 0 < K) (hC0 : 0 < C0)
    (hprime : ∀ p ∈ P, p.Prime)
    (hKlarge : ∀ p ∈ P, K < p)
    (hPupper : ∀ p ∈ P, p ≤ y)
    (hR : Even R)
    (htail :
      (∑ p ∈ P, (1 / (p : ℝ))) ^ (R + 1) /
          ((R + 1).factorial : ℝ) ≤
        localEulerProduct P (fun p ↦ 1 / (p : ℝ)))
    (hbaseAbove : ∀ T ∈ denominatorSelectedSubsets P S,
      y < selectedPrimeBase X T)
    (hheight : ∀ T ∈ denominatorSelectedSubsets P S,
      2 * K ≤ selectedHorizon K C0 T * selectedPrimeBase X T)
    (hrecip : ∀ T ∈ denominatorSelectedSubsets P S,
      Real.log 2 / (16 * Real.log (selectedPrimeBase X T)) ≤
        primeReciprocalSum (16 * selectedPrimeBase X T) -
          primeReciprocalSum (selectedPrimeBase X T))
    (hbad : ∀ T ∈ denominatorSelectedSubsets P S, 2 *
      ((((16 * selectedPrimeBase X T : ℕ) : ℝ) ^ 2 /
          (C0 : ℝ)) * localEulerProduct P (fun p ↦ 1 / (p : ℝ)) +
        ((primeProduct T : ℝ) / (C0 : ℝ)) *
          ((truncatedSubsets (P \ T) R).card : ℝ) *
            (2 * ((16 * selectedPrimeBase X T : ℕ) : ℝ))) ≤
      Real.log 2 * (selectedPrimeBase X T : ℝ) ^ 2 /
        (16 * Real.log (selectedPrimeBase X T))) :
    (∑ T ∈ denominatorSelectedSubsets P S,
      ((selectedHorizon K C0 T : ℕ) : ℝ) / 4 *
        (Real.log 2 * (selectedPrimeBase X T : ℝ) ^ 2 /
          (16 * Real.log (selectedPrimeBase X T)))) ≤
      ∑ n ∈ Finset.Icc 1 X, (t K n : ℝ) := by
  classical
  let outer := denominatorSelectedSubsets P S
  let L : Finset ℕ → Finset ℕ := fun T ↦
    if hTP : T ⊆ P then
      shiftedGoodPrimeSet T K (selectedHorizon K C0 T)
        (selectedPrimeBase X T) (16 * selectedPrimeBase X T)
        (fun p hp ↦ hprime p (hTP hp))
    else ∅
  have houter : ∀ T ∈ outer, T ⊆ P := by
    intro T hT
    exact (mem_denominatorSelectedSubsets_iff.mp hT).1
  have hfixed : ∀ T ∈ outer,
      ((selectedHorizon K C0 T : ℕ) : ℝ) / 4 *
          (Real.log 2 * (selectedPrimeBase X T : ℝ) ^ 2 /
            (16 * Real.log (selectedPrimeBase X T))) ≤
        ∑ ell ∈ L T, (t K (ell * primeProduct T) : ℝ) := by
    intro T hT
    have hTP := houter T hT
    have hquarter := quarter_horizon_primeMain_le_canonical_mass
      P T K C0 X R hK hC0 hTP hprime
      (fun p hp ↦ hKlarge p (hTP hp))
      (fun p hp ↦ (hPupper p hp).trans (hbaseAbove T hT).le)
      (hheight T hT) hR htail
      (Nat.zero_lt_of_lt (hbaseAbove T hT))
      (hrecip T hT) (hbad T hT)
    have hLeq : L T =
        shiftedGoodPrimeSet T K (selectedHorizon K C0 T)
          (selectedPrimeBase X T) (16 * selectedPrimeBase X T)
          (fun p hp ↦ hprime p (hTP hp)) := by
      simp [L, hTP]
    rw [hLeq]
    exact hquarter.trans_eq (shiftedGoodPrimeTMass_eq_sum_set T K
      (selectedHorizon K C0 T) (selectedPrimeBase X T)
      (16 * selectedPrimeBase X T) (fun p hp ↦ hprime p (hTP hp)))
  have hLsubset : ∀ T ∈ outer,
      L T ⊆ largePrimeInterval (selectedPrimeBase X T)
        (16 * selectedPrimeBase X T) := by
    intro T hT
    have hTP := houter T hT
    have hLeq : L T =
        shiftedGoodPrimeSet T K (selectedHorizon K C0 T)
          (selectedPrimeBase X T) (16 * selectedPrimeBase X T)
          (fun p hp ↦ hprime p (hTP hp)) := by
      simp [L, hTP]
    rw [hLeq]
    unfold shiftedGoodPrimeSet
    exact Finset.filter_subset _ _
  have hLprime : ∀ T ∈ outer, ∀ ell ∈ L T, ell.Prime := by
    intro T hT ell hell
    exact (mem_largePrimeInterval_iff.mp (hLsubset T hT hell)).2.2
  have hLlarge : ∀ T ∈ outer, ∀ ell ∈ L T, y < ell := by
    intro T hT ell hell
    exact (hbaseAbove T hT).trans
      (mem_largePrimeInterval_iff.mp (hLsubset T hT hell)).1
  have hLX : ∀ T ∈ outer, ∀ ell ∈ L T,
      0 < ell * primeProduct T ∧ ell * primeProduct T ≤ X := by
    intro T hT ell hell
    have hTP := houter T hT
    have hellInterval := hLsubset T hT hell
    have hellPrime := (mem_largePrimeInterval_iff.mp hellInterval).2.2
    constructor
    · exact mul_pos hellPrime.pos (by
        unfold primeProduct
        exact Finset.prod_pos fun p hp ↦ (hprime p (hTP hp)).pos)
    · apply primeBlock_mul_modulus_le
      exact (mem_largePrimeInterval_iff.mp hellInterval).2.1
  calc
    (∑ T ∈ denominatorSelectedSubsets P S,
      ((selectedHorizon K C0 T : ℕ) : ℝ) / 4 *
        (Real.log 2 * (selectedPrimeBase X T : ℝ) ^ 2 /
          (16 * Real.log (selectedPrimeBase X T)))) ≤
        ∑ T ∈ outer, ∑ ell ∈ L T,
          (t K (ell * primeProduct T) : ℝ) := by
      dsimp [outer]
      exact Finset.sum_le_sum hfixed
    _ ≤ ∑ n ∈ Finset.Icc 1 X, (t K n : ℝ) := by
      exact sum_selected_largePrime_t_le_full_sum K X y P hprime hPupper
        outer L houter hLprime hLlarge hLX

end Erdos394
