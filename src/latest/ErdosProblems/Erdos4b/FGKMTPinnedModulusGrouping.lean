/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTCompatiblePairGrouping
import ErdosProblems.Erdos4b.FGKMTIndividualCoefficientBound
import ErdosProblems.Erdos4b.FGKMTPinnedPrimeMassError

/-!
# The actual pinned progression error grouped by squarefree moduli

Both nonzero coefficients retain the original radius support. Their
compatible merged products lie in the explicit squarefree coprime
range up to `R^2`. The uniform individual pair bound is applied before
enlarging the nonnegative grouped sum to that range.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators ArithmeticFunction.omega
open BoundedGaps.Maynard

def commonPinnedPairModuli (m M R : ℕ) (j : Fin (m + 1)) : Finset ℕ :=
  (supportedCompatiblePairs
    (commonPinnedCoefficient m R (fun q : commonPrimeUniverse M R => q.val) j)).image
      (fun de => assignmentPrimeProduct (fun q => q.val) (mergeAssignment de.1 de.2))

open scoped Classical in
def commonPinnedModulusRange (M R : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (R ^ 2)).filter (fun D => Squarefree D ∧ D.Coprime M)

theorem mem_commonPinnedModulusRange {M R D : ℕ} :
    D ∈ commonPinnedModulusRange M R ↔ 1 ≤ D ∧ D ≤ R ^ 2 ∧ Squarefree D ∧ D.Coprime M := by
  simp only [commonPinnedModulusRange, Finset.mem_filter, Finset.mem_Icc]
  tauto

theorem commonPinnedPairModuli_subset {m M R : ℕ} (hR : 1 < R) (j : Fin (m + 1)) :
    commonPinnedPairModuli m M R j ⊆ commonPinnedModulusRange M R := by
  intro D hD
  obtain ⟨de, hde, rfl⟩ := Finset.mem_image.mp hD
  have hpair := mem_supportedCompatiblePairs.mp hde
  have hpos := assignmentPrimeProduct_pos (fun q => (commonPrimeUniverse_prime q).pos)
    (mergeAssignment de.1 de.2)
  have hbound := commonPinnedPair_period_le (W := 1) commonPrimeUniverse_prime
    Subtype.val_injective hR j de.1 de.2 hpair.2.1 hpair.2.2
  simp only [one_mul] at hbound
  exact mem_commonPinnedModulusRange.mpr ⟨hpos, hbound,
    assignmentPrimeProduct_squarefree commonPrimeUniverse_prime Subtype.val_injective _,
    assignmentPrimeProduct_coprime commonPrimeUniverse_prime commonPrimeUniverse_not_dvd _⟩

def commonPinnedWeightedDiscrepancy (m W M R A B : ℕ) : ℝ :=
  ∑ D ∈ commonPinnedModulusRange M R, (((3 * m) ^ ω D : ℕ) : ℝ) *
    (maxProgressionDiscrepancy B (W * D) + maxProgressionDiscrepancy A (W * D))

theorem commonPinnedWeightedDiscrepancy_nonneg (m W M R A B : ℕ) :
    0 ≤ commonPinnedWeightedDiscrepancy m W M R A B := by
  exact Finset.sum_nonneg fun D _ => mul_nonneg (Nat.cast_nonneg _)
    (add_nonneg (maxProgressionDiscrepancy_nonneg _ _) (maxProgressionDiscrepancy_nonneg _ _))

theorem commonPinnedProgressionError_grouped {m W M R A B : ℕ} (hR : 1 < R)
    (j : Fin (m + 1)) {H : ℝ} (hH : 0 ≤ H)
    (hbound : ∀ d e : commonPrimeUniverse M R → Option (Fin m),
      |commonPinnedCoefficient m R (fun q => q.val) j d *
          commonPinnedCoefficient m R (fun q => q.val) j e| ≤ H) :
    commonPinnedProgressionError m W M R A B j ≤
      H * commonPinnedWeightedDiscrepancy m W M R A B := by
  let F := fun D => maxProgressionDiscrepancy B (W * D) + maxProgressionDiscrepancy A (W * D)
  have hF (D : ℕ) : 0 ≤ F D :=
    add_nonneg (maxProgressionDiscrepancy_nonneg _ _) (maxProgressionDiscrepancy_nonneg _ _)
  have hgroup := weighted_compatiblePair_sum_le commonPrimeUniverse_prime Subtype.val_injective
    (commonPinnedCoefficient m R (fun q : commonPrimeUniverse M R => q.val) j) F hF hH hbound
  simp only [Fintype.card_fin] at hgroup
  change commonPinnedProgressionError m W M R A B j ≤
    H * ∑ D ∈ commonPinnedPairModuli m M R j, (((3 * m) ^ ω D : ℕ) : ℝ) * F D at hgroup
  apply hgroup.trans
  apply mul_le_mul_of_nonneg_left _ hH
  exact Finset.sum_le_sum_of_subset_of_nonneg (commonPinnedPairModuli_subset hR j)
    (fun D _hD _hnot => mul_nonneg (Nat.cast_nonneg _) (hF D))

theorem exists_commonPinnedProgressionError_grouped_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ m W M R A B : ℕ, 1 ≤ m → 1 < R →
      (∀ p : ℕ, p.Prime → p ≤ 2 * (m + 1) ^ 2 → p ∣ M) → ∀ j : Fin (m + 1),
      commonPinnedProgressionError m W M R A B j ≤
        Real.exp (C * (m + 1) * (1 + Real.log (Nat.log 2 R : ℕ))) *
          commonPinnedWeightedDiscrepancy m W M R A B := by
  obtain ⟨C, hC, hbound⟩ := exists_commonPinnedCoefficient_pair_bound
  refine ⟨C, hC, ?_⟩
  intro m W M R A B hm hR hsmall j
  exact commonPinnedProgressionError_grouped hR j (Real.exp_pos _).le
    (hbound m M R hm hsmall j)

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.commonPinnedPairModuli_subset
#print axioms Erdos4b.FGKMT.exists_commonPinnedProgressionError_grouped_bound
