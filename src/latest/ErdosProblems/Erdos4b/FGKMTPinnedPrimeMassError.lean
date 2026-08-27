/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPinnedPairPrimeCount
import ErdosProblems.Erdos4b.FGKMTPinnedMainTerm

/-!
# The pinned prime mass with its exact modulus-dependent error

The signed coefficient quadratic is compared with the already proved
pinned quadratic. Every pair keeps its own progression discrepancy,
so subsequent modulus grouping can use the average distribution bound.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators
open BoundedGaps.Maynard

theorem quadratic_weighted_count_error {β : Type*} [Fintype β]
    (l : β → ℝ) (N K E : β → β → ℝ) (L : ℝ)
    (herror : ∀ d e, |N d e - L * K d e| ≤ E d e) :
    |(∑ d, ∑ e, l d * l e * N d e) - L * (∑ d, ∑ e, l d * l e * K d e)| ≤
      ∑ d, ∑ e, |l d * l e| * E d e := by
  have hid :
      (∑ d, ∑ e, l d * l e * N d e) - L * (∑ d, ∑ e, l d * l e * K d e) =
        ∑ d, ∑ e, l d * l e * (N d e - L * K d e) := by
    simp only [Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d _hd
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e _he
    ring
  rw [hid]
  calc
    _ ≤ ∑ d, |∑ e, l d * l e * (N d e - L * K d e)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d, ∑ e, |l d * l e * (N d e - L * K d e)| :=
      Finset.sum_le_sum fun d _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro d _hd
      apply Finset.sum_le_sum
      intro e _he
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (herror d e) (abs_nonneg _)

open scoped Classical in
def commonPinnedProgressionError (m W M R A B : ℕ) (j : Fin (m + 1)) : ℝ :=
  ∑ d : commonPrimeUniverse M R → Option (Fin m),
    ∑ e : commonPrimeUniverse M R → Option (Fin m),
      |commonPinnedCoefficient m R (fun q => q.val) j d *
          commonPinnedCoefficient m R (fun q => q.val) j e| *
        (if AssignmentCompatible d e then maxProgressionDiscrepancy B
            (W * assignmentPrimeProduct (fun q => q.val) (mergeAssignment d e)) +
          maxProgressionDiscrepancy A
            (W * assignmentPrimeProduct (fun q => q.val) (mergeAssignment d e)) else 0)

theorem commonPinnedProgressionError_nonneg (m W M R A B : ℕ) (j : Fin (m + 1)) :
    0 ≤ commonPinnedProgressionError m W M R A B j := by
  apply Finset.sum_nonneg
  intro d _hd
  apply Finset.sum_nonneg
  intro e _he
  apply mul_nonneg (abs_nonneg _)
  split_ifs
  · exact add_nonneg (maxProgressionDiscrepancy_nonneg _ _) (maxProgressionDiscrepancy_nonneg _ _)
  · exact le_rfl

theorem commonPinnedPrimeMass_quadratic_error {m W M R Q A B : ℕ} {y : ℝ}
    (hW : 0 < W) (hWM : W ∣ M) (hAB : A ≤ B) (hQ : Q.Prime) (hRQ : R < Q)
    (hWsmall : ∀ q : ℕ, q.Prime → q ∣ W → q ≤ A)
    (hsmall : ∀ p : ℕ, p.Prime → p ≤ 2 * (m + 1) ^ 2 → p ∣ M)
    (h : Fin (m + 1) → ℕ) (hinj : Function.Injective h)
    (hshift : ∀ i, h i < 2 * (m + 1) ^ 2) (j : Fin (m + 1))
    (hQy : (Q : ℝ) ≤ y) (hBy : (h j : ℝ) * B ≤ y) :
    |commonPinnedPrimeMass m W M R Q A B y h j -
        primePreSieveDensity W Q (fun i => (h i : ℤ)) j *
          (commonPinnedPrimeSet A B).card * commonPinnedQuadratic m M R j| ≤
      ((primePreSieveResidues W Q (fun i => (h i : ℤ)) j).card : ℝ) *
        commonPinnedProgressionError m W M R A B j := by
  classical
  let l := commonPinnedCoefficient m R (fun q : commonPrimeUniverse M R => q.val) j
  let N := fun v d e => (commonPinnedPairPrimeCount m W Q A B v
    (fun q : commonPrimeUniverse M R => q.val) h j d e : ℝ)
  let L : ℝ := ((commonPinnedPrimeSet A B).card : ℝ) / W.totient
  let S := primePreSieveResidues W Q (fun i => (h i : ℤ)) j
  have hres (v : ℕ) (hv : v ∈ S) :
      |(∑ d, ∑ e, l d * l e * N v d e) - L * commonPinnedQuadratic m M R j| ≤
        commonPinnedProgressionError m W M R A B j := by
    exact quadratic_weighted_count_error l (N v)
      (assignmentCrtKernel (fun q : commonPrimeUniverse M R => (q.val : ℝ) - 1))
      (fun d e => if AssignmentCompatible d e then maxProgressionDiscrepancy B
          (W * assignmentPrimeProduct (fun q => q.val) (mergeAssignment d e)) +
        maxProgressionDiscrepancy A
          (W * assignmentPrimeProduct (fun q => q.val) (mergeAssignment d e)) else 0) L
      (fun d e => commonPinnedPairPrimeCount_compatible_error hW
        (mem_primePreSieveResidues_iff.mp hv).2.1 hWM hAB hsmall hQ hRQ h hinj hshift j d e)
  have hid : commonPinnedPrimeMass m W M R Q A B y h j -
      primePreSieveDensity W Q (fun i => (h i : ℤ)) j *
        (commonPinnedPrimeSet A B).card * commonPinnedQuadratic m M R j =
      ∑ v ∈ S, ((∑ d, ∑ e, l d * l e * N v d e) - L * commonPinnedQuadratic m M R j) := by
    rw [commonPinnedPrimeMass_eq_pair_counts hW hQ hRQ hWsmall h j hQy hBy,
      Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    dsimp only [primePreSieveDensity, S, L, l, N]
    ring
  rw [hid]
  calc
    _ ≤ ∑ v ∈ S, |(∑ d, ∑ e, l d * l e * N v d e) -
        L * commonPinnedQuadratic m M R j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _v ∈ S, commonPinnedProgressionError m W M R A B j :=
      Finset.sum_le_sum fun v hv => hres v hv
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.quadratic_weighted_count_error
#print axioms Erdos4b.FGKMT.commonPinnedPrimeMass_quadratic_error
