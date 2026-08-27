/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTCompatiblePairFiber
import BoundedGaps.Maynard.ImprovedGPY.S2Multiplicity

/-!
# Grouping compatible-pair errors by their merged prime product

The exact finite modulus-fiber identity is reused. Zero coefficients
are removed before grouping, and every surviving fiber has the sharp
three-state coordinate bound rather than the full pair-space cardinality.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators ArithmeticFunction.omega
open BoundedGaps.Maynard

variable {α ι : Type*} [DecidableEq α] [Fintype α] [DecidableEq ι] [Fintype ι]

omit [DecidableEq α] [DecidableEq ι] in
theorem compatiblePair_modulusFiber_le {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p)
    (I : Finset ((α → Option ι) × (α → Option ι)))
    (hI : ∀ de ∈ I, AssignmentCompatible de.1 de.2) {D : ℕ} (hD : Squarefree D) :
    modulusFiberCard I (fun de => assignmentPrimeProduct p (mergeAssignment de.1 de.2)) D ≤
      (3 * Fintype.card ι) ^ ω D := by
  classical
  apply le_trans _ (card_compatiblePairProductFiber_le hp hinj hD)
  apply Finset.card_le_card
  intro de hde
  exact mem_compatiblePairProductFiber.mpr
    ⟨hI de (Finset.mem_filter.mp hde).1, (Finset.mem_filter.mp hde).2⟩

omit [DecidableEq α] [DecidableEq ι] in
theorem sum_compatiblePairs_by_product_le {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p)
    (I : Finset ((α → Option ι) × (α → Option ι)))
    (hI : ∀ de ∈ I, AssignmentCompatible de.1 de.2) (F : ℕ → ℝ) (hF : ∀ D, 0 ≤ F D) :
    (∑ de ∈ I, F (assignmentPrimeProduct p (mergeAssignment de.1 de.2))) ≤
      ∑ D ∈ I.image (fun de => assignmentPrimeProduct p (mergeAssignment de.1 de.2)),
        (((3 * Fintype.card ι) ^ ω D : ℕ) : ℝ) * F D := by
  classical
  rw [sum_comp_eq_sum_modulusFiberCard]
  apply Finset.sum_le_sum
  intro D hD
  obtain ⟨de, _hde, rfl⟩ := Finset.mem_image.mp hD
  apply mul_le_mul_of_nonneg_right _ (hF _)
  exact_mod_cast compatiblePair_modulusFiber_le hp hinj I hI
    (assignmentPrimeProduct_squarefree hp hinj (mergeAssignment de.1 de.2))

open scoped Classical in
def supportedCompatiblePairs (l : (α → Option ι) → ℝ) :
    Finset ((α → Option ι) × (α → Option ι)) :=
  Finset.univ.filter (fun de => AssignmentCompatible de.1 de.2 ∧ l de.1 ≠ 0 ∧ l de.2 ≠ 0)

omit [DecidableEq ι] in
theorem mem_supportedCompatiblePairs {l : (α → Option ι) → ℝ}
    {de : (α → Option ι) × (α → Option ι)} :
    de ∈ supportedCompatiblePairs l ↔ AssignmentCompatible de.1 de.2 ∧
      l de.1 ≠ 0 ∧ l de.2 ≠ 0 := by
  simp only [supportedCompatiblePairs, Finset.mem_filter, Finset.mem_univ, true_and]

open scoped Classical in
omit [DecidableEq ι] in
theorem weighted_compatiblePair_sum_le {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p)
    (l : (α → Option ι) → ℝ) (F : ℕ → ℝ) (hF : ∀ D, 0 ≤ F D)
    {H : ℝ} (hH : 0 ≤ H) (hbound : ∀ d e, |l d * l e| ≤ H) :
    (∑ d : α → Option ι, ∑ e : α → Option ι,
      |l d * l e| * (if AssignmentCompatible d e then
        F (assignmentPrimeProduct p (mergeAssignment d e)) else 0)) ≤
      H * ∑ D ∈ (supportedCompatiblePairs l).image
          (fun de => assignmentPrimeProduct p (mergeAssignment de.1 de.2)),
        (((3 * Fintype.card ι) ^ ω D : ℕ) : ℝ) * F D := by
  classical
  have hid :
      (∑ d : α → Option ι, ∑ e : α → Option ι,
        |l d * l e| * (if AssignmentCompatible d e then
          F (assignmentPrimeProduct p (mergeAssignment d e)) else 0)) =
      ∑ de ∈ supportedCompatiblePairs l,
        |l de.1 * l de.2| * F (assignmentPrimeProduct p (mergeAssignment de.1 de.2)) := by
    simp only [supportedCompatiblePairs, Finset.sum_filter, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro d _hd
    apply Finset.sum_congr rfl
    intro e _he
    by_cases hc : AssignmentCompatible d e <;> by_cases hd : l d = 0 <;>
      by_cases he : l e = 0 <;> simp [hc, hd, he]
  rw [hid]
  calc
    _ ≤ ∑ de ∈ supportedCompatiblePairs l,
        H * F (assignmentPrimeProduct p (mergeAssignment de.1 de.2)) :=
      Finset.sum_le_sum fun de _ => mul_le_mul_of_nonneg_right (hbound de.1 de.2) (hF _)
    _ = H * ∑ de ∈ supportedCompatiblePairs l,
        F (assignmentPrimeProduct p (mergeAssignment de.1 de.2)) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_compatiblePairs_by_product_le hp hinj (supportedCompatiblePairs l)
        (fun de hde => (mem_supportedCompatiblePairs.mp hde).1) F hF) hH

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.sum_compatiblePairs_by_product_le
#print axioms Erdos4b.FGKMT.weighted_compatiblePair_sum_le
