/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTAssignmentCrtClass
import ErdosProblems.Erdos4b.FGKMTIntegerProgressionCount

/-!
# The actual doubled-divisor count in one presieve class

Incompatible assignments contribute exactly zero. Compatible assignments
give one integer residue class with period the presieve modulus times
the merged prime product. Its density is the literal quadratic kernel.
-/

namespace Erdos4b.FGKMT

noncomputable section

variable {α ι : Type*} [Fintype α] [DecidableEq ι]

open scoped Classical in
def assignmentPairIntervalCount (p : α → ℕ) (a : ι → ℤ) (d e : α → Option ι)
    (W : ℕ) (v A B : ℤ) : ℝ :=
  ((Finset.Ico A B).filter (fun n => n ≡ v [ZMOD W] ∧
    ((∀ i, (assignmentPrimeTuple p d i : ℤ) ∣ n + a i) ∧
      (∀ i, (assignmentPrimeTuple p e i : ℤ) ∣ n + a i)))).card

theorem assignmentPairIntervalCount_error {W : ℕ} (hW : 0 < W) {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p) (hcop : ∀ q, (p q).Coprime W)
    (a : ι → ℤ) (hroot : ∀ q i j, (p q : ℤ) ∣ a i - a j → i = j)
    (d e : α → Option ι) (v A B : ℤ) (hAB : A ≤ B) :
    |assignmentPairIntervalCount p a d e W v A B -
      ((B : ℝ) - A) / W * assignmentCrtKernel (fun q => (p q : ℝ)) d e| ≤ 1 := by
  classical
  by_cases hc : AssignmentCompatible d e
  · obtain ⟨c, hclass⟩ := exists_assignmentPreSieve_class hW hp hinj hcop v a
      (mergeAssignment d e)
    have hset :
        (Finset.Ico A B).filter (fun n => n ≡ v [ZMOD W] ∧
          ((∀ i, (assignmentPrimeTuple p d i : ℤ) ∣ n + a i) ∧
            (∀ i, (assignmentPrimeTuple p e i : ℤ) ∣ n + a i))) =
        (Finset.Ico A B).filter (fun n =>
          n ≡ c [ZMOD (W * assignmentPrimeProduct p (mergeAssignment d e) : ℕ)]) := by
      apply Finset.filter_congr
      intro n _hn
      rw [assignmentDivisorPair_iff_merged hp hinj a hroot d e n, and_iff_right hc]
      exact hclass n
    rw [assignmentPairIntervalCount, hset, assignmentCrtKernel_eq_merged, if_pos hc]
    have hperiod : (0 : ℤ) < W * assignmentPrimeProduct p (mergeAssignment d e) := by
      exact_mod_cast Nat.mul_pos hW
        (assignmentPrimeProduct_pos (fun q => (hp q).pos) (mergeAssignment d e))
    have hcount := integerProgressionCount_error A B
      (W * assignmentPrimeProduct p (mergeAssignment d e)) c hAB hperiod
    simpa only [Int.cast_mul, Int.cast_natCast, Nat.cast_mul, div_eq_mul_inv,
      mul_inv, one_mul, mul_assoc] using hcount
  · have hset :
        (Finset.Ico A B).filter (fun n => n ≡ v [ZMOD W] ∧
          ((∀ i, (assignmentPrimeTuple p d i : ℤ) ∣ n + a i) ∧
            (∀ i, (assignmentPrimeTuple p e i : ℤ) ∣ n + a i))) = ∅ := by
      apply Finset.filter_false_of_mem
      intro n _hn hh
      exact hc ((assignmentDivisorPair_iff_merged hp hinj a hroot d e n).mp hh.2).1
    rw [assignmentPairIntervalCount, hset, assignmentCrtKernel_eq_merged, if_neg hc]
    norm_num

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.assignmentPairIntervalCount_error
