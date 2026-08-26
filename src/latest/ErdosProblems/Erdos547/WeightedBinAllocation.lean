import ErdosProblems.Erdos547.FiniteBinAllocation

/-!
# Allocating small objects to allowed bins using common weights
-/

namespace Erdos547

open Finset
open scoped BigOperators

variable {F I J : Type*} [Fintype F] [Fintype I] [Nonempty I] [Fintype J] [DecidableEq I]

open scoped Classical in
theorem exists_weighted_bin_assignment (allowed : F → Finset I)
    (w : I → ℝ) (u : F → J → ℝ) (A L C : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hA : 0 < A) (hC : 0 ≤ C)
    (hallowed : ∀ x, A ≤ ∑ i ∈ allowed x, w i)
    (hu : ∀ x j, 0 ≤ u x j ∧ u x j ≤ L)
    (hsmall : L * (∑ x, ∑ j, u x j) < C ^ 2) :
    ∃ f : F → I, (∀ x, f x ∈ allowed x) ∧
      ∀ i j, (∑ x ∈ (Finset.univ : Finset F).filter (fun x ↦ f x = i), u x j) <
        w i / A * (∑ x, u x j) + C := by
  classical
  let p : F → I → ℝ := fun x i ↦ if i ∈ allowed x
    then w i / (∑ l ∈ allowed x, w l) else 0
  have hden (x : F) : 0 < ∑ i ∈ allowed x, w i := hA.trans_le (hallowed x)
  have hp (x : F) (i : I) : 0 ≤ p x i := by
    dsimp [p]
    split_ifs
    · exact div_nonneg (hw i) (hden x).le
    · exact le_rfl
  have hmass (x : F) : ∑ i, p x i = 1 := by
    simp only [p, ← Finset.sum_filter]
    have hfilter : (Finset.univ : Finset I).filter (fun i ↦ i ∈ allowed x) = allowed x := by
      ext i
      simp
    rw [hfilter, ← Finset.sum_div, div_self (ne_of_gt (hden x))]
  have hpbound (x : F) (i : I) : p x i ≤ w i / A := by
    dsimp [p]
    split_ifs
    · exact div_le_div_of_nonneg_left (hw i) hA (hallowed x)
    · exact div_nonneg (hw i) hA.le
  obtain ⟨f, hf, hloads⟩ := exists_bin_assignment Finset.univ p u hp hmass L C hC
    (fun x _ j ↦ hu x j) hsmall
  refine ⟨f, ?_, ?_⟩
  · intro x
    have hh := hf x (Finset.mem_univ x)
    by_contra hn
    simp only [p, if_neg hn, lt_self_iff_false] at hh
  · intro i j
    apply (hloads i j).trans_le
    apply add_le_add_left
    calc
      (∑ x, p x i * u x j) ≤ ∑ x, (w i / A) * u x j :=
        Finset.sum_le_sum fun x _ ↦ mul_le_mul_of_nonneg_right (hpbound x i) (hu x j).1
      _ = _ := (Finset.mul_sum _ _ _).symm

end Erdos547

#print axioms Erdos547.exists_weighted_bin_assignment
