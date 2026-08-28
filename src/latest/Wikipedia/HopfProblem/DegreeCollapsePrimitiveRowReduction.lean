import Wikipedia.HopfProblem.DegreeCollapseMatrixColumnAlgebra
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Push

/-!
# A primitive integral row acquires a unit by finite column additions

Minimize the nonzero absolute value of any entry among the actual finite
transvection products. Euclidean division would produce a smaller nonzero
remainder unless that entry divides every coefficient. Surjectivity then
forces it to divide one. No row operations or matrix normal form are assumed.
-/

open Function
open scoped BigOperators

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

theorem mul_transvection_list_surjective {r n : ℕ} (A : Matrix (Fin r) (Fin n) ℤ)
    (hA : Surjective A.mulVec) (ops : List (Fin n × Fin n × ℤ))
    (hvalid : ∀ op ∈ ops, op.1 ≠ op.2.1) :
    Surjective (A * (ops.map (fun op => Matrix.transvection op.1 op.2.1 op.2.2)).prod).mulVec := by
  revert hvalid
  induction ops using List.reverseRecOn with
  | nil =>
    intro hvalid
    simpa only [List.map_nil, List.prod_nil, Matrix.mul_one] using hA
  | append_singleton ops op ih =>
    intro hvalid
    have hprev : ∀ e ∈ ops, e.1 ≠ e.2.1 :=
      fun e he => hvalid e (List.mem_append.mpr (Or.inl he))
    have hop := hvalid op (List.mem_append.mpr (Or.inr (List.mem_singleton_self op)))
    simpa only [List.map_append, List.map_singleton, List.prod_append, List.prod_singleton,
      ← Matrix.mul_assoc] using mul_transvection_surjective _ op.1 op.2.1 hop op.2.2 (ih hprev)

theorem primitive_row_has_unit_after_column_additions {n : ℕ}
    (A : Matrix (Fin 1) (Fin n) ℤ) (hA : Surjective A.mulVec) :
    ∃ ops : List (Fin n × Fin n × ℤ), (∀ op ∈ ops, op.1 ≠ op.2.1) ∧
      ∃ i : Fin n,
        (A * (ops.map (fun op => Matrix.transvection op.1 op.2.1 op.2.2)).prod) 0 i = 1 ∨
        (A * (ops.map (fun op => Matrix.transvection op.1 op.2.1 op.2.2)).prod) 0 i = -1 := by
  classical
  have hnonzero : ∃ j, A 0 j ≠ 0 := by
    by_contra hnot
    push Not at hnot
    obtain ⟨x, hx⟩ := hA 1
    have hh := congrFun hx 0
    change ∑ j, A 0 j * x j = 1 at hh
    simp only [hnot, zero_mul, Finset.sum_const_zero] at hh
    exact zero_ne_one hh
  let P : ℕ → Prop := fun m => ∃ ops : List (Fin n × Fin n × ℤ),
    (∀ op ∈ ops, op.1 ≠ op.2.1) ∧ ∃ i : Fin n,
      (A * (ops.map (fun op => Matrix.transvection op.1 op.2.1 op.2.2)).prod) 0 i ≠ 0 ∧
      ((A * (ops.map (fun op => Matrix.transvection op.1 op.2.1 op.2.2)).prod) 0 i).natAbs = m
  obtain ⟨j₀, hj₀⟩ := hnonzero
  have hex : ∃ m, P m := by
    refine ⟨(A 0 j₀).natAbs, [], ?_, j₀, ?_, ?_⟩
    · intro op hop
      simp only [List.not_mem_nil] at hop
    · simpa only [List.map_nil, List.prod_nil, Matrix.mul_one] using hj₀
    · simp only [List.map_nil, List.prod_nil, Matrix.mul_one]
  obtain ⟨ops, hvalid, i, hi, hrank⟩ := Nat.find_spec hex
  let C := A * (ops.map (fun op => Matrix.transvection op.1 op.2.1 op.2.2)).prod
  have hC : Surjective C.mulVec := mul_transvection_list_surjective A hA ops hvalid
  have hdiv (j : Fin n) : C 0 i ∣ C 0 j := by
    by_cases hij : i = j
    · subst j
      exact dvd_refl _
    apply Int.dvd_of_emod_eq_zero
    by_contra hrem
    let op : Fin n × Fin n × ℤ := (i, j, -(C 0 j / C 0 i))
    let ops' := ops ++ [op]
    have hvalid' : ∀ e ∈ ops', e.1 ≠ e.2.1 := by
      intro e he
      rcases List.mem_append.mp he with he | he
      · exact hvalid e he
      · have heq : e = op := List.mem_singleton.mp he
        subst e
        exact hij
    have hnew : A * (ops'.map (fun e => Matrix.transvection e.1 e.2.1 e.2.2)).prod =
        C * Matrix.transvection i j (-(C 0 j / C 0 i)) := by
      simp only [ops', List.map_append, List.map_singleton, List.prod_append,
        List.prod_singleton, ← Matrix.mul_assoc]
      rfl
    have hentry : (A * (ops'.map (fun e => Matrix.transvection e.1 e.2.1 e.2.2)).prod) 0 j =
        C 0 j % C 0 i := by
      rw [hnew, Matrix.mul_transvection_apply_same, Int.emod_def]
      ring
    have hsmall : (C 0 j % C 0 i).natAbs < (C 0 i).natAbs := by
      have hh := Int.natAbs_lt_natAbs_of_nonneg_of_lt (Int.emod_nonneg (C 0 j) hi)
        (Int.emod_lt_abs (C 0 j) hi)
      simpa only [Int.natAbs_abs] using hh
    have hminimal := Nat.find_min' hex (show P (C 0 j % C 0 i).natAbs from
      ⟨ops', hvalid', j, (by rw [hentry]; exact hrem), congrArg Int.natAbs hentry⟩)
    rw [← hrank] at hminimal
    exact (not_le_of_gt hsmall) hminimal
  obtain ⟨x, hx⟩ := hC 1
  have hsum := congrFun hx 0
  change ∑ j, C 0 j * x j = 1 at hsum
  have hdvd : C 0 i ∣ 1 := by
    rw [← hsum]
    exact Finset.dvd_sum (fun j _ => dvd_mul_of_dvd_left (hdiv j) (x j))
  obtain ⟨v, hv⟩ := hdvd
  exact ⟨ops, hvalid, i, Int.eq_one_or_neg_one_of_mul_eq_one hv.symm⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
