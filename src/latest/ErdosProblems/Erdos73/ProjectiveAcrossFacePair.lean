import ErdosProblems.Erdos73.ProjectiveAcrossFace

/-! Verifying the oriented-edge identity for the explicit across-face map. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

theorem projectiveAcrossFace_pair_cell_zero {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0)
    (r : Fin n) (c : Fin (n - 1)) :
    orientedPortPair (projectivePortLabel hn) (projectivePortOpposite n * projectivePortPair n)
      (projectiveAcrossFace hn hnEven (Sum.inl (r, c), 0)) =
        orientedPortPair (projectivePortLabel hn) (projectivePortPair n) (Sum.inl (r, c), 0) := by
  have hr := r.isLt
  have hc := c.isLt
  dsimp only [orientedPortPair]
  rw [projectivePortOtherPair_apply, projectivePortPair_apply]
  simp only [projectiveAcrossFace, Fin.val_zero, show (0 : ℕ) < 2 by decide,
    if_true, eq_self_iff_true, true_or]
  split_ifs <;> try omega
  all_goals dsimp only [projectivePortLabel, projectiveFaceParity, projectiveFaceCorner]
  all_goals simp only [quadranglePair, Bool.not_eq_true_eq_eq_false, decide_eq_true_eq,
    decide_eq_false_iff_not, Bool.not_false, Bool.not_true]
  all_goals split_ifs <;> try omega
  all_goals simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_def, Fin.ext_iff,
    Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, if_true, if_false,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]
  all_goals try dsimp only [projectiveBoundary, projectiveRoot]
  all_goals try simp only [Prod.mk.injEq, Fin.ext_iff, Fin.val_mk,
    Bool.not_eq_true_eq_eq_false, decide_eq_true_eq, decide_eq_false_iff_not, not_not,
    true_and, and_true] at *
  all_goals repeat' first | rfl | omega |
    (split <;> try simp only [Prod.mk.injEq, Fin.ext_iff, Fin.val_mk, true_and, and_true,
      true_or, or_true, not_true_eq_false, Prod.fst, Prod.snd, ite_true, ite_false,
      Bool.not_false, Bool.not_true, Bool.true_eq_false, Bool.false_eq_true] at *)

theorem projectiveAcrossFace_pair_cell_one {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0)
    (r : Fin n) (c : Fin (n - 1)) :
    orientedPortPair (projectivePortLabel hn) (projectivePortOpposite n * projectivePortPair n)
      (projectiveAcrossFace hn hnEven (Sum.inl (r, c), 1)) =
        orientedPortPair (projectivePortLabel hn) (projectivePortPair n) (Sum.inl (r, c), 1) := by
  have hr := r.isLt
  have hc := c.isLt
  dsimp only [orientedPortPair]
  rw [projectivePortOtherPair_apply, projectivePortPair_apply]
  simp only [projectiveAcrossFace, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Nat.reduceMod,
    Nat.reduceEqDiff, show (0 : ℕ) < 2 by decide, show (1 : ℕ) < 2 by decide,
    show ¬(2 : ℕ) < 2 by decide, show ¬(3 : ℕ) < 2 by decide,
    if_true, if_false, eq_self_iff_true, true_or, false_or, or_false]
  split_ifs <;> try omega
  all_goals dsimp only [projectivePortLabel, projectiveFaceParity, projectiveFaceCorner]
  all_goals simp only [quadranglePair, Bool.not_eq_true_eq_eq_false, decide_eq_true_eq,
    decide_eq_false_iff_not, Bool.not_false, Bool.not_true]
  all_goals split_ifs <;> try omega
  all_goals simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_def, Fin.ext_iff,
    Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, if_true, if_false,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]
  all_goals try dsimp only [projectiveBoundary, projectiveRoot]
  all_goals try simp only [Prod.mk.injEq, Fin.ext_iff, Fin.val_mk,
    Bool.not_eq_true_eq_eq_false, decide_eq_true_eq, decide_eq_false_iff_not, not_not,
    true_and, and_true] at *
  all_goals repeat' first | rfl | omega |
    (split <;> try simp only [Prod.mk.injEq, Fin.ext_iff, Fin.val_mk, true_and, and_true,
      true_or, or_true, not_true_eq_false, Prod.fst, Prod.snd, ite_true, ite_false,
      Bool.not_false, Bool.not_true, Bool.true_eq_false, Bool.false_eq_true] at *)

theorem projectiveAcrossFace_pair_cell_two {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0)
    (r : Fin n) (c : Fin (n - 1)) :
    orientedPortPair (projectivePortLabel hn) (projectivePortOpposite n * projectivePortPair n)
      (projectiveAcrossFace hn hnEven (Sum.inl (r, c), 2)) =
        orientedPortPair (projectivePortLabel hn) (projectivePortPair n) (Sum.inl (r, c), 2) := by
  have hr := r.isLt
  have hc := c.isLt
  dsimp only [orientedPortPair]
  rw [projectivePortOtherPair_apply, projectivePortPair_apply]
  simp only [projectiveAcrossFace, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Nat.reduceMod,
    Nat.reduceEqDiff, show (0 : ℕ) < 2 by decide, show (1 : ℕ) < 2 by decide,
    show ¬(2 : ℕ) < 2 by decide, show ¬(3 : ℕ) < 2 by decide,
    if_true, if_false, eq_self_iff_true, true_or, false_or, or_false]
  split_ifs <;> try omega
  all_goals dsimp only [projectivePortLabel, projectiveFaceParity, projectiveFaceCorner]
  all_goals simp only [quadranglePair, Bool.not_eq_true_eq_eq_false, decide_eq_true_eq,
    decide_eq_false_iff_not, Bool.not_false, Bool.not_true]
  all_goals split_ifs <;> try omega
  all_goals simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_def, Fin.ext_iff,
    Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, if_true, if_false,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]
  all_goals try dsimp only [projectiveBoundary, projectiveRoot]
  all_goals try simp only [Prod.mk.injEq, Fin.ext_iff, Fin.val_mk,
    Bool.not_eq_true_eq_eq_false, decide_eq_true_eq, decide_eq_false_iff_not, not_not,
    true_and, and_true] at *
  all_goals repeat' first | rfl | omega |
    (split <;> try simp only [Prod.mk.injEq, Fin.ext_iff, Fin.val_mk, true_and, and_true,
      true_or, or_true, not_true_eq_false, Prod.fst, Prod.snd, ite_true, ite_false,
      Bool.not_false, Bool.not_true, Bool.true_eq_false, Bool.false_eq_true] at *)

theorem projectiveAcrossFace_pair_cell_three {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0)
    (r : Fin n) (c : Fin (n - 1)) :
    orientedPortPair (projectivePortLabel hn) (projectivePortOpposite n * projectivePortPair n)
      (projectiveAcrossFace hn hnEven (Sum.inl (r, c), 3)) =
        orientedPortPair (projectivePortLabel hn) (projectivePortPair n) (Sum.inl (r, c), 3) := by
  have hr := r.isLt
  have hc := c.isLt
  dsimp only [orientedPortPair]
  rw [projectivePortOtherPair_apply, projectivePortPair_apply]
  simp only [projectiveAcrossFace, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Nat.reduceMod,
    Nat.reduceEqDiff, show (0 : ℕ) < 2 by decide, show (1 : ℕ) < 2 by decide,
    show ¬(2 : ℕ) < 2 by decide, show ¬(3 : ℕ) < 2 by decide,
    if_true, if_false, eq_self_iff_true, true_or, false_or, or_false]
  split_ifs <;> try omega
  all_goals dsimp only [projectivePortLabel, projectiveFaceParity, projectiveFaceCorner]
  all_goals simp only [quadranglePair, Bool.not_eq_true_eq_eq_false, decide_eq_true_eq,
    decide_eq_false_iff_not, Bool.not_false, Bool.not_true]
  all_goals split_ifs <;> try omega
  all_goals simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_def, Fin.ext_iff,
    Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, if_true, if_false,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]
  all_goals try dsimp only [projectiveBoundary, projectiveRoot]
  all_goals try simp only [Prod.mk.injEq, Fin.ext_iff, Fin.val_mk,
    Bool.not_eq_true_eq_eq_false, decide_eq_true_eq, decide_eq_false_iff_not, not_not,
    true_and, and_true] at *
  all_goals repeat' first | rfl | omega |
    (split <;> try simp only [Prod.mk.injEq, Fin.ext_iff, Fin.val_mk, true_and, and_true,
      true_or, or_true, not_true_eq_false, Prod.fst, Prod.snd, ite_true, ite_false,
      Bool.not_false, Bool.not_true, Bool.true_eq_false, Bool.false_eq_true] at *)

theorem projectiveAcrossFace_pair_cap_zero {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0)
    (j : Fin (n - 1)) :
    orientedPortPair (projectivePortLabel hn) (projectivePortOpposite n * projectivePortPair n)
      (projectiveAcrossFace hn hnEven (Sum.inr j, 0)) =
        orientedPortPair (projectivePortLabel hn) (projectivePortPair n) (Sum.inr j, 0) := by
  have hj := j.isLt
  dsimp only [orientedPortPair]
  rw [projectivePortOtherPair_apply, projectivePortPair_apply]
  simp only [projectiveAcrossFace, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Nat.reduceMod,
    Nat.reduceEqDiff, show (0 : ℕ) < 2 by decide, show (1 : ℕ) < 2 by decide,
    show ¬(2 : ℕ) < 2 by decide, show ¬(3 : ℕ) < 2 by decide,
    if_true, if_false, eq_self_iff_true, true_or, false_or, or_false]
  split_ifs <;> try omega
  all_goals dsimp only [projectivePortLabel, projectiveFaceParity, projectiveFaceCorner]
  all_goals simp only [quadranglePair, Bool.not_eq_true_eq_eq_false, decide_eq_true_eq,
    decide_eq_false_iff_not, Bool.not_false, Bool.not_true]
  all_goals split_ifs <;> try omega
  all_goals simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_def, Fin.ext_iff,
    Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, if_true, if_false,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]
  all_goals try dsimp only [projectiveBoundary, projectiveRoot]
  all_goals try simp only [Prod.mk.injEq, Fin.ext_iff, Fin.val_mk,
    Bool.not_eq_true_eq_eq_false, decide_eq_true_eq, decide_eq_false_iff_not, not_not,
    true_and, and_true] at *
  all_goals repeat' first | rfl | omega |
    (split <;> try simp only [Prod.mk.injEq, Fin.ext_iff, Fin.val_mk, true_and, and_true,
      true_or, or_true, not_true_eq_false, Prod.fst, Prod.snd, ite_true, ite_false,
      Bool.not_false, Bool.not_true, Bool.true_eq_false, Bool.false_eq_true] at *)

theorem projectiveAcrossFace_pair_cap_one {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0)
    (j : Fin (n - 1)) :
    orientedPortPair (projectivePortLabel hn) (projectivePortOpposite n * projectivePortPair n)
      (projectiveAcrossFace hn hnEven (Sum.inr j, 1)) =
        orientedPortPair (projectivePortLabel hn) (projectivePortPair n) (Sum.inr j, 1) := by
  have hj := j.isLt
  dsimp only [orientedPortPair]
  rw [projectivePortOtherPair_apply, projectivePortPair_apply]
  simp only [projectiveAcrossFace, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Nat.reduceMod,
    Nat.reduceEqDiff, show (0 : ℕ) < 2 by decide, show (1 : ℕ) < 2 by decide,
    show ¬(2 : ℕ) < 2 by decide, show ¬(3 : ℕ) < 2 by decide,
    if_true, if_false, eq_self_iff_true, true_or, false_or, or_false]
  split_ifs <;> try omega
  all_goals dsimp only [projectivePortLabel, projectiveFaceParity, projectiveFaceCorner]
  all_goals simp only [quadranglePair, Bool.not_eq_true_eq_eq_false, decide_eq_true_eq,
    decide_eq_false_iff_not, Bool.not_false, Bool.not_true]
  all_goals split_ifs <;> try omega
  all_goals simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_def, Fin.ext_iff,
    Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, if_true, if_false,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]
  all_goals try dsimp only [projectiveBoundary, projectiveRoot]
  all_goals try simp only [Prod.mk.injEq, Fin.ext_iff, Fin.val_mk,
    Bool.not_eq_true_eq_eq_false, decide_eq_true_eq, decide_eq_false_iff_not, not_not,
    true_and, and_true] at *
  all_goals repeat' first | rfl | omega |
    (split <;> try simp only [Prod.mk.injEq, Fin.ext_iff, Fin.val_mk, true_and, and_true,
      true_or, or_true, not_true_eq_false, Prod.fst, Prod.snd, ite_true, ite_false,
      Bool.not_false, Bool.not_true, Bool.true_eq_false, Bool.false_eq_true] at *)

theorem projectiveAcrossFace_pair_cap_two {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0)
    (j : Fin (n - 1)) :
    orientedPortPair (projectivePortLabel hn) (projectivePortOpposite n * projectivePortPair n)
      (projectiveAcrossFace hn hnEven (Sum.inr j, 2)) =
        orientedPortPair (projectivePortLabel hn) (projectivePortPair n) (Sum.inr j, 2) := by
  have hj := j.isLt
  dsimp only [orientedPortPair]
  rw [projectivePortOtherPair_apply, projectivePortPair_apply]
  simp only [projectiveAcrossFace, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Nat.reduceMod,
    Nat.reduceEqDiff, show (0 : ℕ) < 2 by decide, show (1 : ℕ) < 2 by decide,
    show ¬(2 : ℕ) < 2 by decide, show ¬(3 : ℕ) < 2 by decide,
    if_true, if_false, eq_self_iff_true, true_or, false_or, or_false]
  split_ifs <;> try omega
  all_goals dsimp only [projectivePortLabel, projectiveFaceParity, projectiveFaceCorner]
  all_goals simp only [quadranglePair, Bool.not_eq_true_eq_eq_false, decide_eq_true_eq,
    decide_eq_false_iff_not, Bool.not_false, Bool.not_true]
  all_goals split_ifs <;> try omega
  all_goals simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_def, Fin.ext_iff,
    Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, if_true, if_false,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]
  all_goals try dsimp only [projectiveBoundary, projectiveRoot]
  all_goals try simp only [Prod.mk.injEq, Fin.ext_iff, Fin.val_mk,
    Bool.not_eq_true_eq_eq_false, decide_eq_true_eq, decide_eq_false_iff_not, not_not,
    true_and, and_true] at *
  all_goals repeat' first | rfl | omega |
    (split <;> try simp only [Prod.mk.injEq, Fin.ext_iff, Fin.val_mk, true_and, and_true,
      true_or, or_true, not_true_eq_false, Prod.fst, Prod.snd, ite_true, ite_false,
      Bool.not_false, Bool.not_true, Bool.true_eq_false, Bool.false_eq_true] at *)

theorem projectiveAcrossFace_pair_cap_three {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0)
    (j : Fin (n - 1)) :
    orientedPortPair (projectivePortLabel hn) (projectivePortOpposite n * projectivePortPair n)
      (projectiveAcrossFace hn hnEven (Sum.inr j, 3)) =
        orientedPortPair (projectivePortLabel hn) (projectivePortPair n) (Sum.inr j, 3) := by
  have hj := j.isLt
  dsimp only [orientedPortPair]
  rw [projectivePortOtherPair_apply, projectivePortPair_apply]
  simp only [projectiveAcrossFace, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Nat.reduceMod,
    Nat.reduceEqDiff, show (0 : ℕ) < 2 by decide, show (1 : ℕ) < 2 by decide,
    show ¬(2 : ℕ) < 2 by decide, show ¬(3 : ℕ) < 2 by decide,
    if_true, if_false, eq_self_iff_true, true_or, false_or, or_false]
  split_ifs <;> try omega
  all_goals dsimp only [projectivePortLabel, projectiveFaceParity, projectiveFaceCorner]
  all_goals simp only [quadranglePair, Bool.not_eq_true_eq_eq_false, decide_eq_true_eq,
    decide_eq_false_iff_not, Bool.not_false, Bool.not_true]
  all_goals split_ifs <;> try omega
  all_goals simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_def, Fin.ext_iff,
    Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, if_true, if_false,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]
  all_goals try dsimp only [projectiveBoundary, projectiveRoot]
  all_goals try simp only [Prod.mk.injEq, Fin.ext_iff, Fin.val_mk,
    Bool.not_eq_true_eq_eq_false, decide_eq_true_eq, decide_eq_false_iff_not, not_not,
    true_and, and_true] at *
  all_goals repeat' first | rfl | omega |
    (split <;> try simp only [Prod.mk.injEq, Fin.ext_iff, Fin.val_mk, true_and, and_true,
      true_or, or_true, not_true_eq_false, Prod.fst, Prod.snd, ite_true, ite_false,
      Bool.not_false, Bool.not_true, Bool.true_eq_false, Bool.false_eq_true] at *)

theorem projectiveAcrossFace_pair {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0)
    (d : ProjectivePort n) :
    orientedPortPair (projectivePortLabel hn) (projectivePortOpposite n * projectivePortPair n)
      (projectiveAcrossFace hn hnEven d) =
        orientedPortPair (projectivePortLabel hn) (projectivePortPair n) d := by
  rcases d with ⟨f, i⟩
  rcases f with ⟨r, c⟩ | j
  · fin_cases i
    · exact projectiveAcrossFace_pair_cell_zero hn hnEven r c
    · exact projectiveAcrossFace_pair_cell_one hn hnEven r c
    · exact projectiveAcrossFace_pair_cell_two hn hnEven r c
    · exact projectiveAcrossFace_pair_cell_three hn hnEven r c
  · fin_cases i
    · exact projectiveAcrossFace_pair_cap_zero hn hnEven j
    · exact projectiveAcrossFace_pair_cap_one hn hnEven j
    · exact projectiveAcrossFace_pair_cap_two hn hnEven j
    · exact projectiveAcrossFace_pair_cap_three hn hnEven j


end
end Erdos73
