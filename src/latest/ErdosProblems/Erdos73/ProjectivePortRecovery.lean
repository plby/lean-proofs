import ErdosProblems.Erdos73.ProjectiveSelectedPorts
import ErdosProblems.Erdos73.EdgePairRotation

/-! Recovering the unique alpha-side corner from its oriented grid or fan edge. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

abbrev ProjectivePortCode := Bool × ℕ × ℕ × ℕ

def projectivePortCode {n : ℕ} (d : ProjectivePort n) : ProjectivePortCode :=
  match d.1 with
  | Sum.inl (r, c) => (false, r.val, c.val, d.2.val)
  | Sum.inr j => (true, 0, j.val, d.2.val)

theorem projectivePortCode_injective {n : ℕ} : Function.Injective (@projectivePortCode n) := by
  rintro ⟨f, i⟩ ⟨g, j⟩ he
  rcases f with ⟨r, c⟩ | k <;> rcases g with ⟨s, d⟩ | l
  all_goals simp only [projectivePortCode, Prod.mk.injEq, Bool.false_eq_true,
    Bool.true_eq_false, false_and, true_and] at he
  · exact Prod.ext (congrArg Sum.inl (Prod.ext (Fin.ext he.1) (Fin.ext he.2.1))) (Fin.ext he.2.2)
  · exact Prod.ext (congrArg Sum.inr (Fin.ext he.1)) (Fin.ext he.2)

def projectiveRecoveredPort (n : ℕ) (u v : ℕ × ℕ) : ProjectivePortCode :=
  if u.1 = v.1 then
    let r := u.1
    let c := min u.2 v.2
    let forward := u.2 < v.2
    if (r + c) % 2 = 0 then (false, r, c, if forward then 0 else 1)
    else if 0 < r then (false, r - 1, c, if forward then 3 else 2)
    else (false, n - 1, n - 2 - c, if forward then 2 else 3)
  else if u.2 = v.2 ∧ (u.1 + 1 = v.1 ∨ v.1 + 1 = u.1) then
    let r := min u.1 v.1
    let c := u.2
    let forward := u.1 < v.1
    if (r + c) % 2 = 1 ∧ c + 1 < n then (false, r, c, if forward then 0 else 3)
    else if (r + c) % 2 = 0 ∧ 0 < c then (false, r, c - 1, if forward then 1 else 2)
    else if c = 0 ∧ r = 0 then (true, 0, 0, if forward then 0 else 1)
    else
      let a := if c = 0 then r else n + r
      (true, 0, a / 2 - 1, if forward then 2 else 3)
  else if (u.1 + 1 = n ∧ v.1 = 0 ∨ v.1 + 1 = n ∧ u.1 = 0) ∧ u.2 + v.2 + 1 = n then
    let forward := u.1 + 1 = n
    let c := if forward then u.2 else v.2
    if c % 2 = 0 then (false, n - 1, c, if forward then 0 else 3)
    else (false, n - 1, c - 1, if forward then 1 else 2)
  else
    let forward := u = (0, 0)
    let w := if forward then v else u
    let a := if w.2 = 0 then w.1 else n + w.1
    (true, 0, (a - 1) / 2, if forward then 0 else 1)

def projectiveRawVertex {n : ℕ} (v : Fin n × Fin n) : ℕ × ℕ := (v.1.val, v.2.val)

theorem projectiveRecoveredPort_cell_ordinary_odd {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0)
    (r : Fin n) (c : Fin (n - 1)) (i : Fin 4)
    (hrow : r.val + 1 < n) (hp : (r.val + c.val) % 2 = 1) :
    projectiveRecoveredPort n (projectiveRawVertex (projectivePortLabel hn (Sum.inl (r, c), i)))
      (projectiveRawVertex (projectivePortLabel hn (projectivePortPair n (Sum.inl (r, c), i)))) =
      projectivePortCode (Sum.inl (r, c), i) := by
  have hr := r.isLt
  have hc := c.isLt
  rw [projectivePortPair_apply]
  change projectiveRecoveredPort n
    (projectiveRawVertex (projectiveFaceCorner hn (Sum.inl (r, c)) i))
    (projectiveRawVertex (projectiveFaceCorner hn (Sum.inl (r, c))
      (quadranglePair (projectiveFaceParity (Sum.inl (r, c))) i))) = _
  fin_cases i
  all_goals simp only [projectiveFaceCorner, projectiveFaceParity, projectivePortCode,
    hrow, hp, decide_true, decide_false, dite_true, dite_false, quadranglePair,
    Bool.true_eq, Bool.false_eq_true, if_true, if_false, Equiv.Perm.mul_apply,
    Equiv.swap_apply_def, Fin.ext_iff] 
  all_goals simp only [Fin.reduceFinMk, Fin.val_zero, Fin.val_one, Fin.val_two,
    Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, if_true, if_false,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]
  all_goals dsimp only [projectiveRawVertex, projectiveRecoveredPort]
  all_goals simp only [Nat.min_def]
  all_goals repeat' first | rfl | omega |
    (split <;> try simp only [Prod.mk.injEq, true_and, and_true, true_or, or_true,
      not_true_eq_false, Bool.false_eq_true, Bool.true_eq_false, Prod.fst, Prod.snd,
      ite_true, ite_false] at *)

theorem projectiveRecoveredPort_cell_ordinary_even {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0)
    (r : Fin n) (c : Fin (n - 1)) (i : Fin 4)
    (hrow : r.val + 1 < n) (hp : ¬(r.val + c.val) % 2 = 1) :
    projectiveRecoveredPort n (projectiveRawVertex (projectivePortLabel hn (Sum.inl (r, c), i)))
      (projectiveRawVertex (projectivePortLabel hn (projectivePortPair n (Sum.inl (r, c), i)))) =
      projectivePortCode (Sum.inl (r, c), i) := by
  have hr := r.isLt
  have hc := c.isLt
  rw [projectivePortPair_apply]
  change projectiveRecoveredPort n
    (projectiveRawVertex (projectiveFaceCorner hn (Sum.inl (r, c)) i))
    (projectiveRawVertex (projectiveFaceCorner hn (Sum.inl (r, c))
      (quadranglePair (projectiveFaceParity (Sum.inl (r, c))) i))) = _
  fin_cases i
  all_goals simp only [projectiveFaceCorner, projectiveFaceParity, projectivePortCode,
    hrow, hp, decide_true, decide_false, dite_true, dite_false, quadranglePair,
    Bool.true_eq, Bool.false_eq_true, if_true, if_false, Equiv.Perm.mul_apply,
    Equiv.swap_apply_def, Fin.ext_iff] 
  all_goals simp only [Fin.reduceFinMk, Fin.val_zero, Fin.val_one, Fin.val_two,
    Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, if_true, if_false,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]
  all_goals dsimp only [projectiveRawVertex, projectiveRecoveredPort]
  all_goals simp only [Nat.min_def]
  all_goals repeat' first | rfl | omega |
    (split <;> try simp only [Prod.mk.injEq, true_and, and_true, true_or, or_true,
      not_true_eq_false, Bool.false_eq_true, Bool.true_eq_false, Prod.fst, Prod.snd,
      ite_true, ite_false] at *)

theorem projectiveRecoveredPort_cell_wrap_odd {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0)
    (r : Fin n) (c : Fin (n - 1)) (i : Fin 4)
    (hrow : ¬r.val + 1 < n) (hp : (r.val + c.val) % 2 = 1) :
    projectiveRecoveredPort n (projectiveRawVertex (projectivePortLabel hn (Sum.inl (r, c), i)))
      (projectiveRawVertex (projectivePortLabel hn (projectivePortPair n (Sum.inl (r, c), i)))) =
      projectivePortCode (Sum.inl (r, c), i) := by
  have hr := r.isLt
  have hc := c.isLt
  rw [projectivePortPair_apply]
  change projectiveRecoveredPort n
    (projectiveRawVertex (projectiveFaceCorner hn (Sum.inl (r, c)) i))
    (projectiveRawVertex (projectiveFaceCorner hn (Sum.inl (r, c))
      (quadranglePair (projectiveFaceParity (Sum.inl (r, c))) i))) = _
  fin_cases i
  all_goals simp only [projectiveFaceCorner, projectiveFaceParity, projectivePortCode,
    hrow, hp, decide_true, decide_false, dite_true, dite_false, quadranglePair,
    Bool.true_eq, Bool.false_eq_true, if_true, if_false, Equiv.Perm.mul_apply,
    Equiv.swap_apply_def, Fin.ext_iff] 
  all_goals simp only [Fin.reduceFinMk, Fin.val_zero, Fin.val_one, Fin.val_two,
    Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, if_true, if_false,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]
  all_goals dsimp only [projectiveRawVertex, projectiveRecoveredPort]
  all_goals simp only [Nat.min_def]
  all_goals repeat' first | rfl | omega |
    (split <;> try simp only [Prod.mk.injEq, true_and, and_true, true_or, or_true,
      not_true_eq_false, Bool.false_eq_true, Bool.true_eq_false, Prod.fst, Prod.snd,
      ite_true, ite_false] at *)

theorem projectiveRecoveredPort_cell_wrap_even {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0)
    (r : Fin n) (c : Fin (n - 1)) (i : Fin 4)
    (hrow : ¬r.val + 1 < n) (hp : ¬(r.val + c.val) % 2 = 1) :
    projectiveRecoveredPort n (projectiveRawVertex (projectivePortLabel hn (Sum.inl (r, c), i)))
      (projectiveRawVertex (projectivePortLabel hn (projectivePortPair n (Sum.inl (r, c), i)))) =
      projectivePortCode (Sum.inl (r, c), i) := by
  have hr := r.isLt
  have hc := c.isLt
  rw [projectivePortPair_apply]
  change projectiveRecoveredPort n
    (projectiveRawVertex (projectiveFaceCorner hn (Sum.inl (r, c)) i))
    (projectiveRawVertex (projectiveFaceCorner hn (Sum.inl (r, c))
      (quadranglePair (projectiveFaceParity (Sum.inl (r, c))) i))) = _
  fin_cases i
  all_goals simp only [projectiveFaceCorner, projectiveFaceParity, projectivePortCode,
    hrow, hp, decide_true, decide_false, dite_true, dite_false, quadranglePair,
    Bool.true_eq, Bool.false_eq_true, if_true, if_false, Equiv.Perm.mul_apply,
    Equiv.swap_apply_def, Fin.ext_iff] 
  all_goals simp only [Fin.reduceFinMk, Fin.val_zero, Fin.val_one, Fin.val_two,
    Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, if_true, if_false,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]
  all_goals dsimp only [projectiveRawVertex, projectiveRecoveredPort]
  all_goals simp only [Nat.min_def]
  all_goals repeat' first | rfl | omega |
    (split <;> try simp only [Prod.mk.injEq, true_and, and_true, true_or, or_true,
      not_true_eq_false, Bool.false_eq_true, Bool.true_eq_false, Prod.fst, Prod.snd,
      ite_true, ite_false] at *)

theorem projectiveRecoveredPort_cell {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0)
    (r : Fin n) (c : Fin (n - 1)) (i : Fin 4) :
    projectiveRecoveredPort n (projectiveRawVertex (projectivePortLabel hn (Sum.inl (r, c), i)))
      (projectiveRawVertex (projectivePortLabel hn (projectivePortPair n (Sum.inl (r, c), i)))) =
      projectivePortCode (Sum.inl (r, c), i) := by
  by_cases hrow : r.val + 1 < n
  · by_cases hp : (r.val + c.val) % 2 = 1
    · exact projectiveRecoveredPort_cell_ordinary_odd hn hnEven r c i hrow hp
    · exact projectiveRecoveredPort_cell_ordinary_even hn hnEven r c i hrow hp
  · by_cases hp : (r.val + c.val) % 2 = 1
    · exact projectiveRecoveredPort_cell_wrap_odd hn hnEven r c i hrow hp
    · exact projectiveRecoveredPort_cell_wrap_even hn hnEven r c i hrow hp


theorem projectiveRecoveredPort_cap_zero {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0)
    (j : Fin (n - 1)) :
    projectiveRecoveredPort n (projectiveRawVertex (projectivePortLabel hn (Sum.inr j, (0 : Fin 4))))
      (projectiveRawVertex (projectivePortLabel hn (projectivePortPair n (Sum.inr j, (0 : Fin 4))))) =
      projectivePortCode (Sum.inr j, (0 : Fin 4)) := by
  have hj := j.isLt
  rw [projectivePortPair_apply]
  change projectiveRecoveredPort n
    (projectiveRawVertex (projectiveFaceCorner hn (Sum.inr j) (0 : Fin 4)))
    (projectiveRawVertex (projectiveFaceCorner hn (Sum.inr j) (quadranglePair false (0 : Fin 4)))) = _
  all_goals simp only [projectiveFaceCorner, projectivePortCode, quadranglePair,
    Bool.false_eq_true, if_false, Equiv.Perm.mul_apply, Equiv.swap_apply_def, Fin.ext_iff]
  all_goals simp only [Fin.reduceFinMk, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff,
    if_true, if_false, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals dsimp only [projectiveBoundary, projectiveRoot, projectiveRawVertex]
  all_goals split_ifs <;> try omega
  all_goals dsimp only [projectiveRawVertex, projectiveRecoveredPort]
  all_goals simp only [Nat.min_def]
  all_goals repeat' first | rfl | omega |
    (split <;> try simp only [Prod.mk.injEq, true_and, and_true, true_or, or_true,
      not_true_eq_false, Bool.false_eq_true, Bool.true_eq_false, Prod.fst, Prod.snd,
      ite_true, ite_false] at *)

theorem projectiveRecoveredPort_cap_one {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0)
    (j : Fin (n - 1)) :
    projectiveRecoveredPort n (projectiveRawVertex (projectivePortLabel hn (Sum.inr j, (1 : Fin 4))))
      (projectiveRawVertex (projectivePortLabel hn (projectivePortPair n (Sum.inr j, (1 : Fin 4))))) =
      projectivePortCode (Sum.inr j, (1 : Fin 4)) := by
  have hj := j.isLt
  rw [projectivePortPair_apply]
  change projectiveRecoveredPort n
    (projectiveRawVertex (projectiveFaceCorner hn (Sum.inr j) (1 : Fin 4)))
    (projectiveRawVertex (projectiveFaceCorner hn (Sum.inr j) (quadranglePair false (1 : Fin 4)))) = _
  all_goals simp only [projectiveFaceCorner, projectivePortCode, quadranglePair,
    Bool.false_eq_true, if_false, Equiv.Perm.mul_apply, Equiv.swap_apply_def, Fin.ext_iff]
  all_goals simp only [Fin.reduceFinMk, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff,
    if_true, if_false, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals dsimp only [projectiveBoundary, projectiveRoot, projectiveRawVertex]
  all_goals split_ifs <;> try omega
  all_goals dsimp only [projectiveRawVertex, projectiveRecoveredPort]
  all_goals simp only [Nat.min_def]
  all_goals repeat' first | rfl | omega |
    (split <;> try simp only [Prod.mk.injEq, true_and, and_true, true_or, or_true,
      not_true_eq_false, Bool.false_eq_true, Bool.true_eq_false, Prod.fst, Prod.snd,
      ite_true, ite_false] at *)

theorem projectiveRecoveredPort_cap_two {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0)
    (j : Fin (n - 1)) :
    projectiveRecoveredPort n (projectiveRawVertex (projectivePortLabel hn (Sum.inr j, (2 : Fin 4))))
      (projectiveRawVertex (projectivePortLabel hn (projectivePortPair n (Sum.inr j, (2 : Fin 4))))) =
      projectivePortCode (Sum.inr j, (2 : Fin 4)) := by
  have hj := j.isLt
  rw [projectivePortPair_apply]
  change projectiveRecoveredPort n
    (projectiveRawVertex (projectiveFaceCorner hn (Sum.inr j) (2 : Fin 4)))
    (projectiveRawVertex (projectiveFaceCorner hn (Sum.inr j) (quadranglePair false (2 : Fin 4)))) = _
  all_goals simp only [projectiveFaceCorner, projectivePortCode, quadranglePair,
    Bool.false_eq_true, if_false, Equiv.Perm.mul_apply, Equiv.swap_apply_def, Fin.ext_iff]
  all_goals simp only [Fin.reduceFinMk, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff,
    if_true, if_false, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals dsimp only [projectiveBoundary, projectiveRoot, projectiveRawVertex]
  all_goals split_ifs <;> try omega
  all_goals dsimp only [projectiveRawVertex, projectiveRecoveredPort]
  all_goals simp only [Nat.min_def]
  all_goals repeat' first | rfl | omega |
    (split <;> try simp only [Prod.mk.injEq, true_and, and_true, true_or, or_true,
      not_true_eq_false, Bool.false_eq_true, Bool.true_eq_false, Prod.fst, Prod.snd,
      ite_true, ite_false] at *)

theorem projectiveRecoveredPort_cap_three {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0)
    (j : Fin (n - 1)) :
    projectiveRecoveredPort n (projectiveRawVertex (projectivePortLabel hn (Sum.inr j, (3 : Fin 4))))
      (projectiveRawVertex (projectivePortLabel hn (projectivePortPair n (Sum.inr j, (3 : Fin 4))))) =
      projectivePortCode (Sum.inr j, (3 : Fin 4)) := by
  have hj := j.isLt
  rw [projectivePortPair_apply]
  change projectiveRecoveredPort n
    (projectiveRawVertex (projectiveFaceCorner hn (Sum.inr j) (3 : Fin 4)))
    (projectiveRawVertex (projectiveFaceCorner hn (Sum.inr j) (quadranglePair false (3 : Fin 4)))) = _
  all_goals simp only [projectiveFaceCorner, projectivePortCode, quadranglePair,
    Bool.false_eq_true, if_false, Equiv.Perm.mul_apply, Equiv.swap_apply_def, Fin.ext_iff]
  all_goals simp only [Fin.reduceFinMk, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff,
    if_true, if_false, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  all_goals dsimp only [projectiveBoundary, projectiveRoot, projectiveRawVertex]
  all_goals split_ifs <;> try omega
  all_goals dsimp only [projectiveRawVertex, projectiveRecoveredPort]
  all_goals simp only [Nat.min_def]
  all_goals repeat' first | rfl | omega |
    (split <;> try simp only [Prod.mk.injEq, true_and, and_true, true_or, or_true,
      not_true_eq_false, Bool.false_eq_true, Bool.true_eq_false, Prod.fst, Prod.snd,
      ite_true, ite_false] at *)

theorem projectiveRecoveredPort_cap {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0)
    (j : Fin (n - 1)) (i : Fin 4) :
    projectiveRecoveredPort n (projectiveRawVertex (projectivePortLabel hn (Sum.inr j, i)))
      (projectiveRawVertex (projectivePortLabel hn (projectivePortPair n (Sum.inr j, i)))) =
      projectivePortCode (Sum.inr j, i) := by
  fin_cases i
  · exact projectiveRecoveredPort_cap_zero hn hnEven j
  · exact projectiveRecoveredPort_cap_one hn hnEven j
  · exact projectiveRecoveredPort_cap_two hn hnEven j
  · exact projectiveRecoveredPort_cap_three hn hnEven j

theorem projectiveRecoveredPort_leftInverse {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0)
    (d : ProjectivePort n) :
    projectiveRecoveredPort n (projectiveRawVertex (projectivePortLabel hn d))
      (projectiveRawVertex (projectivePortLabel hn (projectivePortPair n d))) =
      projectivePortCode d := by
  rcases d with ⟨f, i⟩
  rcases f with ⟨r, c⟩ | j
  · exact projectiveRecoveredPort_cell hn hnEven r c i
  · exact projectiveRecoveredPort_cap hn hnEven j i

theorem projectiveAlphaPair_injective {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0) :
    Function.Injective (orientedPortPair (projectivePortLabel hn) (projectivePortPair n)) := by
  intro d e he
  apply projectivePortCode_injective
  rw [← projectiveRecoveredPort_leftInverse hn hnEven d,
    ← projectiveRecoveredPort_leftInverse hn hnEven e]
  have hleft := congrArg Prod.fst he
  have hright := congrArg Prod.snd he
  change projectivePortLabel hn d = projectivePortLabel hn e at hleft
  change projectivePortLabel hn (projectivePortPair n d) =
    projectivePortLabel hn (projectivePortPair n e) at hright
  rw [hleft, hright]

end
end Erdos73
