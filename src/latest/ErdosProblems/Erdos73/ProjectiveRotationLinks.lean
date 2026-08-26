import ErdosProblems.Erdos73.ProjectiveRotation
import ErdosProblems.Erdos73.PermutationCutCycles

/-! Shared face edges connect the corresponding ports in the vertex rotation. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open Equiv

theorem projectiveBetaPair_injective {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0) :
    Function.Injective (orientedPortPair (projectivePortLabel hn)
      (projectivePortOpposite n * projectivePortPair n)) := by
  intro d e he
  apply (projectiveRotation hn hnEven).injective
  apply projectiveAlphaPair_injective hn hnEven
  rw [projectiveRotation_pair, projectiveRotation_pair, he]

theorem projectiveSameCycle_of_shared_pair {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0)
    (d e : ProjectivePort n)
    (hpair : orientedPortPair (projectivePortLabel hn) (projectivePortPair n) d =
      orientedPortPair (projectivePortLabel hn) (projectivePortOpposite n * projectivePortPair n) e) :
    (projectiveAcrossPermutation hn hnEven).SameCycle d e := by
  have he : projectiveAcrossFace hn hnEven d = e := by
    apply projectiveBetaPair_injective hn hnEven
    exact (projectiveAcrossFace_pair hn hnEven d).trans hpair
  have hh := (Perm.SameCycle.refl (projectiveAcrossPermutation hn hnEven) d).apply_right
  change (projectiveAcrossPermutation hn hnEven).SameCycle d (projectiveAcrossFace hn hnEven d) at hh
  exact he ▸ hh

theorem projectiveSameCycle_label {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0)
    {d e : ProjectivePort n} (h : (projectiveAcrossPermutation hn hnEven).SameCycle d e) :
    projectivePortLabel hn d = projectivePortLabel hn e :=
  label_eq_of_sameCycle (projectiveAcrossPermutation hn hnEven) (projectivePortLabel hn)
    (projectiveAcrossFace_label hn hnEven) h

theorem projectiveSameCycle_right_top {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0)
    (r : Fin n) (c : Fin (n - 1)) (hc : c.val + 2 < n) :
    (projectiveAcrossPermutation hn hnEven).SameCycle
      (Sum.inl (r, c), 1) (Sum.inl (r, ⟨c.val + 1, by omega⟩), 0) := by
  have hr := r.isLt
  by_cases hp : (r.val + c.val) % 2 = 1
  · apply projectiveSameCycle_of_shared_pair hn hnEven
    dsimp only [orientedPortPair]
    rw [projectivePortPair_apply, projectivePortOtherPair_apply]
    have hq : ¬(r.val + (c.val + 1)) % 2 = 1 := by omega
    dsimp only [projectivePortLabel, projectiveFaceParity]
    simp only [hp, hq, decide_true, decide_false, Bool.not_false]
    by_cases hrow : r.val + 1 < n
    all_goals simp only [projectiveFaceCorner, hrow, dite_true, dite_false, quadranglePair,
      Bool.true_eq, if_true, Equiv.Perm.mul_apply, Equiv.swap_apply_def, Fin.ext_iff,
      Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, if_false,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons, Prod.mk.injEq, Fin.val_mk, true_and, and_true]
    all_goals omega
  · apply Perm.SameCycle.symm
    apply projectiveSameCycle_of_shared_pair hn hnEven
    dsimp only [orientedPortPair]
    rw [projectivePortPair_apply, projectivePortOtherPair_apply]
    have hq : (r.val + (c.val + 1)) % 2 = 1 := by omega
    dsimp only [projectivePortLabel, projectiveFaceParity]
    simp only [hp, hq, decide_true, decide_false, Bool.not_false]
    by_cases hrow : r.val + 1 < n
    all_goals simp only [projectiveFaceCorner, hrow, dite_true, dite_false, quadranglePair,
      Bool.true_eq, if_true, Equiv.Perm.mul_apply, Equiv.swap_apply_def, Fin.ext_iff,
      Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, if_false,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons, Prod.mk.injEq, Fin.val_mk, true_and, and_true]
    all_goals omega

theorem projectiveSameCycle_below_right {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0)
    (r : Fin n) (c : Fin (n - 1)) (hr : r.val + 1 < n) :
    (projectiveAcrossPermutation hn hnEven).SameCycle
      (Sum.inl (r, c), 2) (Sum.inl (⟨r.val + 1, hr⟩, c), 1) := by
  by_cases hp : (r.val + c.val) % 2 = 1
  · apply Perm.SameCycle.symm
    apply projectiveSameCycle_of_shared_pair hn hnEven
    dsimp only [orientedPortPair]
    rw [projectivePortPair_apply, projectivePortOtherPair_apply]
    have hq : ¬(r.val + 1 + c.val) % 2 = 1 := by omega
    dsimp only [projectivePortLabel, projectiveFaceParity]
    simp only [hp, hq, decide_true, decide_false, Bool.not_true]
    by_cases hrow : r.val + 1 + 1 < n
    all_goals simp only [projectiveFaceCorner, hr, hrow, dite_true, dite_false, quadranglePair,
      Bool.false_eq_true, if_true, if_false, Equiv.Perm.mul_apply, Equiv.swap_apply_def, Fin.ext_iff,
      Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons, Prod.mk.injEq, Fin.val_mk, true_and, and_true]
  · apply projectiveSameCycle_of_shared_pair hn hnEven
    dsimp only [orientedPortPair]
    rw [projectivePortPair_apply, projectivePortOtherPair_apply]
    have hq : (r.val + 1 + c.val) % 2 = 1 := by omega
    dsimp only [projectivePortLabel, projectiveFaceParity]
    simp only [hp, hq, decide_true, decide_false, Bool.not_true]
    by_cases hrow : r.val + 1 + 1 < n
    all_goals simp only [projectiveFaceCorner, hr, hrow, dite_true, dite_false, quadranglePair,
      Bool.false_eq_true, if_true, if_false, Equiv.Perm.mul_apply, Equiv.swap_apply_def, Fin.ext_iff,
      Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons, Prod.mk.injEq, Fin.val_mk, true_and, and_true]

theorem projectiveSameCycle_wrap_right {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0)
    (r : Fin n) (c : Fin (n - 1)) (hr : ¬r.val + 1 < n) :
    (projectiveAcrossPermutation hn hnEven).SameCycle (Sum.inl (r, c), 2)
      (Sum.inl (⟨0, by omega⟩, ⟨n - 2 - c.val, by omega⟩), 0) := by
  have hrr := r.isLt
  have hcc := c.isLt
  have hsmall : 1 < n := by omega
  by_cases hp : (r.val + c.val) % 2 = 1
  · apply Perm.SameCycle.symm
    apply projectiveSameCycle_of_shared_pair hn hnEven
    dsimp only [orientedPortPair]
    rw [projectivePortPair_apply, projectivePortOtherPair_apply]
    have hq : ¬(n - 2 - c.val) % 2 = 1 := by omega
    dsimp only [projectivePortLabel, projectiveFaceParity]
    simp only [Nat.zero_add, hp, hq, decide_true, decide_false, Bool.not_true]
    simp only [projectiveFaceCorner, hr, hsmall, dite_true, dite_false, quadranglePair,
      Bool.false_eq_true, if_true, if_false, Equiv.Perm.mul_apply, Equiv.swap_apply_def, Fin.ext_iff,
      Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, Nat.zero_add,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons, Prod.mk.injEq, Fin.val_mk, true_and, and_true]
    omega
  · apply projectiveSameCycle_of_shared_pair hn hnEven
    dsimp only [orientedPortPair]
    rw [projectivePortPair_apply, projectivePortOtherPair_apply]
    have hq : (n - 2 - c.val) % 2 = 1 := by omega
    dsimp only [projectivePortLabel, projectiveFaceParity]
    simp only [Nat.zero_add, hp, hq, decide_true, decide_false, Bool.not_true]
    simp only [projectiveFaceCorner, hr, hsmall, dite_true, dite_false, quadranglePair,
      Bool.false_eq_true, if_true, if_false, Equiv.Perm.mul_apply, Equiv.swap_apply_def, Fin.ext_iff,
      Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, Nat.zero_add,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons, Prod.mk.injEq, Fin.val_mk, true_and, and_true]
    omega

theorem projectiveSameCycle_below_left {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0)
    (r : Fin n) (c : Fin (n - 1)) (hr : r.val + 1 < n) :
    (projectiveAcrossPermutation hn hnEven).SameCycle
      (Sum.inl (r, c), 3) (Sum.inl (⟨r.val + 1, hr⟩, c), 0) := by
  by_cases hp : (r.val + c.val) % 2 = 1
  · apply Perm.SameCycle.symm
    apply projectiveSameCycle_of_shared_pair hn hnEven
    dsimp only [orientedPortPair]
    rw [projectivePortPair_apply, projectivePortOtherPair_apply]
    have hq : ¬(r.val + 1 + c.val) % 2 = 1 := by omega
    dsimp only [projectivePortLabel, projectiveFaceParity]
    simp only [hp, hq, decide_true, decide_false, Bool.not_true]
    by_cases hrow : r.val + 1 + 1 < n
    all_goals simp only [projectiveFaceCorner, hr, hrow, dite_true, dite_false, quadranglePair,
      Bool.false_eq_true, if_true, if_false, Equiv.Perm.mul_apply, Equiv.swap_apply_def, Fin.ext_iff,
      Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons, Prod.mk.injEq, Fin.val_mk, true_and, and_true]
  · apply projectiveSameCycle_of_shared_pair hn hnEven
    dsimp only [orientedPortPair]
    rw [projectivePortPair_apply, projectivePortOtherPair_apply]
    have hq : (r.val + 1 + c.val) % 2 = 1 := by omega
    dsimp only [projectivePortLabel, projectiveFaceParity]
    simp only [hp, hq, decide_true, decide_false, Bool.not_true]
    by_cases hrow : r.val + 1 + 1 < n
    all_goals simp only [projectiveFaceCorner, hr, hrow, dite_true, dite_false, quadranglePair,
      Bool.false_eq_true, if_true, if_false, Equiv.Perm.mul_apply, Equiv.swap_apply_def, Fin.ext_iff,
      Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons, Prod.mk.injEq, Fin.val_mk, true_and, and_true]

theorem projectiveSameCycle_wrap_left {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0)
    (r : Fin n) (c : Fin (n - 1)) (hr : ¬r.val + 1 < n) :
    (projectiveAcrossPermutation hn hnEven).SameCycle (Sum.inl (r, c), 3)
      (Sum.inl (⟨0, by omega⟩, ⟨n - 2 - c.val, by omega⟩), 1) := by
  have hrr := r.isLt
  have hcc := c.isLt
  have hsmall : 1 < n := by omega
  by_cases hp : (r.val + c.val) % 2 = 1
  · apply Perm.SameCycle.symm
    apply projectiveSameCycle_of_shared_pair hn hnEven
    dsimp only [orientedPortPair]
    rw [projectivePortPair_apply, projectivePortOtherPair_apply]
    have hq : ¬(n - 2 - c.val) % 2 = 1 := by omega
    dsimp only [projectivePortLabel, projectiveFaceParity]
    simp only [Nat.zero_add, hp, hq, decide_true, decide_false, Bool.not_true]
    simp only [projectiveFaceCorner, hr, hsmall, dite_true, dite_false, quadranglePair,
      Bool.false_eq_true, if_true, if_false, Equiv.Perm.mul_apply, Equiv.swap_apply_def, Fin.ext_iff,
      Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, Nat.zero_add,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons, Prod.mk.injEq, Fin.val_mk, true_and, and_true]
    omega
  · apply projectiveSameCycle_of_shared_pair hn hnEven
    dsimp only [orientedPortPair]
    rw [projectivePortPair_apply, projectivePortOtherPair_apply]
    have hq : (n - 2 - c.val) % 2 = 1 := by omega
    dsimp only [projectivePortLabel, projectiveFaceParity]
    simp only [Nat.zero_add, hp, hq, decide_true, decide_false, Bool.not_true]
    simp only [projectiveFaceCorner, hr, hsmall, dite_true, dite_false, quadranglePair,
      Bool.false_eq_true, if_true, if_false, Equiv.Perm.mul_apply, Equiv.swap_apply_def, Fin.ext_iff,
      Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, Nat.zero_add,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons, Prod.mk.injEq, Fin.val_mk, true_and, and_true]
    omega

end
end Erdos73
