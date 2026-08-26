import ErdosProblems.Erdos73.ProjectiveRotationLinks

/-! Every strip port reaches a fixed reference port for its vertex label. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open Equiv

def projectiveReferencePort {n : ℕ} (hn : 2 ≤ n) (v : Fin n × Fin n) : ProjectivePort n :=
  if hc : v.2.val + 1 < n then (Sum.inl (v.1, ⟨v.2.val, by omega⟩), 0)
  else (Sum.inl (v.1, ⟨n - 2, by omega⟩), 1)

def ProjectiveReachesReference {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0)
    (d : ProjectivePort n) : Prop :=
  (projectiveAcrossPermutation hn hnEven).SameCycle d (projectiveReferencePort hn (projectivePortLabel hn d))

theorem projectiveReference_transfer {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0)
    {d e : ProjectivePort n} (hde : (projectiveAcrossPermutation hn hnEven).SameCycle d e)
    (he : ProjectiveReachesReference hn hnEven e) : ProjectiveReachesReference hn hnEven d := by
  have hl := projectiveSameCycle_label hn hnEven hde
  unfold ProjectiveReachesReference at *
  rw [hl]
  exact hde.trans he

theorem projectiveReference_of_across {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0)
    (d : ProjectivePort n) (h : ProjectiveReachesReference hn hnEven (projectiveAcrossFace hn hnEven d)) :
    ProjectiveReachesReference hn hnEven d :=
  projectiveReference_transfer hn hnEven
    (Perm.SameCycle.refl (projectiveAcrossPermutation hn hnEven) d).apply_right h

theorem projectiveReference_cell_zero {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0)
    (r : Fin n) (c : Fin (n - 1)) : ProjectiveReachesReference hn hnEven (Sum.inl (r, c), 0) := by
  have hc : c.val + 1 < n := by have hh := c.isLt; omega
  have hl : projectivePortLabel hn (Sum.inl (r, c), 0) = (r, ⟨c.val, by omega⟩) := by
    dsimp only [projectivePortLabel, projectiveFaceCorner]
    split <;> rfl
  unfold ProjectiveReachesReference
  rw [hl, projectiveReferencePort, dif_pos hc]

theorem projectiveReference_cell_one {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0)
    (r : Fin n) (c : Fin (n - 1)) : ProjectiveReachesReference hn hnEven (Sum.inl (r, c), 1) := by
  have hc : c.val + 1 < n := by have hh := c.isLt; omega
  by_cases hi : c.val + 2 < n
  · exact projectiveReference_transfer hn hnEven (projectiveSameCycle_right_top hn hnEven r c hi)
      (projectiveReference_cell_zero hn hnEven r ⟨c.val + 1, by omega⟩)
  have hl : projectivePortLabel hn (Sum.inl (r, c), 1) = (r, ⟨c.val + 1, hc⟩) := by
    dsimp only [projectivePortLabel, projectiveFaceCorner]
    split <;> rfl
  have href : projectiveReferencePort hn (projectivePortLabel hn (Sum.inl (r, c), 1)) =
      (Sum.inl (r, c), 1) := by
    rw [hl, projectiveReferencePort, dif_neg (by omega)]
    apply Prod.ext
    · apply congrArg Sum.inl
      apply Prod.ext
      · rfl
      · exact Fin.ext (by dsimp only; omega)
    · rfl
  unfold ProjectiveReachesReference
  rw [href]

theorem projectiveReference_cell_two {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0)
    (r : Fin n) (c : Fin (n - 1)) : ProjectiveReachesReference hn hnEven (Sum.inl (r, c), 2) := by
  by_cases hr : r.val + 1 < n
  · exact projectiveReference_transfer hn hnEven (projectiveSameCycle_below_right hn hnEven r c hr)
      (projectiveReference_cell_one hn hnEven ⟨r.val + 1, hr⟩ c)
  · exact projectiveReference_transfer hn hnEven (projectiveSameCycle_wrap_right hn hnEven r c hr)
      (projectiveReference_cell_zero hn hnEven ⟨0, by omega⟩ ⟨n - 2 - c.val, by omega⟩)

theorem projectiveReference_cell_three {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0)
    (r : Fin n) (c : Fin (n - 1)) : ProjectiveReachesReference hn hnEven (Sum.inl (r, c), 3) := by
  by_cases hr : r.val + 1 < n
  · exact projectiveReference_transfer hn hnEven (projectiveSameCycle_below_left hn hnEven r c hr)
      (projectiveReference_cell_zero hn hnEven ⟨r.val + 1, hr⟩ c)
  · exact projectiveReference_transfer hn hnEven (projectiveSameCycle_wrap_left hn hnEven r c hr)
      (projectiveReference_cell_one hn hnEven ⟨0, by omega⟩ ⟨n - 2 - c.val, by omega⟩)

theorem projectiveReference_cell {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0)
    (r : Fin n) (c : Fin (n - 1)) (i : Fin 4) :
    ProjectiveReachesReference hn hnEven (Sum.inl (r, c), i) := by
  fin_cases i
  · exact projectiveReference_cell_zero hn hnEven r c
  · exact projectiveReference_cell_one hn hnEven r c
  · exact projectiveReference_cell_two hn hnEven r c
  · exact projectiveReference_cell_three hn hnEven r c

end
end Erdos73
