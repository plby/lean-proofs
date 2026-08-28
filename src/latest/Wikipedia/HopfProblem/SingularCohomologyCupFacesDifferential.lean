import Wikipedia.HopfProblem.SingularCohomologyCupFaces

/-!
# Consecutive faces and the singular differential

The three identities below describe deleting a vertex before, after,
or within a consecutive block of vertices. They are equalities of the
actual continuous affine simplex maps.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SingularCohomologyCup

open FirstHurewicz

theorem succAbove_val {n : ℕ} (i : Fin (n + 1)) (j : Fin n) :
    (i.succAbove j).val = if j.val < i.val then j.val else j.val + 1 := by
  by_cases h : j.val < i.val
  · rw [Fin.succAbove_of_castSucc_lt i j h, if_pos h]
    rfl
  · rw [Fin.succAbove_of_le_castSucc i j (Nat.le_of_not_gt h), if_neg h]
    rfl

theorem face_window_before (a k n : ℕ) (h : a + k ≤ n)
    (i : Fin (n + 2)) (hi : i.val ≤ a) :
    (simplexFace n i).comp (windowFace a k n h) =
      windowFace (a + 1) k (n + 1) (by omega) := by
  simp only [simplexFace_eq_vertexMap, windowFace, vertexMap_comp]
  congr 1
  funext j
  apply Fin.ext
  simp only [Function.comp_apply, succAbove_val]
  rw [if_neg (show ¬a + j.val < i.val by omega)]
  omega

theorem face_window_after (a k n : ℕ) (h : a + k ≤ n)
    (i : Fin (n + 2)) (hi : a + k < i.val) :
    (simplexFace n i).comp (windowFace a k n h) =
      windowFace a k (n + 1) (by omega) := by
  simp only [simplexFace_eq_vertexMap, windowFace, vertexMap_comp]
  congr 1
  funext j
  apply Fin.ext
  simp only [Function.comp_apply, succAbove_val]
  rw [if_pos (show a + j.val < i.val by omega)]

theorem face_window_middle (a k n : ℕ) (h : a + k ≤ n)
    (i : Fin (n + 2)) (j : Fin (k + 2)) (hij : i.val = a + j.val) :
    (simplexFace n i).comp (windowFace a k n h) =
      (windowFace a (k + 1) (n + 1) (by omega)).comp (simplexFace k j) := by
  simp only [simplexFace_eq_vertexMap, windowFace, vertexMap_comp]
  congr 1
  funext l
  apply Fin.ext
  simp only [Function.comp_apply, succAbove_val, windowIndex_val]
  by_cases hl : l.val < j.val
  · rw [if_pos hl, if_pos (show a + l.val < i.val by omega)]
  · rw [if_neg hl, if_neg (show ¬a + l.val < i.val by omega)]
    omega

theorem window_face_last (a k n : ℕ) (h : a + (k + 1) ≤ n) :
    (windowFace a (k + 1) n h).comp (simplexFace k (Fin.last (k + 1))) =
      windowFace a k n (by omega) := by
  simp only [simplexFace_eq_vertexMap, windowFace, vertexMap_comp]
  congr 1
  funext j
  apply Fin.ext
  simp only [Function.comp_apply, windowIndex_val, succAbove_val, Fin.val_last]
  rw [if_pos j.isLt]

theorem window_face_zero (a k n : ℕ) (h : a + (k + 1) ≤ n) :
    (windowFace a (k + 1) n h).comp (simplexFace k 0) =
      windowFace (a + 1) k n (by omega) := by
  simp only [simplexFace_eq_vertexMap, windowFace, vertexMap_comp]
  congr 1
  funext j
  apply Fin.ext
  simp only [Function.comp_apply, windowIndex_val, succAbove_val, Fin.val_zero,
    Nat.not_lt_zero, if_false]
  omega

end Wikipedia.HopfProblem.SingularCohomologyCup
