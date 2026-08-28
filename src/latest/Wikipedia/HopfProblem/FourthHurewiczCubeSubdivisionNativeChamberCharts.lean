import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionNativeChamberChartsBasic

/-!
# Boundary faces of inserted native chamber charts

When insertion separates two coordinates that agree on a source face, the
new coordinate is an interpolation between equal endpoints. All other old
faces keep their original affine face, and the two new faces are exactly the
lower and upper endpoint graphs.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.NativeSubdivision

variable {n : ℕ}

theorem insertChamberMap_zero_last (e : Equiv.Perm (Fin n)) (r : Fin (n + 1))
    (chart : NativeChamberChart e) (u : NativeCube (Fin (n + 1)))
    (i : Fin (n + 1)) (hi : i.val + 1 = n + 1)
    (hu : u (insertPermutation e r i) = 0) :
    insertChamberMap e r chart u (insertPermutation e r i) = 0 := by
  revert hi hu
  refine Fin.succAboveCases r ?_ (fun k => ?_) i
  · intro hi hu
    simp only [insertPermutation_apply_at] at hu ⊢
    rw [insertChamberMap_apply_last, hu, Set.Icc.convexComb_zero]
    exact chamberLower_last e r chart (chamberOldCoordinates u) (by omega)
  · intro hi hu
    have hk := chamberSuccAbove_val_cases r k
    simp only [insertPermutation_apply_succAbove, insertChamberMap_apply_castSucc] at hu ⊢
    exact chart.zero_last (chamberOldCoordinates u) k (by omega) hu

theorem insertChamberMap_zero_adjacent (e : Equiv.Perm (Fin n)) (r : Fin (n + 1))
    (chart : NativeChamberChart e) (u : NativeCube (Fin (n + 1)))
    (i j : Fin (n + 1)) (hij : i.val + 1 = j.val)
    (hu : u (insertPermutation e r i) = 0) :
    insertChamberMap e r chart u (insertPermutation e r i) =
      insertChamberMap e r chart u (insertPermutation e r j) := by
  revert hij hu
  refine Fin.succAboveCases r ?_ (fun k => ?_) i
  · refine Fin.succAboveCases r ?_ (fun l => ?_) j
    · intro hij
      omega
    · intro hij hu
      have hl := chamberSuccAbove_val_cases r l
      have hr : r.val = l.val := by omega
      simp only [insertPermutation_apply_at, insertPermutation_apply_succAbove,
        insertChamberMap_apply_last, insertChamberMap_apply_castSucc] at hu ⊢
      rw [hu, Set.Icc.convexComb_zero]
      exact chamberLower_of_rank e r chart (chamberOldCoordinates u) l hr
  · refine Fin.succAboveCases r ?_ (fun l => ?_) j
    · intro hij hu
      have hk := chamberSuccAbove_val_cases r k
      have hr : r.val = k.val + 1 := by omega
      simp only [insertPermutation_apply_at, insertPermutation_apply_succAbove,
        insertChamberMap_apply_last, insertChamberMap_apply_castSucc] at hu ⊢
      rw [chamberLower_zero_face e r chart (chamberOldCoordinates u) k hr hu,
        chamberUpper_of_rank e r chart (chamberOldCoordinates u) k hr]
      simp
    · intro hij hu
      have hk := chamberSuccAbove_val_cases r k
      have hl := chamberSuccAbove_val_cases r l
      have hkl : k.val + 1 = l.val := by omega
      simp only [insertPermutation_apply_succAbove, insertChamberMap_apply_castSucc] at hu ⊢
      exact chart.zero_adjacent (chamberOldCoordinates u) k l hkl hu

theorem insertChamberMap_one_first (e : Equiv.Perm (Fin n)) (r : Fin (n + 1))
    (chart : NativeChamberChart e) (u : NativeCube (Fin (n + 1)))
    (i : Fin (n + 1)) (hi : i.val = 0)
    (hu : u (insertPermutation e r i) = 1) :
    insertChamberMap e r chart u (insertPermutation e r i) = 1 := by
  revert hi hu
  refine Fin.succAboveCases r ?_ (fun k => ?_) i
  · intro hi hu
    simp only [insertPermutation_apply_at] at hu ⊢
    rw [insertChamberMap_apply_last, hu, Set.Icc.convexComb_one]
    exact chamberUpper_first e r chart (chamberOldCoordinates u) hi
  · intro hi hu
    have hk := chamberSuccAbove_val_cases r k
    simp only [insertPermutation_apply_succAbove, insertChamberMap_apply_castSucc] at hu ⊢
    exact chart.one_first (chamberOldCoordinates u) k (by omega) hu

theorem insertChamberMap_one_adjacent (e : Equiv.Perm (Fin n)) (r : Fin (n + 1))
    (chart : NativeChamberChart e) (u : NativeCube (Fin (n + 1)))
    (i j : Fin (n + 1)) (hij : j.val + 1 = i.val)
    (hu : u (insertPermutation e r i) = 1) :
    insertChamberMap e r chart u (insertPermutation e r i) =
      insertChamberMap e r chart u (insertPermutation e r j) := by
  revert hij hu
  refine Fin.succAboveCases r ?_ (fun k => ?_) i
  · refine Fin.succAboveCases r ?_ (fun l => ?_) j
    · intro hij
      omega
    · intro hij hu
      have hl := chamberSuccAbove_val_cases r l
      have hr : r.val = l.val + 1 := by omega
      simp only [insertPermutation_apply_at, insertPermutation_apply_succAbove,
        insertChamberMap_apply_last, insertChamberMap_apply_castSucc] at hu ⊢
      rw [hu, Set.Icc.convexComb_one]
      exact chamberUpper_of_rank e r chart (chamberOldCoordinates u) l hr
  · refine Fin.succAboveCases r ?_ (fun l => ?_) j
    · intro hij hu
      have hk := chamberSuccAbove_val_cases r k
      have hr : r.val = k.val := by omega
      simp only [insertPermutation_apply_at, insertPermutation_apply_succAbove,
        insertChamberMap_apply_last, insertChamberMap_apply_castSucc] at hu ⊢
      rw [chamberLower_of_rank e r chart (chamberOldCoordinates u) k hr,
        chamberUpper_one_face e r chart (chamberOldCoordinates u) k hr hu]
      simp
    · intro hij hu
      have hk := chamberSuccAbove_val_cases r k
      have hl := chamberSuccAbove_val_cases r l
      have hkl : l.val + 1 = k.val := by omega
      simp only [insertPermutation_apply_succAbove, insertChamberMap_apply_castSucc] at hu ⊢
      exact chart.one_adjacent (chamberOldCoordinates u) k l hkl hu

/-- Insert one coordinate, preserving all four boundary-face conditions. -/
def insertChamberChart (e : Equiv.Perm (Fin n)) (r : Fin (n + 1))
    (chart : NativeChamberChart e) : NativeChamberChart (insertPermutation e r) where
  toContinuousMap := insertChamberMap e r chart
  zero_last := insertChamberMap_zero_last e r chart
  zero_adjacent := insertChamberMap_zero_adjacent e r chart
  one_first := insertChamberMap_one_first e r chart
  one_adjacent := insertChamberMap_one_adjacent e r chart

@[simp] theorem insertChamberChart_toContinuousMap (e : Equiv.Perm (Fin n))
    (r : Fin (n + 1)) (chart : NativeChamberChart e) :
    (insertChamberChart e r chart).toContinuousMap = insertChamberMap e r chart := rfl

@[simp] theorem insertChamberChart_apply_castSucc (e : Equiv.Perm (Fin n))
    (r : Fin (n + 1)) (chart : NativeChamberChart e)
    (u : NativeCube (Fin (n + 1))) (k : Fin n) :
    (insertChamberChart e r chart).toContinuousMap u k.castSucc =
      chart.toContinuousMap (chamberOldCoordinates u) k :=
  insertChamberMap_apply_castSucc e r chart u k

@[simp] theorem insertChamberChart_apply_last (e : Equiv.Perm (Fin n))
    (r : Fin (n + 1)) (chart : NativeChamberChart e) (u : NativeCube (Fin (n + 1))) :
    (insertChamberChart e r chart).toContinuousMap u (Fin.last n) =
      Set.Icc.convexComb (chamberLower e r chart (chamberOldCoordinates u))
        (chamberUpper e r chart (chamberOldCoordinates u)) (u (Fin.last n)) :=
  insertChamberMap_apply_last e r chart u

@[ext] theorem NativeChamberChart.ext {e : Equiv.Perm (Fin n)}
    {f g : NativeChamberChart e} (h : f.toContinuousMap = g.toContinuousMap) : f = g := by
  cases f
  cases g
  cases h
  rfl

end Wikipedia.HopfProblem.HigherHurewicz.NativeSubdivision
