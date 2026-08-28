import Wikipedia.HopfProblem.HigherHurewiczCubeTriangulationGeometry
import Wikipedia.HopfProblem.HigherHurewiczCubeTriangulationSort
import Mathlib.Algebra.BigOperators.Fin

/-!
# Successive differences of ordered cube coordinates

Adding the endpoint values one and zero makes barycentric coordinates
successive differences in every dimension, including dimension zero.
-/

noncomputable section

open Set
open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.CubeTriangulation

open FirstHurewicz

/-- A finite sum of successive differences telescopes to its endpoints. -/
theorem sum_fin_differences {n : ℕ} (a : Fin (n + 1) → ℝ) :
    ∑ i : Fin n, (a i.castSucc - a i.succ) = a 0 - a (Fin.last n) := by
  rw [Finset.sum_sub_distrib]
  have h₀ := Fin.sum_univ_succ a
  have h₁ := Fin.sum_univ_castSucc a
  linarith

/-- A tail of a finite sum of successive differences also telescopes. -/
theorem sum_fin_differences_tail (n : ℕ) (a : Fin (n + 1) → ℝ) (i : Fin n) :
    ∑ k : Fin n, (if i.val ≤ k.val then a k.castSucc - a k.succ else 0) =
      a i.castSucc - a (Fin.last n) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    cases i using Fin.cases with
    | zero =>
      simpa only [Fin.val_zero, Nat.zero_le, if_pos, Fin.castSucc_zero]
        using sum_fin_differences a
    | succ i =>
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, Fin.val_succ, Nat.add_one_le_iff,
        Nat.not_lt_zero, if_false, Nat.lt_succ_iff, zero_add, Fin.castSucc_succ]
      simpa only [Fin.succ_last] using ih (fun k => a k.succ) i

/-- The ordered cube coordinates with endpoint values one and zero. -/
def cubeExtendedCoordinates {n : ℕ} (e : Equiv.Perm (Fin n)) (u : CubeN n) :
    Fin (n + 2) → ℝ :=
  Fin.cons 1 (Fin.snoc (fun i => (u (e i) : ℝ)) 0)

@[simp] theorem cubeExtendedCoordinates_zero {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : CubeN n) : cubeExtendedCoordinates e u 0 = 1 := by
  simp only [cubeExtendedCoordinates, Fin.cons_zero]

@[simp] theorem cubeExtendedCoordinates_last {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : CubeN n) :
    cubeExtendedCoordinates e u (Fin.last (n + 1)) = 0 := by
  change cubeExtendedCoordinates e u (Fin.last n).succ = 0
  unfold cubeExtendedCoordinates
  simp only [Fin.cons_succ, Fin.snoc_last]

@[simp] theorem cubeExtendedCoordinates_inner {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : CubeN n) (i : Fin n) :
    cubeExtendedCoordinates e u i.castSucc.succ = (u (e i) : ℝ) := by
  simp only [cubeExtendedCoordinates, Fin.cons_succ, Fin.snoc_castSucc]

theorem cubeExtendedCoordinates_nonneg {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : CubeN n) (i : Fin (n + 2)) :
    0 ≤ cubeExtendedCoordinates e u i := by
  cases i using Fin.cases with
  | zero => simp only [cubeExtendedCoordinates_zero, zero_le_one]
  | succ i =>
    cases i using Fin.lastCases with
    | last => simp only [cubeExtendedCoordinates, Fin.cons_succ, Fin.snoc_last, le_refl]
    | cast i =>
      simpa only [cubeExtendedCoordinates_inner] using (u (e i)).property.1

theorem cubeExtendedCoordinates_le_one {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : CubeN n) (i : Fin (n + 2)) :
    cubeExtendedCoordinates e u i ≤ 1 := by
  cases i using Fin.cases with
  | zero => simp only [cubeExtendedCoordinates_zero, le_refl]
  | succ i =>
    cases i using Fin.lastCases with
    | last => simp only [cubeExtendedCoordinates, Fin.cons_succ, Fin.snoc_last, zero_le_one]
    | cast i =>
      simpa only [cubeExtendedCoordinates_inner] using (u (e i)).property.2

theorem cubeExtendedCoordinates_antitone {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : CubeN n) (h : SortedCoordinates u e) :
    Antitone (cubeExtendedCoordinates e u) := by
  intro i j hij
  cases i using Fin.cases with
  | zero => exact cubeExtendedCoordinates_le_one e u j
  | succ i =>
    cases j using Fin.cases with
    | zero =>
      have hh : i.val + 1 ≤ 0 := (Fin.le_iff_val_le_val).mp hij
      omega
    | succ j =>
      cases j using Fin.lastCases with
      | last =>
        simpa only [Fin.succ_last, cubeExtendedCoordinates_last]
          using cubeExtendedCoordinates_nonneg e u i.succ
      | cast j =>
        cases i using Fin.lastCases with
        | last =>
          have hj : j.val < n := j.isLt
          have hh := (Fin.le_iff_val_le_val).mp hij
          simp only [Fin.val_succ, Fin.val_last, Fin.val_castSucc] at hh
          omega
        | cast i =>
          have hh : i ≤ j := by
            simpa only [Fin.succ_le_succ_iff, Fin.castSucc_le_castSucc_iff] using hij
          have hreal : (u (e j) : ℝ) ≤ (u (e i) : ℝ) := h hh
          simpa only [cubeExtendedCoordinates_inner] using hreal

/-- The barycentric coefficients are successive differences. -/
def cubeBarycentric {n : ℕ} (e : Equiv.Perm (Fin n)) (u : CubeN n) :
    Fin (n + 1) → ℝ :=
  fun i => cubeExtendedCoordinates e u i.castSucc - cubeExtendedCoordinates e u i.succ

@[simp] theorem cubeBarycentric_zero {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (u : CubeN (n + 1)) :
    cubeBarycentric e u 0 = 1 - (u (e 0) : ℝ) := by
  simp only [cubeBarycentric, Fin.castSucc_zero, cubeExtendedCoordinates,
    Fin.cons_zero, Fin.cons_succ, Fin.snoc_apply_zero]

@[simp] theorem cubeBarycentric_last {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (u : CubeN (n + 1)) :
    cubeBarycentric e u (Fin.last (n + 1)) = (u (e (Fin.last n)) : ℝ) := by
  change cubeExtendedCoordinates e u (Fin.last n).castSucc.succ -
    cubeExtendedCoordinates e u (Fin.last (n + 2)) = _
  simp only [cubeExtendedCoordinates_inner, cubeExtendedCoordinates_last, sub_zero]

@[simp] theorem cubeBarycentric_inner {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (u : CubeN (n + 1)) (i : Fin n) :
    cubeBarycentric e u i.succ.castSucc =
      (u (e i.castSucc) : ℝ) - (u (e i.succ) : ℝ) := by
  change cubeExtendedCoordinates e u i.castSucc.castSucc.succ -
    cubeExtendedCoordinates e u i.succ.castSucc.succ = _
  simp only [cubeExtendedCoordinates_inner]

theorem cubeBarycentric_nonneg {n : ℕ} (e : Equiv.Perm (Fin n)) (u : CubeN n)
    (h : SortedCoordinates u e) (i : Fin (n + 1)) : 0 ≤ cubeBarycentric e u i :=
  sub_nonneg.mpr (cubeExtendedCoordinates_antitone e u h (Nat.le_succ i.val))

theorem cubeBarycentric_sum {n : ℕ} (e : Equiv.Perm (Fin n)) (u : CubeN n) :
    ∑ i, cubeBarycentric e u i = 1 := by
  unfold cubeBarycentric
  rw [sum_fin_differences]
  simp only [cubeExtendedCoordinates_zero, cubeExtendedCoordinates_last, sub_zero]

/-- Summing the coefficients after a coordinate recovers that coordinate. -/
theorem cubeBarycentric_tail {n : ℕ} (e : Equiv.Perm (Fin n)) (u : CubeN n)
    (i : Fin n) :
    ∑ k : Fin (n + 1), (if i.val < k.val then cubeBarycentric e u k else 0) =
      (u (e i) : ℝ) := by
  have h := sum_fin_differences_tail (n + 1) (cubeExtendedCoordinates e u) i.succ
  simpa only [Fin.val_succ, Nat.succ_le_iff, cubeBarycentric,
    Fin.castSucc_succ, cubeExtendedCoordinates_inner, cubeExtendedCoordinates_last,
    sub_zero] using h

end Wikipedia.HopfProblem.HigherHurewicz.CubeTriangulation
