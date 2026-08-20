import ErdosProblems.Erdos957.GeometryCore
import ErdosProblems.Erdos957.HullRadial

/-!
# Seam-safe seven-window indexing for Erdős problem 957

This module contains only the finite cyclic-index arithmetic used by the
large-diameter locality argument.  It turns exclusion from the seven shifts
centered at a source into the two closed cyclic arcs beginning at the fourth
successor and ending at the fourth predecessor.
-/

noncomputable section

namespace Erdos957WindowIndex

open Erdos957
open Erdos957GeometryCore

private lemma ofNat_eq_nsmul_one {n : ℕ} [NeZero n] (m : ℕ) :
    Fin.ofNat n m = m • (1 : Fin n) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [succ_nsmul, ← ih]
      apply Fin.ext
      simp [Fin.ofNat, Fin.add_def, Nat.add_mod]

theorem sevenShift_finRotate {n : ℕ} [NeZero n] (j : Fin 7) (a : Fin n) :
    sevenShift (finRotate n) j a =
      a - Fin.ofNat n 3 + Fin.ofNat n j.1 := by
  rw [ofNat_eq_nsmul_one, ofNat_eq_nsmul_one]
  fin_cases j <;>
    simp [sevenShift, finRotate_apply, finRotate_symm_apply,
      Equiv.Perm.mul_apply, pow_succ] <;>
    abel

theorem mem_sevenShift_of_offset_le_three {n : ℕ} [NeZero n]
    (a z : Fin n) (h : (z - a).val ≤ 3) :
    ∃ j : Fin 7, z = sevenShift (finRotate n) j a := by
  let j : Fin 7 := ⟨(z - a).val + 3, by omega⟩
  refine ⟨j, ?_⟩
  rw [sevenShift_finRotate]
  have hj : j.1 = (z - a).val + 3 := rfl
  rw [show z = a + (z - a) by abel, hj]
  have hz : Fin.ofNat n (z - a).val = z - a := Fin.ofNat_val_eq_self _
  have hadd : Fin.ofNat n ((z - a).val + 3) =
      Fin.ofNat n (z - a).val + Fin.ofNat n 3 := by
    apply Fin.ext
    simp [Fin.ofNat, Fin.add_def, Nat.add_mod]
  rw [hadd, hz]
  abel

theorem mem_sevenShift_of_offset_near_end {n : ℕ} [NeZero n]
    (a z : Fin n) (h : n ≤ (z - a).val + 3) :
    ∃ j : Fin 7, z = sevenShift (finRotate n) j a := by
  have hn : 0 < n := NeZero.pos n
  let t := n - (z - a).val
  have ht : t ≤ 3 := by omega
  have htpos : 0 < t := by
    dsimp [t]
    omega
  let j : Fin 7 := ⟨3 - t, by omega⟩
  refine ⟨j, ?_⟩
  rw [sevenShift_finRotate]
  have hdt : (z - a).val + t = n := by
    dsimp [t]
    omega
  have hz : Fin.ofNat n (z - a).val + Fin.ofNat n t = 0 := by
    apply Fin.ext
    simp [Fin.ofNat, Fin.add_def, hdt]
  have hjt : j.1 + t = 3 := by
    dsimp [j]
    omega
  have hj : Fin.ofNat n j.1 + Fin.ofNat n t = Fin.ofNat n 3 := by
    apply Fin.ext
    simp [Fin.ofNat, Fin.add_def, hjt]
  have hza : z - a = Fin.ofNat n (z - a).val :=
    (Fin.ofNat_val_eq_self _).symm
  rw [show z = a + (z - a) by abel, hza]
  rw [show Fin.ofNat n j.1 = Fin.ofNat n 3 - Fin.ofNat n t by
    exact eq_sub_iff_add_eq.mpr hj]
  have hd : Fin.ofNat n (z - a).val = -Fin.ofNat n t := by
    exact eq_neg_of_add_eq_zero_left hz
  rw [hd]
  abel

theorem outside_sevenShift_offset_bounds {n : ℕ} [NeZero n]
    (a z : Fin n)
    (hout : ∀ j : Fin 7, z ≠ sevenShift (finRotate n) j a) :
    4 ≤ (z - a).val ∧ (z - a).val + 4 ≤ n := by
  constructor
  · by_contra h
    have hle : (z - a).val ≤ 3 := by omega
    obtain ⟨j, hj⟩ := mem_sevenShift_of_offset_le_three a z hle
    exact hout j hj
  · by_contra h
    have hnear : n ≤ (z - a).val + 3 := by omega
    obtain ⟨j, hj⟩ := mem_sevenShift_of_offset_near_end a z hnear
    exact hout j hj

theorem outside_sevenShift_arc_partition {n : ℕ} [NeZero n]
    (a q z : Fin n)
    (hq : ∀ j : Fin 7, q ≠ sevenShift (finRotate n) j a)
    (hz : ∀ j : Fin 7, z ≠ sevenShift (finRotate n) j a) :
    RadiallySortedCyclicHullOrder.InClosedCCWArc
        (a + Fin.ofNat n 4) z q ∨
      RadiallySortedCyclicHullOrder.InClosedCCWArc
        q z (a - Fin.ofNat n 4) := by
  obtain ⟨hq4, hqend⟩ := outside_sevenShift_offset_bounds a q hq
  obtain ⟨hz4, hzend⟩ := outside_sevenShift_offset_bounds a z hz
  have hn8 : 8 ≤ n := by omega
  let four : Fin n := Fin.ofNat n 4
  have hfour : four.val = 4 := by
    simp [four, Nat.mod_eq_of_lt (by omega : 4 < n)]
  have hfour0 : four ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp [hfour] at this
  let left : Fin n := a - four
  have hleftOffset : (left - a).val = n - 4 := by
    have heq : left - a = -four := by
      dsimp [left]
      abel
    rw [heq, Fin.val_neg, if_neg hfour0, hfour]
  by_cases hzq : (z - a).val ≤ (q - a).val
  · left
    rw [RadiallySortedCyclicHullOrder.inClosedCCWArc_iff_sub_val_le]
    have hzEq : z - (a + four) = (z - a) - four := by abel
    have hqEq : q - (a + four) = (q - a) - four := by abel
    rw [hzEq, hqEq]
    have hfz : four ≤ z - a := by
      apply Fin.le_iff_val_le_val.mpr
      simpa [hfour] using hz4
    have hfq : four ≤ q - a := by
      apply Fin.le_iff_val_le_val.mpr
      simpa [hfour] using hq4
    rw [Fin.sub_val_of_le hfz, Fin.sub_val_of_le hfq]
    omega
  · right
    rw [RadiallySortedCyclicHullOrder.inClosedCCWArc_iff_sub_val_le]
    have hqz : (q - a).val ≤ (z - a).val := by omega
    have hzqEq : z - q = (z - a) - (q - a) := by abel
    have hleftqEq : left - q = (left - a) - (q - a) := by abel
    rw [hzqEq, hleftqEq]
    have hqzFin : q - a ≤ z - a := Fin.le_iff_val_le_val.mpr hqz
    have hqleftFin : q - a ≤ left - a := by
      apply Fin.le_iff_val_le_val.mpr
      rw [hleftOffset]
      omega
    rw [Fin.sub_val_of_le hqzFin, Fin.sub_val_of_le hqleftFin,
      hleftOffset]
    omega

/-- The opposite endpoint need not itself be outside the seven-window.
Every vertex `z` outside the window lies either on the closed forward arc
from the fourth successor to an arbitrary vertex `q`, or on the closed
forward arc from `q` to the fourth predecessor. -/
theorem outside_sevenShift_arc_partition_any_q {n : ℕ} [NeZero n]
    (a q z : Fin n)
    (hz : ∀ j : Fin 7, z ≠ sevenShift (finRotate n) j a) :
    RadiallySortedCyclicHullOrder.InClosedCCWArc
        (a + Fin.ofNat n 4) z q ∨
      RadiallySortedCyclicHullOrder.InClosedCCWArc
        q z (a - Fin.ofNat n 4) := by
  obtain ⟨hz4, hzend⟩ := outside_sevenShift_offset_bounds a z hz
  have hn8 : 8 ≤ n := by omega
  let four : Fin n := Fin.ofNat n 4
  have hfour : four.val = 4 := by
    simp [four, Nat.mod_eq_of_lt (by omega : 4 < n)]
  have hfour0 : four ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp [hfour] at this
  let left : Fin n := a - four
  have hleftOffset : (left - a).val = n - 4 := by
    have heq : left - a = -four := by
      dsimp [left]
      abel
    rw [heq, Fin.val_neg, if_neg hfour0, hfour]
  by_cases hzq : (z - a).val ≤ (q - a).val
  · left
    rw [RadiallySortedCyclicHullOrder.inClosedCCWArc_iff_sub_val_le]
    have hzEq : z - (a + four) = (z - a) - four := by abel
    have hqEq : q - (a + four) = (q - a) - four := by abel
    rw [hzEq, hqEq]
    have hfz : four ≤ z - a := by
      apply Fin.le_iff_val_le_val.mpr
      simpa [hfour] using hz4
    have hfq : four ≤ q - a := by
      apply Fin.le_iff_val_le_val.mpr
      rw [hfour]
      omega
    rw [Fin.sub_val_of_le hfz, Fin.sub_val_of_le hfq]
    omega
  · right
    rw [RadiallySortedCyclicHullOrder.inClosedCCWArc_iff_sub_val_le]
    have hqz : (q - a).val ≤ (z - a).val := by omega
    have hzqEq : z - q = (z - a) - (q - a) := by abel
    have hleftqEq : left - q = (left - a) - (q - a) := by abel
    rw [hzqEq, hleftqEq]
    have hqzFin : q - a ≤ z - a := Fin.le_iff_val_le_val.mpr hqz
    have hqleftFin : q - a ≤ left - a := by
      apply Fin.le_iff_val_le_val.mpr
      rw [hleftOffset]
      omega
    rw [Fin.sub_val_of_le hqzFin, Fin.sub_val_of_le hqleftFin,
      hleftOffset]
    omega

end Erdos957WindowIndex
