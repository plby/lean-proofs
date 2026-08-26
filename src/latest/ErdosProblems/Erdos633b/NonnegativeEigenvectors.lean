import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Equality at an extremal coordinate of a negative eigenvector forces every
positive outgoing matrix entry to lead to the opposite normalized coordinate. -/

namespace Erdos633b

open Matrix

theorem weighted_opposite_of_max {ι : Type*} [Fintype ι] (a y : ι → ℝ)
    (t L : ℝ) (ha : ∀ j, 0 ≤ a j) (hy : ∀ j, |y j| ≤ |t|)
    (hs : ∑ j, a j = L) (he : ∑ j, a j * y j = -L * t) :
    ∀ j, 0 < a j → y j = -t := by
  classical
  by_cases ht : 0 ≤ t
  · have hn (j : ι) : 0 ≤ a j * (y j + t) := by
      have hj := (abs_le.mp ((hy j).trans_eq (abs_of_nonneg ht))).1
      exact mul_nonneg (ha j) (by linarith)
    have hz : ∑ j, a j * (y j + t) = 0 := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hs, he]
      ring
    have hh := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hn j)).mp hz
    intro j hj
    have hj0 := hh j (Finset.mem_univ j)
    exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp hj0).resolve_left hj.ne')
  · have ht' : t ≤ 0 := le_of_not_ge ht
    have hn (j : ι) : 0 ≤ a j * (-t - y j) := by
      have hj := (abs_le.mp ((hy j).trans_eq (abs_of_nonpos ht'))).2
      exact mul_nonneg (ha j) (by linarith)
    have hz : ∑ j, a j * (-t - y j) = 0 := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hs, he]
      ring
    have hh := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hn j)).mp hz
    intro j hj
    have hj0 := hh j (Finset.mem_univ j)
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hj0).resolve_left hj.ne')).symm

namespace NonnegativeMatrix

noncomputable def weight {ι : Type*} (D : Matrix ι ι ℝ) (v : ι → ℝ) (i j : ι) : ℝ :=
  D i j * v j / v i

theorem weight_sum {ι : Type*} [Fintype ι] {D : Matrix ι ι ℝ}
    {v : ι → ℝ} {L : ℝ} (hv : ∀ i, 0 < v i) (h : D *ᵥ v = L • v) (i : ι) :
    ∑ j, weight D v i j = L := by
  have hi := congrFun h i
  change (∑ j, D i j * v j) = L * v i at hi
  simp only [weight, ← Finset.sum_div, hi, mul_div_cancel_right₀ L (hv i).ne']

theorem weight_negative_sum {ι : Type*} [Fintype ι] {D : Matrix ι ι ℝ}
    {v w : ι → ℝ} {L : ℝ} (hv : ∀ i, 0 < v i)
    (h : D *ᵥ w = -L • w) (i : ι) :
    ∑ j, weight D v i j * (w j / v j) = -L * (w i / v i) := by
  have hi := congrFun h i
  change (∑ j, D i j * w j) = -L * w i at hi
  have he (j : ι) : weight D v i j * (w j / v j) = D i j * w j / v i := by
    unfold weight
    field_simp [(hv i).ne', (hv j).ne']
  simp_rw [he]
  rw [← Finset.sum_div, hi, mul_div_assoc]

theorem opposite_of_max {ι : Type*} [Fintype ι] {D : Matrix ι ι ℝ}
    (hD : ∀ i j, 0 ≤ D i j) {v w : ι → ℝ} {L : ℝ}
    (hv : ∀ i, 0 < v i) (hpos : D *ᵥ v = L • v) (hneg : D *ᵥ w = -L • w)
    (i : ι) (hmax : ∀ j, |w j / v j| ≤ |w i / v i|) :
    ∀ j, 0 < D i j → w j / v j = -(w i / v i) := by
  apply fun j hj => weighted_opposite_of_max (weight D v i) (fun j => w j / v j)
    (w i / v i) L (fun j => div_nonneg (mul_nonneg (hD i j) (hv j).le) (hv i).le)
    hmax (weight_sum hv hpos i) (weight_negative_sum hv hneg i) j
    (div_pos (mul_pos hj (hv j)) (hv i))

theorem diagonal_zero_of_max {ι : Type*} [Fintype ι] {D : Matrix ι ι ℝ}
    (hD : ∀ i j, 0 ≤ D i j) {v w : ι → ℝ} {L : ℝ}
    (hv : ∀ i, 0 < v i) (hpos : D *ᵥ v = L • v) (hneg : D *ᵥ w = -L • w)
    (i : ι) (hmax : ∀ j, |w j / v j| ≤ |w i / v i|) (hi : w i ≠ 0) :
    D i i = 0 := by
  by_contra hn
  have hp := lt_of_le_of_ne (hD i i) (Ne.symm hn)
  have he := opposite_of_max hD hv hpos hneg i hmax i hp
  have hy : w i / v i ≠ 0 := div_ne_zero hi (hv i).ne'
  apply hy
  linarith


theorem exists_positive_entry {ι : Type*} [Fintype ι] {D : Matrix ι ι ℝ}
    (hD : ∀ i j, 0 ≤ D i j) {v : ι → ℝ} {L : ℝ}
    (hv : ∀ i, 0 < v i) (hL : 0 < L) (hpos : D *ᵥ v = L • v) (i : ι) :
    ∃ j, 0 < D i j := by
  have hs : 0 < ∑ j, D i j * v j := by
    change 0 < (D *ᵥ v) i
    rw [hpos]
    exact mul_pos hL (hv i)
  obtain ⟨j, _, hj⟩ := (Finset.sum_pos_iff_of_nonneg
    (fun j _ => mul_nonneg (hD i j) (hv j).le)).mp hs
  exact ⟨j, (mul_pos_iff.mp hj).resolve_right (by intro h; linarith [hv j]) |>.1⟩

theorem exists_max_coordinate {ι : Type*} [Finite ι] {v w : ι → ℝ}
    (hv : ∀ i, 0 < v i) (hw : w ≠ 0) :
    ∃ i, w i ≠ 0 ∧ ∀ j, |w j / v j| ≤ |w i / v i| := by
  classical
  let _ := Fintype.ofFinite ι
  obtain ⟨k, hk⟩ : ∃ k, w k ≠ 0 := by
    by_contra h
    push Not at h
    exact hw (funext h)
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun i => |w i / v i|)
    ⟨k, Finset.mem_univ k⟩
  refine ⟨i, ?_, fun j => hi j (Finset.mem_univ j)⟩
  intro hz
  have hki := hi k (Finset.mem_univ k)
  rw [hz, zero_div, abs_zero] at hki
  have hp := abs_pos.mpr (div_ne_zero hk (hv k).ne')
  linarith

theorem positive_diagonal_excluded_of_max {ι : Type*} [Fintype ι]
    {D : Matrix ι ι ℝ} (hD : ∀ i j, 0 ≤ D i j) {v w : ι → ℝ} {L : ℝ}
    (hv : ∀ i, 0 < v i) (hpos : D *ᵥ v = L • v) (hneg : D *ᵥ w = -L • w)
    (i : ι) (hmax : ∀ j, |w j / v j| ≤ |w i / v i|) (hi : w i ≠ 0)
    (k : ι) (hk : 0 < D k k) : D i k = 0 := by
  by_contra hn
  have hp := lt_of_le_of_ne (hD i k) (Ne.symm hn)
  have he := opposite_of_max hD hv hpos hneg i hmax k hp
  have habs : |w k / v k| = |w i / v i| := by rw [he, abs_neg]
  have hk0 : w k ≠ 0 := by
    intro hz
    rw [hz, zero_div] at he
    exact div_ne_zero hi (hv i).ne' (neg_eq_zero.mp he.symm)
  have hd := diagonal_zero_of_max hD hv hpos hneg k
    (fun j => (hmax j).trans_eq habs.symm) hk0
  exact hk.ne' hd

theorem exists_two_zero_diagonals {ι : Type*} [Fintype ι] {D : Matrix ι ι ℝ}
    (hD : ∀ i j, 0 ≤ D i j) {v w : ι → ℝ} {L : ℝ}
    (hv : ∀ i, 0 < v i) (hL : 0 < L) (hw : w ≠ 0)
    (hpos : D *ᵥ v = L • v) (hneg : D *ᵥ w = -L • w) :
    ∃ i j, i ≠ j ∧ D i i = 0 ∧ D j j = 0 ∧ 0 < D i j ∧
      w i ≠ 0 ∧ w j ≠ 0 ∧
      (∀ k, |w k / v k| ≤ |w i / v i|) ∧
      (∀ k, |w k / v k| ≤ |w j / v j|) := by
  obtain ⟨i, hi, hmax⟩ := exists_max_coordinate hv hw
  obtain ⟨j, hj⟩ := exists_positive_entry hD hv hL hpos i
  have he := opposite_of_max hD hv hpos hneg i hmax j hj
  have habs : |w j / v j| = |w i / v i| := by rw [he, abs_neg]
  have hj0 : w j ≠ 0 := by
    intro hz
    rw [hz, zero_div] at he
    exact div_ne_zero hi (hv i).ne' (neg_eq_zero.mp he.symm)
  have hmaxj : ∀ k, |w k / v k| ≤ |w j / v j| :=
    fun k => (hmax k).trans_eq habs.symm
  have hii := diagonal_zero_of_max hD hv hpos hneg i hmax hi
  have hjj := diagonal_zero_of_max hD hv hpos hneg j hmaxj hj0
  have hij : i ≠ j := by
    intro hij
    subst j
    exact hj.ne' hii
  exact ⟨i, j, hij, hii, hjj, hj, hi, hj0, hmax, hmaxj⟩

end NonnegativeMatrix

end Erdos633b
