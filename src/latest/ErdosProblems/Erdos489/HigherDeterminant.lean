import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos489

open scoped BigOperators
open Matrix

/-- A determinant bound with a separate uniform bound for each column. -/
theorem abs_det_le_factorial_mul_prod_column_bounds
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (c : ι → ℝ)
    (hc : ∀ j, 0 < c j)
    (hM : ∀ i j, |M i j| ≤ c j) :
    |M.det| ≤ (Fintype.card ι).factorial * ∏ j, c j := by
  let C : Matrix ι ι ℝ := fun i j => M i j / c j
  have hC : ∀ i j, |C i j| ≤ (1 : ℝ) := by
    intro i j
    dsimp [C]
    rw [abs_div, div_le_one (abs_pos.mpr (hc j).ne')]
    simpa [abs_of_pos (hc j)] using hM i j
  have hdetC : |C.det| ≤ ((Fintype.card ι).factorial : ℝ) := by
    have h := Matrix.det_le (A := C) (abv := AbsoluteValue.abs) (x := (1 : ℝ)) hC
    simpa using h
  have hMC : M = Matrix.of (fun i j => c j * C i j) := by
    ext i j
    dsimp [C]
    field_simp [(hc j).ne']
  have hdet : M.det = (∏ j, c j) * C.det := by
    rw [hMC, Matrix.det_mul_row]
  rw [hdet, abs_mul]
  have hcprod : 0 ≤ ∏ j, c j := by
    exact Finset.prod_nonneg fun j _ => (hc j).le
  rw [abs_of_nonneg hcprod]
  calc
    (∏ j, c j) * |C.det| ≤
        (∏ j, c j) * ((Fintype.card ι).factorial : ℝ) :=
      mul_le_mul_of_nonneg_left hdetC hcprod
    _ = (Fintype.card ι).factorial * ∏ j, c j := by ring

/-- The covered-number matrix associated to several gap starts and one witness
modulus per column.  Its large part is constant across every column of a row. -/
def shiftedIncidenceMatrix {k : ℕ}
    (n : Fin (k + 1) → ℝ) (u : Fin (k + 1) → Fin (k + 1) → ℝ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
  fun i j => n i + u i j

/-- Replace each noninitial column by its difference from the preceding
column.  This cancels the large row-dependent starts. -/
def adjacentDifferenceMatrix {k : ℕ}
    (n : Fin (k + 1) → ℝ) (u : Fin (k + 1) → Fin (k + 1) → ℝ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
  fun i => Fin.cases (n i + u i 0)
    (fun j => u i j.succ - u i j.castSucc)

/-- Successively subtracting the preceding column leaves the determinant
unchanged. -/
theorem det_shiftedIncidenceMatrix_eq_det_adjacentDifferenceMatrix
    {k : ℕ} (n : Fin (k + 1) → ℝ)
    (u : Fin (k + 1) → Fin (k + 1) → ℝ) :
    (shiftedIncidenceMatrix n u).det =
      (adjacentDifferenceMatrix n u).det := by
  apply Matrix.det_eq_of_forall_col_eq_smul_add_pred (fun _ => (1 : ℝ))
  · intro i
    simp [shiftedIncidenceMatrix, adjacentDifferenceMatrix]
  · intro i j
    simp [shiftedIncidenceMatrix, adjacentDifferenceMatrix]
    ring

/-- A `k+1` by `k+1` covered-number determinant is small after the common
row starts are cancelled.  The stronger factor `G^k` is available when every
offset lies in `[0,G]` (rather than merely having absolute value at most `G`). -/
theorem abs_det_shiftedIncidenceMatrix_le
    {k : ℕ} (n : Fin (k + 1) → ℝ)
    (u : Fin (k + 1) → Fin (k + 1) → ℝ) (X G : ℝ)
    (hn0 : ∀ i, 0 ≤ n i) (hnX : ∀ i, n i ≤ X)
    (hu0 : ∀ i j, 0 ≤ u i j) (huG : ∀ i j, u i j ≤ G)
    (hG : 0 < G) :
    |(shiftedIncidenceMatrix n u).det| ≤
      (k + 1).factorial * (X + G) * G ^ k := by
  let c : Fin (k + 1) → ℝ := Fin.cases (X + G) (fun _ => G)
  have hX0 : 0 ≤ X := le_trans (hn0 0) (hnX 0)
  have hc : ∀ j, 0 < c j := by
    intro j
    refine Fin.cases ?_ (fun _ => ?_) j
    · dsimp [c]
      linarith
    · exact hG
  have hentry : ∀ i j, |adjacentDifferenceMatrix n u i j| ≤ c j := by
    intro i j
    refine Fin.cases ?_ (fun q => ?_) j
    · dsimp [adjacentDifferenceMatrix, c]
      rw [abs_of_nonneg (add_nonneg (hn0 i) (hu0 i 0))]
      linarith [hnX i, huG i 0]
    · dsimp [adjacentDifferenceMatrix, c]
      rw [abs_le]
      constructor <;> linarith [hu0 i q.succ, hu0 i q.castSucc,
        huG i q.succ, huG i q.castSucc]
  rw [det_shiftedIncidenceMatrix_eq_det_adjacentDifferenceMatrix]
  calc
    |(adjacentDifferenceMatrix n u).det| ≤
        (Fintype.card (Fin (k + 1))).factorial * ∏ j, c j :=
      abs_det_le_factorial_mul_prod_column_bounds
        (adjacentDifferenceMatrix n u) c hc hentry
    _ = (k + 1).factorial * (X + G) * G ^ k := by
      simp [c, Fin.prod_univ_succ, mul_assoc]

/-- If every entry in column `j` is divisible by `a j`, their product divides
the determinant. -/
theorem prod_dvd_det_of_dvd_columns
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℤ) (M : Matrix ι ι ℤ)
    (hdiv : ∀ i j, a j ∣ M i j) :
    (∏ j, a j) ∣ M.det := by
  classical
  let Q : Matrix ι ι ℤ := fun i j => Classical.choose (hdiv i j)
  have hfactor : M = Matrix.of (fun i j => a j * Q i j) := by
    ext i j
    change M i j = a j * Q i j
    exact Classical.choose_spec (hdiv i j)
  refine ⟨Q.det, ?_⟩
  rw [hfactor, Matrix.det_mul_row]

/-- Integer covered-number matrix for natural starts and offsets. -/
def shiftedIncidenceMatrixInt {k : ℕ}
    (n : Fin (k + 1) → ℕ) (u : Fin (k + 1) → Fin (k + 1) → ℕ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ :=
  fun i j => ((n i + u i j : ℕ) : ℤ)

/-- The product of witness moduli divides every square incidence minor in which
one modulus labels each column. -/
theorem int_prod_moduli_dvd_shiftedIncidenceMatrix_det
    {k : ℕ} (a n : Fin (k + 1) → ℕ)
    (u : Fin (k + 1) → Fin (k + 1) → ℕ)
    (hdiv : ∀ i j, a j ∣ n i + u i j) :
    (((∏ j, a j : ℕ) : ℕ) : ℤ) ∣
      (shiftedIncidenceMatrixInt n u).det := by
  have hzdiv : ∀ i j, (a j : ℤ) ∣ shiftedIncidenceMatrixInt n u i j := by
    intro i j
    rcases hdiv i j with ⟨q, hq⟩
    refine ⟨(q : ℤ), ?_⟩
    dsimp [shiftedIncidenceMatrixInt]
    exact_mod_cast hq
  simpa using prod_dvd_det_of_dvd_columns
    (fun j => (a j : ℤ)) (shiftedIncidenceMatrixInt n u) hzdiv

/-- A nonzero integer multiple of `P` has real absolute value at least `P`. -/
theorem int_eq_zero_of_dvd_of_real_abs_lt
    (P : ℕ) (d : ℤ) (hdvd : (P : ℤ) ∣ d)
    (hsmall : |(d : ℝ)| < (P : ℝ)) :
    d = 0 := by
  by_contra hd0
  have hnatpos : 0 < d.natAbs := Int.natAbs_pos.mpr hd0
  have hnatdvd : P ∣ d.natAbs := by
    rw [← Int.natAbs_natCast P, Int.natAbs_dvd_natAbs]
    exact hdvd
  have hP_le : P ≤ d.natAbs := Nat.le_of_dvd hnatpos hnatdvd
  have hP_real : (P : ℝ) ≤ |(d : ℝ)| := by
    calc
      (P : ℝ) ≤ (d.natAbs : ℝ) := by exact_mod_cast hP_le
      _ = |(d : ℝ)| := by norm_num
  linarith

/-- If the product of the column moduli exceeds the cancellation-size bound,
the corresponding higher incidence minor vanishes. -/
theorem shiftedIncidenceMatrixInt_det_eq_zero_of_product_large
    {k : ℕ} (a n : Fin (k + 1) → ℕ)
    (u : Fin (k + 1) → Fin (k + 1) → ℕ) (X G : ℕ)
    (hnX : ∀ i, n i ≤ X) (huG : ∀ i j, u i j ≤ G)
    (hG : 0 < G) (hdiv : ∀ i j, a j ∣ n i + u i j)
    (hlarge : (k + 1).factorial * (X + G) * G ^ k < ∏ j, a j) :
    (shiftedIncidenceMatrixInt n u).det = 0 := by
  let d : ℤ := (shiftedIncidenceMatrixInt n u).det
  let B : ℕ := (k + 1).factorial * (X + G) * G ^ k
  let P : ℕ := ∏ j, a j
  have hdvd : (P : ℤ) ∣ d := by
    dsimp [P, d]
    exact int_prod_moduli_dvd_shiftedIncidenceMatrix_det a n u hdiv
  have hboundR : |(d : ℝ)| ≤ (B : ℝ) := by
    have h := abs_det_shiftedIncidenceMatrix_le
      (fun i => (n i : ℝ)) (fun i j => (u i j : ℝ))
      (X : ℝ) (G : ℝ)
      (fun _ => by positivity) (fun i => by exact_mod_cast hnX i)
      (fun _ _ => by positivity) (fun i j => by exact_mod_cast huG i j)
      (by exact_mod_cast hG)
    have hdetcast :
        (d : ℝ) =
          (shiftedIncidenceMatrix (fun i => (n i : ℝ))
            (fun i j => (u i j : ℝ))).det := by
      dsimp [d]
      rw [Int.cast_det]
      congr 1
      ext i j
      simp [shiftedIncidenceMatrixInt, shiftedIncidenceMatrix]
    rw [hdetcast]
    dsimp [B]
    norm_cast at h ⊢
  apply int_eq_zero_of_dvd_of_real_abs_lt P d hdvd
  have hBP : B < P := by
    simpa [B, P] using hlarge
  have hBP_real : (B : ℝ) < (P : ℝ) := by exact_mod_cast hBP
  exact lt_of_le_of_lt hboundR hBP_real

end Erdos489
