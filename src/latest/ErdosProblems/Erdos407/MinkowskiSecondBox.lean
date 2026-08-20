/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos407.AdelicMinkowski
import ErdosProblems.Erdos407.PrimitiveExtension
import Mathlib.Algebra.Module.ZLattice.Covolume

/-!
# A non-sharp upper half of Minkowski's second theorem for boxes

This file proves the form of Minkowski's second theorem needed in the
three-place argument.  The proof is by dimension induction.  At each step a
shortest primitive lattice vector is made the first vector of an integral
basis, one coordinate on which its box norm is attained is deleted, and the
remaining lattice is projected along that vector.  Rounding the coefficient
of a lifted point costs at most one half of the shortest vector.  This gives
the harmless recurrence `C (n+1) = 2^n C n`.
-/

namespace Erdos407.MinkowskiSecondBox

open scoped BigOperators Matrix
open Erdos407.AdelicMinkowski Set Module Submodule

/-- The dimension-only loss in the coordinate-projection proof. -/
noncomputable def minkowskiSecondConstant (n : ℕ) : ℝ :=
  (2 : ℝ) ^ (n * (n - 1) / 2)

@[simp] theorem minkowskiSecondConstant_zero : minkowskiSecondConstant 0 = 1 := by
  simp [minkowskiSecondConstant]

@[simp] theorem minkowskiSecondConstant_one : minkowskiSecondConstant 1 = 1 := by
  simp [minkowskiSecondConstant]

theorem minkowskiSecondConstant_nonneg (n : ℕ) :
    0 ≤ minkowskiSecondConstant n := by
  exact pow_nonneg (by norm_num) _

/-- A full lattice has a shortest nonzero vector for the sup norm. -/
theorem exists_shortest_nonzero_of_basis {n : ℕ}
    (b : Basis (Fin (n + 1)) ℝ (Fin (n + 1) → ℝ)) :
    ∃ v : Fin (n + 1) → ℝ,
      v ∈ Submodule.span ℤ (Set.range b) ∧ v ≠ 0 ∧
        ∀ x ∈ Submodule.span ℤ (Set.range b), x ≠ 0 → ‖v‖ ≤ ‖x‖ := by
  classical
  let e : Fin (n + 1) := 0
  have hbe_mem : b e ∈ Submodule.span ℤ (Set.range b) :=
    Submodule.subset_span ⟨e, rfl⟩
  have hbe_ne : b e ≠ 0 := b.ne_zero e
  let S : Set (Fin (n + 1) → ℝ) :=
    Metric.closedBall 0 ‖b e‖ ∩ Submodule.span ℤ (Set.range b)
  have hSfin : S.Finite := by
    exact ZSpan.setFinite_inter b Metric.isBounded_closedBall
  let T : Set (Fin (n + 1) → ℝ) := {x ∈ S | x ≠ 0}
  have hTfin : T.Finite := hSfin.subset (by intro x hx; exact hx.1)
  have hbeS : b e ∈ S := by
    refine ⟨?_, hbe_mem⟩
    simp
  have hTne : T.Nonempty := ⟨b e, hbeS, hbe_ne⟩
  obtain ⟨v, hvT, hvmin⟩ := Set.exists_min_image T norm hTfin hTne
  refine ⟨v, hvT.1.2, hvT.2, ?_⟩
  intro x hxL hx0
  by_cases hxle : ‖x‖ ≤ ‖b e‖
  · exact hvmin x ⟨⟨by simpa [Metric.mem_closedBall] using hxle, hxL⟩, hx0⟩
  · have hvle : ‖v‖ ≤ ‖b e‖ := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hvT.1.1
    exact hvle.trans (le_of_not_ge hxle)

/-- Any integral basis of the same full lattice has the same absolute real
determinant. -/
theorem abs_det_zspan_basis_eq {n : ℕ}
    (b : Basis (Fin n) ℝ (Fin n → ℝ))
    (B : Basis (Fin n) ℤ (span ℤ (Set.range b))) :
    |(Matrix.of (((↑) : span ℤ (Set.range b) → (Fin n → ℝ)) ∘ B)).det| =
      |(Matrix.of b).det| := by
  let L : Submodule ℤ (Fin n → ℝ) := span ℤ (Set.range b)
  have hB := ZLattice.covolume_eq_det L B
  have hb := ZLattice.covolume_eq_det L
    (Erdos407.PrimitiveExtension.zspanBasis b)
  calc
    |(Matrix.of (((↑) : L → (Fin n → ℝ)) ∘ B)).det| =
        ZLattice.covolume L := hB.symm
    _ = |(Matrix.of (((↑) : L → (Fin n → ℝ)) ∘
        Erdos407.PrimitiveExtension.zspanBasis b)).det| := hb
    _ = |(Matrix.of b).det| := by
      congr 2
      ext i j
      simp [L]

/-- Cast an integral coordinate vector to a real coordinate vector. -/
def intCastVec {n : ℕ} (z : Fin n → ℤ) : Fin n → ℝ :=
  fun i ↦ (z i : ℝ)

@[simp] theorem intCastVec_zero {n : ℕ} :
    intCastVec (0 : Fin n → ℤ) = 0 := by
  funext i
  simp [intCastVec]

@[simp] theorem intCastVec_add {n : ℕ} (z w : Fin n → ℤ) :
    intCastVec (z + w) = intCastVec z + intCastVec w := by
  funext i
  simp [intCastVec]

@[simp] theorem intCastVec_smul {n : ℕ} (a : ℤ) (z : Fin n → ℤ) :
    intCastVec (a • z) = (a : ℝ) • intCastVec z := by
  funext i
  simp [intCastVec]

/-- The sup norm is membership in a symmetric unit coordinate box. -/
theorem mem_realBox_const_iff_norm_le {n : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (x : Fin n → ℝ) :
    x ∈ realBox (fun _ ↦ s) ↔ ‖x‖ ≤ s := by
  rw [pi_norm_le_iff_of_nonneg hs]
  constructor
  · intro hx i
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨hx.1 i, hx.2 i⟩
  · intro hx
    constructor <;> intro i
    · have hi := hx i
      rw [Real.norm_eq_abs, abs_le] at hi
      exact hi.1
    · have hi := hx i
      rw [Real.norm_eq_abs, abs_le] at hi
      exact hi.2

/-- Rounding a coefficient along a shortest vector loses at most a factor
two in the quotient norm.  This is the numerical heart of the induction. -/
theorem reducedLift_norm_le_two {n : ℕ} (v w : Fin n → ℝ) (a : ℝ)
    (ha : |a| ≤ (1 : ℝ) / 2) (hshort : ‖v‖ ≤ ‖w + a • v‖) :
    ‖w + a • v‖ ≤ 2 * ‖w‖ := by
  have htri : ‖w + a • v‖ ≤ ‖w‖ + |a| * ‖v‖ := by
    simpa [norm_smul, Real.norm_eq_abs] using norm_add_le w (a • v)
  have hav : |a| * ‖v‖ ≤ ((1 : ℝ) / 2) * ‖v‖ :=
    mul_le_mul_of_nonneg_right ha (norm_nonneg v)
  have hvw : ‖v‖ ≤ 2 * ‖w‖ := by linarith
  calc
    ‖w + a • v‖ ≤ ‖w‖ + |a| * ‖v‖ := htri
    _ ≤ ‖w‖ + ((1 : ℝ) / 2) * ‖v‖ := by linarith
    _ ≤ 2 * ‖w‖ := by linarith

theorem shortest_le_two_projection {n : ℕ} (v w : Fin n → ℝ) (a : ℝ)
    (ha : |a| ≤ (1 : ℝ) / 2) (hshort : ‖v‖ ≤ ‖w + a • v‖) :
    ‖v‖ ≤ 2 * ‖w‖ := by
  exact hshort.trans (reducedLift_norm_le_two v w a ha hshort)

/-- The rounding operation used when lifting a projected lattice point. -/
noncomputable def roundedCoefficient (a : ℝ) : ℤ := round a

theorem abs_sub_roundedCoefficient_le_half (a : ℝ) :
    |a - (roundedCoefficient a : ℝ)| ≤ (1 : ℝ) / 2 := by
  simpa [roundedCoefficient] using abs_sub_round a

/-- Delete the coordinate `h` after projecting along `v` to the hyperplane
whose `h`-coordinate is zero. -/
noncomputable def deleteProjection {n : ℕ} (h : Fin (n + 1))
    (v x : Fin (n + 1) → ℝ) : Fin n → ℝ :=
  fun i ↦ x (h.succAbove i) - (x h / v h) * v (h.succAbove i)

/-- `deleteProjection` bundled as a real linear map in its point argument. -/
noncomputable def deleteProjectionLinear {n : ℕ} (h : Fin (n + 1))
    (v : Fin (n + 1) → ℝ) :
    (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun := deleteProjection h v
  map_add' x y := by
    funext i
    simp only [deleteProjection, Pi.add_apply]
    ring
  map_smul' a x := by
    funext i
    simp [deleteProjection]
    ring

@[simp] theorem deleteProjectionLinear_apply {n : ℕ} (h : Fin (n + 1))
    (v x : Fin (n + 1) → ℝ) :
    deleteProjectionLinear h v x = deleteProjection h v x := rfl

theorem deleteProjection_add_smul {n : ℕ} (h : Fin (n + 1))
    (v x : Fin (n + 1) → ℝ) (a : ℝ) (hvh : v h ≠ 0) :
    deleteProjection h v (x + a • v) = deleteProjection h v x := by
  funext i
  simp only [deleteProjection, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

theorem deleteProjection_self {n : ℕ} (h : Fin (n + 1))
    (v : Fin (n + 1) → ℝ) (hvh : v h ≠ 0) :
    deleteProjection h v v = 0 := by
  funext i
  simp [deleteProjection, hvh]

theorem abs_apply_le_norm {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    |x i| ≤ ‖x‖ := by
  have hi := (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mp (le_refl ‖x‖) i
  simpa only [Real.norm_eq_abs] using hi

/-- If `h` is a coordinate on which the sup norm of `v` is attained, then a
point whose deleted projection has norm at most `t` can be reduced modulo
`v` into the box of radius `t + ‖v‖/2`. -/
theorem reducedLift_apply_le {n : ℕ} (h : Fin (n + 1))
    (v x : Fin (n + 1) → ℝ) (t a : ℝ)
    (hh : |v h| = ‖v‖) (hvh : v h ≠ 0)
    (ha : |x h / v h + a| ≤ (1 : ℝ) / 2)
    (hx : ‖deleteProjection h v x‖ ≤ t) :
    ‖x + a • v‖ ≤ t + ‖v‖ / 2 := by
  have ht : 0 ≤ t := (norm_nonneg _).trans hx
  rw [pi_norm_le_iff_of_nonneg (add_nonneg ht (by positivity))]
  rw [h.forall_iff_succAbove]
  constructor
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs]
    have heq : x h + a * v h = (x h / v h + a) * v h := by
      field_simp
    rw [heq, abs_mul, hh]
    calc
      |x h / v h + a| * ‖v‖ ≤ ((1 : ℝ) / 2) * ‖v‖ :=
        mul_le_mul_of_nonneg_right ha (norm_nonneg v)
      _ ≤ t + ‖v‖ / 2 := by linarith
  · intro j
    have hproj : |deleteProjection h v x j| ≤ t := by
      simpa only [Real.norm_eq_abs] using
        (abs_apply_le_norm (deleteProjection h v x) j).trans hx
    have hv : |v (h.succAbove j)| ≤ ‖v‖ :=
      abs_apply_le_norm v (h.succAbove j)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs]
    have hdecomp : x (h.succAbove j) + a * v (h.succAbove j) =
        deleteProjection h v x j +
          (x h / v h + a) * v (h.succAbove j) := by
      rw [deleteProjection]
      ring
    rw [hdecomp]
    calc
      |deleteProjection h v x j + (x h / v h + a) * v (h.succAbove j)| ≤
          |deleteProjection h v x j| +
            |x h / v h + a| * |v (h.succAbove j)| := by
            simpa only [abs_mul] using
              abs_add_le (deleteProjection h v x j)
                ((x h / v h + a) * v (h.succAbove j))
      _ ≤ t + ((1 : ℝ) / 2) * ‖v‖ := by
        exact add_le_add hproj
          (mul_le_mul ha hv (abs_nonneg _) (by norm_num))
      _ = t + ‖v‖ / 2 := by ring

/-! ## The coordinate quotient determinant -/

/-- The elementary column shear which kills row `h` in every column except
the first one. -/
noncomputable def tailShear {n : ℕ} (h : Fin (n + 1))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i j ↦
    if j = 0 then (if i = 0 then 1 else 0)
    else if i = 0 then -(B h j / B h 0)
    else if i = j then 1 else 0

@[simp] theorem tailShear_apply_zero_zero {n : ℕ} (h : Fin (n + 1))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    tailShear h B 0 0 = 1 := by simp [tailShear]

@[simp] theorem tailShear_apply_succ_zero {n : ℕ} (h : Fin (n + 1))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i : Fin n) :
    tailShear h B i.succ 0 = 0 := by simp [tailShear]

@[simp] theorem tailShear_apply_zero_succ {n : ℕ} (h : Fin (n + 1))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (j : Fin n) :
    tailShear h B 0 j.succ = -(B h j.succ / B h 0) := by simp [tailShear]

@[simp] theorem tailShear_apply_succ_succ {n : ℕ} (h : Fin (n + 1))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i j : Fin n) :
    tailShear h B i.succ j.succ = if i = j then 1 else 0 := by
  simp [tailShear]

theorem tailShear_det {n : ℕ} (h : Fin (n + 1))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    (tailShear h B).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · apply Finset.prod_eq_one
    intro i _
    by_cases hi : i = 0
    · subst i
      simp [tailShear]
    · simp [tailShear, hi]
  · intro i j hji
    have hi0 : i ≠ 0 := by
      intro hi
      subst i
      exact (not_lt_of_ge (Fin.zero_le j)) hji
    have hij : i ≠ j := ne_of_gt hji
    simp [tailShear, hi0, hij]

/-- The projected tail matrix after deleting row `h`. -/
noncomputable def projectedTail {n : ℕ} (h : Fin (n + 1))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ B (h.succAbove i) j.succ -
    (B h j.succ / B h 0) * B (h.succAbove i) 0

theorem mul_tailShear_apply_zero {n : ℕ} (h : Fin (n + 1))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i : Fin (n + 1)) :
    (B * tailShear h B) i 0 = B i 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_succ, tailShear]

theorem mul_tailShear_apply_succ {n : ℕ} (h : Fin (n + 1))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i : Fin (n + 1))
    (j : Fin n) :
    (B * tailShear h B) i j.succ =
      B i j.succ - (B h j.succ / B h 0) * B i 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_succ, tailShear]
  ring

theorem mul_tailShear_pivot_succ {n : ℕ} (h : Fin (n + 1))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hB : B h 0 ≠ 0)
    (j : Fin n) :
    (B * tailShear h B) h j.succ = 0 := by
  rw [mul_tailShear_apply_succ]
  field_simp
  ring

theorem mul_tailShear_minor {n : ℕ} (h : Fin (n + 1))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    (B * tailShear h B).submatrix h.succAbove Fin.succ = projectedTail h B := by
  ext i j
  simp [projectedTail, mul_tailShear_apply_succ]

/-- Exact covolume factor for the coordinate quotient. -/
theorem abs_det_eq_abs_pivot_mul_abs_det_projectedTail {n : ℕ}
    (h : Fin (n + 1)) (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hB : B h 0 ≠ 0) :
    |B.det| = |B h 0| * |(projectedTail h B).det| := by
  have hdetC : (B * tailShear h B).det = B.det := by
    simp [Matrix.det_mul, tailShear_det]
  have hminor :
      (B * tailShear h B).submatrix h.succAbove (Fin.succAbove 0) =
        projectedTail h B := by
    simpa using mul_tailShear_minor h B
  have hLaplace := Matrix.det_succ_row (B * tailShear h B) h
  rw [Fin.sum_univ_succ] at hLaplace
  rw [mul_tailShear_apply_zero] at hLaplace
  simp_rw [mul_tailShear_pivot_succ h B hB] at hLaplace
  simp only [mul_zero, zero_mul, Finset.sum_const_zero, add_zero] at hLaplace
  rw [hdetC] at hLaplace
  rw [hminor] at hLaplace
  rw [hLaplace, abs_mul, abs_mul]
  simp only [abs_pow, abs_neg, abs_one, one_pow, one_mul]

end Erdos407.MinkowskiSecondBox

#print axioms Erdos407.MinkowskiSecondBox.reducedLift_norm_le_two
#print axioms Erdos407.MinkowskiSecondBox.deleteProjection_add_smul
