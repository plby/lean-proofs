/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos407.MinkowskiSecondBoxBasis

/-!
# Coordinate quotient glue for the box form of Minkowski's second theorem

This file records the compatibility of an integral combination of the tail
columns of a matrix with the coordinate quotient used in
`MinkowskiSecondBox`.
-/

namespace Erdos407.MinkowskiSecondBox

open scoped BigOperators Matrix
open Erdos407.AdelicMinkowski Set Module Submodule

/-- The lift to the original space of an integral vector in the tail-column
coordinates.  Its first coordinate in the matrix basis is zero. -/
def rawTailLift {n : ℕ} (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (z : Fin n → ℤ) : Fin (n + 1) → ℝ :=
  Matrix.mulVec B (Fin.cons 0 (intCastVec z))

/-- Taking the coordinate quotient of a raw tail lift is multiplication by
the projected tail matrix. -/
theorem deleteProjection_rawTailLift {n : ℕ} (h : Fin (n + 1))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (z : Fin n → ℤ) :
    deleteProjection h (fun i ↦ B i 0) (rawTailLift B z) =
      Matrix.mulVec (projectedTail h B) (intCastVec z) := by
  funext i
  simp only [deleteProjection, rawTailLift, Matrix.mulVec, dotProduct,
    projectedTail]
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, mul_zero,
    zero_add]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  congr 1
  simp only [div_eq_mul_inv]
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The basis of `ℝ^n` whose columns are those of a nonsingular matrix. -/
noncomputable def matrixBasis {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ)
    (hD : D.det ≠ 0) : Module.Basis (Fin n) ℝ (Fin n → ℝ) :=
  (Pi.basisFun ℝ (Fin n)).map
    (D.toLinearEquiv' (D.invertibleOfIsUnitDet (isUnit_iff_ne_zero.mpr hD)))

@[simp] theorem matrixBasis_apply {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ)
    (hD : D.det ≠ 0) (j : Fin n) :
    matrixBasis D hD j = fun i ↦ D i j := by
  ext i
  rw [matrixBasis, Module.Basis.map_apply, Pi.basisFun_apply]
  change Matrix.mulVec D (Pi.single j 1) i = D i j
  simp [Matrix.mulVec]

/-- Every integral combination of the columns of a nonsingular matrix lies
in the integral span of its column basis. -/
theorem matrix_mulVec_intCastVec_mem_span {n : ℕ}
    (D : Matrix (Fin n) (Fin n) ℝ) (hD : D.det ≠ 0)
    (z : Fin n → ℤ) :
    Matrix.mulVec D (intCastVec z) ∈
      Submodule.span ℤ (Set.range (matrixBasis D hD)) := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine ⟨z, ?_⟩
  ext i
  simp [Matrix.mulVec, dotProduct, intCastVec, mul_comm]

/-! ## Induction for the unit cube -/

theorem minkowskiSecondConstant_succ (n : ℕ) :
    minkowskiSecondConstant (n + 1) =
      (2 : ℝ) ^ n * minkowskiSecondConstant n := by
  unfold minkowskiSecondConstant
  have he : (n + 1) * ((n + 1) - 1) / 2 = n + n * (n - 1) / 2 := by
    rw [← Nat.choose_two_right, ← Nat.choose_two_right]
    simp [Nat.choose_succ_succ]
  rw [he, pow_add]

theorem exists_abs_apply_eq_norm {n : ℕ} (x : Fin (n + 1) → ℝ) :
    ∃ h, |x h| = ‖x‖ := by
  classical
  obtain ⟨h, -, hh⟩ := Finset.exists_max_image Finset.univ (fun i => |x i|)
    Finset.univ_nonempty
  refine ⟨h, le_antisymm (abs_apply_le_norm x h) ?_⟩
  rw [pi_norm_le_iff_of_nonneg (abs_nonneg (x h))]
  intro i
  simpa only [Real.norm_eq_abs] using hh i (Finset.mem_univ i)

theorem realBox_smul_one_eq_const {n : ℕ} (s : ℝ) :
    realBox (s • (fun _ : Fin n ↦ (1 : ℝ))) = realBox (fun _ ↦ s) := by
  congr 1
  funext i
  simp

/-- The upper half of Minkowski's second theorem for a full lattice and the
unit coordinate cube.  The factor is `2^(n(n-1)/2)`. -/
theorem cube_has_successiveProductCertificate :
    ∀ {n : ℕ} (b : Basis (Fin n) ℝ (Fin n → ℝ)),
      Nonempty (SuccessiveProductCertificate
        (span ℤ (Set.range b)).toAddSubgroup (fun _ ↦ 1)
        (minkowskiSecondConstant n * |(Matrix.of b).det|)) := by
  intro n
  induction n with
  | zero =>
      intro b
      refine ⟨{
        scale := fun i ↦ Fin.elim0 i
        point := fun i ↦ Fin.elim0 i
        scale_nonneg := fun i ↦ Fin.elim0 i
        point_mem := fun i ↦ Fin.elim0 i
        independent := linearIndependent_empty_type
        mem_scaledBox := fun i ↦ Fin.elim0 i
        product_le := ?_ }⟩
      simp [minkowskiSecondConstant]
  | succ n ih =>
      intro b
      classical
      let L : Submodule ℤ (Fin (n + 1) → ℝ) := span ℤ (Set.range b)
      obtain ⟨v, hvL, hv0, hvmin⟩ := exists_shortest_nonzero_of_basis b
      let vL : L := ⟨v, hvL⟩
      have hvL0 : vL ≠ 0 := by
        intro h
        apply hv0
        exact congrArg Subtype.val h
      have hμpos : ∀ x : L, x ≠ 0 → 0 < ‖(x : Fin (n + 1) → ℝ)‖ := by
        intro x hx
        exact norm_pos_iff.mpr (by
          intro h
          apply hx
          exact Subtype.ext h)
      have hμhom : ∀ (c : ℤ), 0 < c → ∀ x : L,
          ‖((c • x : L) : Fin (n + 1) → ℝ)‖ =
            (c : ℝ) * ‖(x : Fin (n + 1) → ℝ)‖ := by
        intro c hc x
        have hcast : (((c • x : L) : Fin (n + 1) → ℝ)) =
            (c : ℝ) • (x : Fin (n + 1) → ℝ) := by
          ext i
          simp
        rw [hcast]
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos]
        exact_mod_cast hc
      have hμmin : ∀ x : L, x ≠ 0 →
          ‖(vL : Fin (n + 1) → ℝ)‖ ≤ ‖(x : Fin (n + 1) → ℝ)‖ := by
        intro x hx
        exact hvmin x x.property (by
          intro h
          apply hx
          exact Subtype.ext h)
      obtain ⟨-, Bz, hBz0⟩ :=
        Erdos407.PrimitiveExtension.shortest_zspan_vector_primitive_and_extends
          (Nat.succ_pos n) b vL hvL0
          (fun x : L ↦ ‖(x : Fin (n + 1) → ℝ)‖) hμpos hμhom hμmin
      let b' : Basis (Fin (n + 1)) ℝ (Fin (n + 1) → ℝ) :=
        Bz.ofZLatticeBasis ℝ L
      have hb'0 : b' 0 = v := by
        rw [show b' 0 = ((Bz 0 : L) : Fin (n + 1) → ℝ) by
          exact Basis.ofZLatticeBasis_apply ℝ L Bz 0]
        exact congrArg Subtype.val (by simpa using hBz0)
      have hb'span : span ℤ (Set.range b') = L := by
        exact Bz.ofZLatticeBasis_span ℝ L
      let M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := (Matrix.of b')ᵀ
      have hMdet : M.det ≠ 0 := by
        have hbdet : (Pi.basisFun ℝ (Fin (n + 1))).det b' ≠ 0 :=
          (AlternatingMap.map_basis_ne_zero_iff b'
            (Pi.basisFun ℝ (Fin (n + 1))).det).mpr
              (Pi.basisFun ℝ (Fin (n + 1))).det_ne_zero
        rw [Pi.basisFun_det_apply] at hbdet
        simpa [M] using hbdet
      obtain ⟨h, hh⟩ := exists_abs_apply_eq_norm v
      have hvh : v h ≠ 0 := by
        intro hz
        have : ‖v‖ = 0 := by simpa [hz] using hh.symm
        exact hv0 (norm_eq_zero.mp this)
      have hMh0 : M h 0 ≠ 0 := by
        simpa [M, Matrix.of_apply, hb'0] using hvh
      let Q : Matrix (Fin n) (Fin n) ℝ := projectedTail h M
      have hQdet : Q.det ≠ 0 := projectedTail_det_ne_zero h M hMdet hMh0
      let qB : Basis (Fin n) ℝ (Fin n → ℝ) := projectedTailBasis h M hMdet hMh0
      obtain ⟨cq⟩ := ih qB
      have hQpoint : ∀ j, ∃ z : Fin n → ℤ,
          Matrix.mulVec Q (intCastVec z) = cq.point j := by
        intro j
        have hm := cq.point_mem j
        change cq.point j ∈ span ℤ (Set.range qB) at hm
        rw [Submodule.mem_span_range_iff_exists_fun] at hm
        obtain ⟨z, hz⟩ := hm
        refine ⟨z, ?_⟩
        rw [← hz]
        ext i
        simp [Q, qB, Matrix.mulVec, dotProduct, intCastVec, mul_comm]
      choose z hz using hQpoint
      let raw : Fin n → Fin (n + 1) → ℝ := fun j ↦ rawTailLift M (z j)
      let a : Fin n → ℤ := fun j ↦ -roundedCoefficient (raw j h / v h)
      let lift : Fin n → Fin (n + 1) → ℝ :=
        fun j ↦ raw j + (a j) • v
      let scale : Fin (n + 1) → ℝ := Fin.cons ‖v‖ (fun j ↦ 2 * cq.scale j)
      let point : Fin (n + 1) → Fin (n + 1) → ℝ := Fin.cons v lift
      have hraw_eq : ∀ j, raw j = ∑ k, (z j k) • b' k.succ := by
        intro j
        ext i
        simp [raw, rawTailLift, M, Matrix.mulVec, dotProduct, intCastVec,
          Fin.sum_univ_succ, mul_comm]
      have hrawL : ∀ j, raw j ∈ L := by
        intro j
        rw [hraw_eq]
        rw [← hb'span]
        apply sum_mem
        intro k hk
        exact smul_mem _ _ (subset_span (Set.mem_range_self k.succ))
      have hliftL : ∀ j, lift j ∈ L := by
        intro j
        change raw j + (a j) • v ∈ L
        exact add_mem (hrawL j) (smul_mem L (a j) hvL)
      have hcol0 : (fun i ↦ M i 0) = v := by
        funext i
        simp [M, Matrix.of_apply, hb'0]
      have hproj_raw : ∀ j, deleteProjection h v (raw j) = cq.point j := by
        intro j
        rw [← hcol0]
        rw [deleteProjection_rawTailLift]
        exact hz j
      have hproj_lift : ∀ j, deleteProjection h v (lift j) = cq.point j := by
        intro j
        change deleteProjection h v (raw j + (a j) • v) = cq.point j
        have hcast : (a j) • v = (a j : ℝ) • v := by
          ext i
          simp
        rw [hcast, deleteProjection_add_smul h v (raw j) (a j : ℝ) hvh]
        exact hproj_raw j
      have hqnorm : ∀ j, ‖cq.point j‖ ≤ cq.scale j := by
        intro j
        apply (mem_realBox_const_iff_norm_le (cq.scale_nonneg j) _).mp
        rw [← realBox_smul_one_eq_const]
        exact cq.mem_scaledBox j
      have ha : ∀ j, |raw j h / v h + (a j : ℝ)| ≤ (1 : ℝ) / 2 := by
        intro j
        simpa [a, sub_eq_add_neg] using
          abs_sub_roundedCoefficient_le_half (raw j h / v h)
      have hlift_upper : ∀ j, ‖lift j‖ ≤ cq.scale j + ‖v‖ / 2 := by
        intro j
        have hcast : (a j) • v = (a j : ℝ) • v := by
          ext i
          simp
        change ‖raw j + (a j) • v‖ ≤ cq.scale j + ‖v‖ / 2
        rw [hcast]
        exact reducedLift_apply_le h v (raw j) (cq.scale j) (a j : ℝ)
          hh hvh (ha j) ((congrArg norm (hproj_raw j)).le.trans (hqnorm j))
      have hlift0 : ∀ j, lift j ≠ 0 := by
        intro j hj
        apply cq.independent.ne_zero j
        rw [← hproj_lift j, hj]
        ext i
        simp [deleteProjection]
      have hshortlift : ∀ j, ‖v‖ ≤ ‖lift j‖ := by
        intro j
        exact hvmin (lift j) (hliftL j) (hlift0 j)
      have hliftnorm : ∀ j, ‖lift j‖ ≤ 2 * cq.scale j := by
        intro j
        have hu := hlift_upper j
        have hs := hshortlift j
        linarith
      have hind : LinearIndependent ℝ point := by
        rw [Fintype.linearIndependent_iff]
        intro g hg i
        have hprojrel : ∑ j, g j.succ • cq.point j = 0 := by
          have hm := congrArg (deleteProjectionLinear h v) hg
          rw [map_sum] at hm
          rw [Fin.sum_univ_succ] at hm
          simp only [point, Fin.cons_zero, Fin.cons_succ] at hm
          rw [map_smul, deleteProjectionLinear_apply,
            deleteProjection_self h v hvh, smul_zero, zero_add] at hm
          simp only [map_smul, deleteProjectionLinear_apply, map_zero] at hm
          simp_rw [hproj_lift] at hm
          exact hm
        have htail : ∀ j : Fin n, g j.succ = 0 :=
          (Fintype.linearIndependent_iff.mp cq.independent) _ hprojrel
        refine Fin.cases ?_ htail i
        rw [Fin.sum_univ_succ] at hg
        simp only [point, Fin.cons_zero, Fin.cons_succ] at hg
        simp_rw [htail] at hg
        simp only [zero_smul, Finset.sum_const_zero, add_zero] at hg
        exact (smul_eq_zero.mp hg).resolve_right hv0
      have hqdet : |(Matrix.of qB).det| = |Q.det| := by
        have hmat : Matrix.of qB = Qᵀ := by
          ext i j
          simp [qB, Q, Matrix.of_apply, Matrix.col]
        rw [hmat, Matrix.det_transpose]
      have hMabs : |M.det| = |(Matrix.of b).det| := by
        have hchange := abs_det_zspan_basis_eq b Bz
        have hmat : Matrix.of (((↑) : L → (Fin (n + 1) → ℝ)) ∘ Bz) =
            Matrix.of b' := by
          ext i j
          simp [b', Matrix.of_apply]
        rw [hmat] at hchange
        simpa [M] using hchange
      have hfactor : |(Matrix.of b).det| = ‖v‖ * |Q.det| := by
        rw [← hMabs]
        have hd := abs_det_eq_abs_pivot_mul_abs_det_projectedTail h M hMh0
        have hentry : M h 0 = v h := congrFun hcol0 h
        rw [hentry, hh] at hd
        simpa [Q] using hd
      refine ⟨{
        scale := scale
        point := point
        scale_nonneg := ?_
        point_mem := ?_
        independent := hind
        mem_scaledBox := ?_
        product_le := ?_ }⟩
      · intro i
        refine Fin.cases (norm_nonneg v) (fun j ↦ ?_) i
        exact mul_nonneg (by norm_num) (cq.scale_nonneg j)
      · intro i
        refine Fin.cases hvL (fun j ↦ hliftL j) i
      · intro i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · rw [realBox_smul_one_eq_const]
          apply (mem_realBox_const_iff_norm_le (norm_nonneg v) v).mpr
          simp
        · have hm := (mem_realBox_const_iff_norm_le
              (mul_nonneg (by norm_num) (cq.scale_nonneg j)) (lift j)).mpr
              (hliftnorm j)
          rw [realBox_smul_one_eq_const]
          simpa [scale, point] using hm
      · have hcq : ∏ j, cq.scale j ≤ minkowskiSecondConstant n * |Q.det| := by
          simpa [hqdet] using cq.product_le
        calc
          ∏ i, scale i = ‖v‖ * ((2 : ℝ) ^ n * ∏ j, cq.scale j) := by
            simp [scale, Fin.prod_univ_succ, Finset.prod_mul_distrib,
              Finset.prod_const]
          _ ≤ ‖v‖ * ((2 : ℝ) ^ n *
              (minkowskiSecondConstant n * |Q.det|)) := by
            gcongr
          _ = minkowskiSecondConstant (n + 1) * |(Matrix.of b).det| := by
            rw [minkowskiSecondConstant_succ, hfactor]
            ring

/-- A tail lift reduced by the nearest integral multiple of the first
column. -/
noncomputable def roundedTailLift {n : ℕ} (h : Fin (n + 1))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (z : Fin n → ℤ) :
    Fin (n + 1) → ℝ :=
  rawTailLift B z -
    (roundedCoefficient ((rawTailLift B z) h / B h 0) : ℝ) •
      (fun i ↦ B i 0)

/-- Rounding a raw lift does not change its coordinate quotient. -/
theorem deleteProjection_roundedTailLift {n : ℕ} (h : Fin (n + 1))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hB : B h 0 ≠ 0)
    (z : Fin n → ℤ) :
    deleteProjection h (fun i ↦ B i 0) (roundedTailLift h B z) =
      Matrix.mulVec (projectedTail h B) (intCastVec z) := by
  rw [roundedTailLift, sub_eq_add_neg, ← neg_smul]
  rw [deleteProjection_add_smul h (fun i ↦ B i 0) (rawTailLift B z)
    (-(roundedCoefficient ((rawTailLift B z) h / B h 0) : ℝ)) hB]
  exact deleteProjection_rawTailLift h B z

/-- A nearest-integer reduced lift has norm at most twice the norm of its
coordinate quotient, provided the first column is a shortest nonzero
lattice vector. -/
theorem roundedTailLift_norm_le_two {n : ℕ} (h : Fin (n + 1))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (z : Fin n → ℤ)
    (hh : |B h 0| = ‖(fun i ↦ B i 0)‖) (hB : B h 0 ≠ 0)
    (hshort : ‖(fun i ↦ B i 0)‖ ≤ ‖roundedTailLift h B z‖) :
    ‖roundedTailLift h B z‖ ≤
      2 * ‖Matrix.mulVec (projectedTail h B) (intCastVec z)‖ := by
  let x := rawTailLift B z
  let v : Fin (n + 1) → ℝ := fun i ↦ B i 0
  let a : ℝ := -(roundedCoefficient (x h / v h) : ℝ)
  have ha : |x h / v h + a| ≤ (1 : ℝ) / 2 := by
    change |x h / v h - (round (x h / v h) : ℝ)| ≤ (1 : ℝ) / 2
    simpa only [sub_eq_add_neg] using abs_sub_round (x h / v h)
  have hproj : ‖deleteProjection h v x‖ ≤
      ‖Matrix.mulVec (projectedTail h B) (intCastVec z)‖ := by
    rw [deleteProjection_rawTailLift]
  have hu := reducedLift_apply_le h v x
    ‖Matrix.mulVec (projectedTail h B) (intCastVec z)‖ a hh hB ha hproj
  have hlift : x + a • v = roundedTailLift h B z := by
    simp [x, v, a, roundedTailLift, sub_eq_add_neg]
  rw [hlift] at hu
  have hhalf : ‖(fun i ↦ B i 0)‖ / 2 ≤
      ‖Matrix.mulVec (projectedTail h B) (intCastVec z)‖ := by
    linarith
  linarith

/-- A raw tail lift belongs to every integral submodule containing all
columns of the matrix. -/
theorem rawTailLift_mem_of_columns_mem {n : ℕ}
    (L : Submodule ℤ (Fin (n + 1) → ℝ))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hcol : ∀ j, (fun i ↦ B i j) ∈ L) (z : Fin n → ℤ) :
    rawTailLift B z ∈ L := by
  have heq : rawTailLift B z =
      ∑ j : Fin n, z j • (fun i ↦ B i j.succ) := by
    ext i
    rw [rawTailLift, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, intCastVec, mul_zero, zero_add,
      Finset.sum_apply, Pi.smul_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_comm]
    simpa only [smul_eq_mul] using
      Int.cast_smul_eq_zsmul ℝ (z j) (B i j.succ)
  rw [heq]
  apply Submodule.sum_mem
  intro j _
  exact L.smul_mem (z j) (hcol j.succ)

/-- The rounded lift remains in the original integral lattice. -/
theorem roundedTailLift_mem_of_columns_mem {n : ℕ} (h : Fin (n + 1))
    (L : Submodule ℤ (Fin (n + 1) → ℝ))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hcol : ∀ j, (fun i ↦ B i j) ∈ L) (z : Fin n → ℤ) :
    roundedTailLift h B z ∈ L := by
  apply L.sub_mem (rawTailLift_mem_of_columns_mem L B hcol z)
  simpa only [Int.cast_smul_eq_zsmul] using
    L.smul_mem (roundedCoefficient ((rawTailLift B z) h / B h 0)) (hcol 0)

/-- If the quotient vectors are linearly independent, adjoining the first
column to their rounded lifts gives a linearly independent family upstairs. -/
theorem roundedTailLift_linearIndependent {n : ℕ} (h : Fin (n + 1))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hB : B h 0 ≠ 0)
    (z : Fin n → Fin n → ℤ)
    (hli : LinearIndependent ℝ (fun j ↦
      Matrix.mulVec (projectedTail h B) (intCastVec (z j)))) :
    LinearIndependent ℝ (Fin.cons (fun i ↦ B i 0)
      (fun j ↦ roundedTailLift h B (z j))) := by
  rw [Fintype.linearIndependent_iff] at hli ⊢
  intro c hc i
  have hp := congrArg (deleteProjectionLinear h (fun i ↦ B i 0)) hc
  simp only [map_sum, map_smul, map_zero] at hp
  rw [Fin.sum_univ_succ] at hp
  simp only [Fin.cons_zero, Fin.cons_succ,
    deleteProjectionLinear_apply] at hp
  rw [deleteProjection_self h (fun i ↦ B i 0) hB] at hp
  simp_rw [deleteProjection_roundedTailLift h B hB] at hp
  simp only [smul_zero, zero_add] at hp
  have htail : ∀ j : Fin n, c j.succ = 0 := by
    exact fun j ↦ hli (fun j ↦ c j.succ) hp j
  have hc' := hc
  rw [Fin.sum_univ_succ] at hc'
  simp only [Fin.cons_zero, Fin.cons_succ] at hc'
  simp_rw [htail, zero_smul] at hc'
  simp only [Finset.sum_const_zero, add_zero] at hc'
  have hc0 : c 0 = 0 := by
    have hh := congrFun hc' h
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hh
    exact (mul_eq_zero.mp hh).resolve_right hB
  exact Fin.cases hc0 htail i

end Erdos407.MinkowskiSecondBox

#print axioms Erdos407.MinkowskiSecondBox.deleteProjection_rawTailLift
#print axioms Erdos407.MinkowskiSecondBox.minkowskiSecondConstant_succ
#print axioms Erdos407.MinkowskiSecondBox.matrixBasis_apply
#print axioms Erdos407.MinkowskiSecondBox.matrix_mulVec_intCastVec_mem_span
#print axioms Erdos407.MinkowskiSecondBox.deleteProjection_roundedTailLift
#print axioms Erdos407.MinkowskiSecondBox.roundedTailLift_norm_le_two
#print axioms Erdos407.MinkowskiSecondBox.rawTailLift_mem_of_columns_mem
#print axioms Erdos407.MinkowskiSecondBox.roundedTailLift_mem_of_columns_mem
#print axioms Erdos407.MinkowskiSecondBox.roundedTailLift_linearIndependent
#print axioms Erdos407.MinkowskiSecondBox.cube_has_successiveProductCertificate
