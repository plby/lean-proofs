import Wikipedia.HomotopyGroupsOfSpheres.CliffordBoundaryComplexStructure
import Wikipedia.HomotopyGroupsOfSpheres.RankSixSpinorScaling
import Wikipedia.HomotopyGroupsOfSpheres.RankSixSpinorProjection

/-! # The actual complex two-plane and Hopf projection of the boundary complex structures -/

noncomputable section

open scoped Matrix Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.CliffordBoundaryBott

open NoExoticSixSphere NoExoticSixSphere.RankSixSkewMatrix
open NoExoticSixSphere.RankSixComplexProjection

abbrev PairSpace := EuclideanSpace ℂ (Fin 2)
abbrev UnitPair := Metric.sphere (0 : PairSpace) 1

theorem unitPair_norm (q : UnitPair) : ‖q.val‖ = 1 := mem_sphere_zero_iff_norm.mp q.property

theorem unitPair_normSq (q : UnitPair) :
    Complex.normSq (q.val 0) + Complex.normSq (q.val 1) = 1 := by
  calc
    _ = ‖q.val‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp [Fin.sum_univ_succ, Complex.sq_norm]
    _ = 1 := by rw [unitPair_norm]; norm_num

def hopfCoordinates (q : Fin 2 → ℂ) : Fin 3 → ℝ :=
  ![2 * (q 0 * star (q 1)).re, Complex.normSq (q 0) - Complex.normSq (q 1),
    -2 * (q 0 * star (q 1)).im]

theorem hopfCoordinates_sq (q : Fin 2 → ℂ) :
    ∑ i, hopfCoordinates q i ^ 2 = (Complex.normSq (q 0) + Complex.normSq (q 1)) ^ 2 := by
  norm_num [hopfCoordinates, Fin.sum_univ_succ, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im]
  ring

def hopfMap : C(UnitPair, Sphere 2) where
  toFun q := ⟨WithLp.toLp 2 (hopfCoordinates q.val), mem_sphere_zero_iff_norm.mpr (by
    have h : ‖WithLp.toLp 2 (hopfCoordinates q.val)‖ ^ 2 = 1 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      change ∑ i, hopfCoordinates q.val i ^ 2 = 1
      rw [hopfCoordinates_sq, unitPair_normSq, one_pow]
    nlinarith [norm_nonneg (WithLp.toLp 2 (hopfCoordinates q.val))])⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 ↦ ℝ)).comp
    apply continuous_pi
    intro i
    fin_cases i <;> simp only [hopfCoordinates] <;> fun_prop

def unscaledPairVector (q : PairSpace) : Spinor :=
  WithLp.toLp 2 ![q 0, q 0, q 1, -q 1]

theorem unscaledPairVector_norm_sq (q : PairSpace) :
    ‖unscaledPairVector q‖ ^ 2 = 2 * ‖q‖ ^ 2 := by
  simp [unscaledPairVector, EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]
  ring

def planeCoefficient : ℝ := Real.sqrt (1 / 2)

theorem planeCoefficient_sq : planeCoefficient ^ 2 = 1 / 2 :=
  Real.sq_sqrt (by norm_num)

def spinorPlaneMap : C(UnitPair, UnitSpinor) where
  toFun q := ⟨planeCoefficient • unscaledPairVector q.val, mem_sphere_zero_iff_norm.mpr (by
    have h : ‖planeCoefficient • unscaledPairVector q.val‖ ^ 2 = 1 := by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, planeCoefficient_sq,
        unscaledPairVector_norm_sq, unitPair_norm]
      norm_num
    nlinarith [norm_nonneg (planeCoefficient • unscaledPairVector q.val)])⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    have h : Continuous (fun q : UnitPair ↦ unscaledPairVector q.val) := by
      apply (PiLp.continuous_toLp 2 (fun _ : Fin 4 ↦ ℂ)).comp
      apply continuous_pi
      intro i
      fin_cases i <;> fun_prop
    exact h.const_smul planeCoefficient

theorem spinorMatrix_pair_row0 (q : UnitPair) (j : Fin 6) :
    spinorMatrix ![q.val 0, q.val 0, q.val 1, -q.val 1] 0 j =
      ((2 : ℝ) • realGenerator (hopfCoordinates q.val)) 0 j := by
  have hq := unitPair_normSq q
  simp only [Complex.normSq_apply] at hq
  fin_cases j <;>
    norm_num [spinorMatrix, skew, realGenerator, hopfCoordinates,
      Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, vecCons_five]
  nlinarith [hq]

theorem spinorMatrix_pair_row1 (q : UnitPair) (j : Fin 6) :
    spinorMatrix ![q.val 0, q.val 0, q.val 1, -q.val 1] 1 j =
      ((2 : ℝ) • realGenerator (hopfCoordinates q.val)) 1 j := by
  have hq := unitPair_normSq q
  simp only [Complex.normSq_apply] at hq
  fin_cases j <;>
    norm_num [spinorMatrix, skew, realGenerator, hopfCoordinates,
      Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, vecCons_five] <;>
      nlinarith [hq]

theorem spinorMatrix_pair_row2 (q : UnitPair) (j : Fin 6) :
    spinorMatrix ![q.val 0, q.val 0, q.val 1, -q.val 1] 2 j =
      ((2 : ℝ) • realGenerator (hopfCoordinates q.val)) 2 j := by
  have hq := unitPair_normSq q
  simp only [Complex.normSq_apply] at hq
  fin_cases j <;>
    norm_num [spinorMatrix, skew, realGenerator, hopfCoordinates,
      Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, vecCons_five] <;>
      nlinarith [hq]

theorem spinorMatrix_pair_row3 (q : UnitPair) (j : Fin 6) :
    spinorMatrix ![q.val 0, q.val 0, q.val 1, -q.val 1] 3 j =
      ((2 : ℝ) • realGenerator (hopfCoordinates q.val)) 3 j := by
  have hq := unitPair_normSq q
  simp only [Complex.normSq_apply] at hq
  fin_cases j <;>
    norm_num [spinorMatrix, skew, realGenerator, hopfCoordinates,
      Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, vecCons_five]
  nlinarith [hq]

theorem spinorMatrix_pair_row4 (q : UnitPair) (j : Fin 6) :
    spinorMatrix ![q.val 0, q.val 0, q.val 1, -q.val 1] 4 j =
      ((2 : ℝ) • realGenerator (hopfCoordinates q.val)) 4 j := by
  have hq := unitPair_normSq q
  simp only [Complex.normSq_apply] at hq
  fin_cases j <;>
    norm_num [spinorMatrix, skew, realGenerator, hopfCoordinates,
      Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, vecCons_five] <;>
      nlinarith [hq]

theorem spinorMatrix_pair_row5 (q : UnitPair) (j : Fin 6) :
    spinorMatrix ![q.val 0, q.val 0, q.val 1, -q.val 1] 5 j =
      ((2 : ℝ) • realGenerator (hopfCoordinates q.val)) 5 j := by
  have hq := unitPair_normSq q
  simp only [Complex.normSq_apply] at hq
  fin_cases j <;>
    norm_num [spinorMatrix, skew, realGenerator, hopfCoordinates,
      Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, vecCons_five] <;>
      nlinarith [hq]

theorem spinorMatrix_pair (q : UnitPair) :
    spinorMatrix ![q.val 0, q.val 0, q.val 1, -q.val 1] =
      (2 : ℝ) • realGenerator (hopfCoordinates q.val) := by
  apply Matrix.ext
  intro i j
  fin_cases i
  · exact spinorMatrix_pair_row0 q j
  · exact spinorMatrix_pair_row1 q j
  · exact spinorMatrix_pair_row2 q j
  · exact spinorMatrix_pair_row3 q j
  · exact spinorMatrix_pair_row4 q j
  · exact spinorMatrix_pair_row5 q j

theorem fromSpinor_plane (q : UnitPair) :
    fromSpinor (spinorPlaneMap q) = structureMap (hopfMap q) := by
  apply matrix_injective
  rw [matrix_fromSpinor, structureMap_matrix]
  change spinorMatrix (fun i ↦ planeCoefficient •
    (![q.val 0, q.val 0, q.val 1, -q.val 1] : Fin 4 → ℂ) i) =
      realGenerator (hopfCoordinates q.val)
  rw [spinorMatrix_real_smul, planeCoefficient_sq, spinorMatrix_pair, smul_smul]
  norm_num

def pairPole : UnitPair :=
  ⟨EuclideanSpace.basisFun (Fin 2) ℂ 0, mem_sphere_zero_iff_norm.mpr
    ((EuclideanSpace.basisFun (Fin 2) ℂ).orthonormal.1 0)⟩

theorem hopfMap_pairPole : hopfMap pairPole = structurePole := by
  apply Subtype.ext
  apply PiLp.ext
  intro i
  fin_cases i <;> norm_num [hopfMap, hopfCoordinates, pairPole, structurePole,
    EuclideanSpace.basisFun_apply, Complex.normSq_apply]

end Wikipedia.HomotopyGroupsOfSpheres.CliffordBoundaryBott
