import ErdosProblems.Erdos1148.NormalizedAction
import ErdosProblems.Erdos1148.IsotropicDirections
import ErdosProblems.Erdos1148.PairStabilizer

/-!
# Representing special isometries by two-by-two matrices

For the split discriminant form, the normalized change-of-variables action
accounts for every special isometry over a characteristic-zero field. The
proof uses its action on two isotropic directions and the trivial stabilizer.
-/

namespace Erdos1148.DukeArithmetic

def directionRoot {K : Type*} [Field K] : Option K → K × K
  | none => (0, 1)
  | some x => (1, x)

lemma isotropicDirection_eq_root {K : Type*} [Field K] (x : Option K) :
    isotropicDirection x =
      ((directionRoot x).1 ^ 2, 2 * (directionRoot x).1 * (directionRoot x).2,
        (directionRoot x).2 ^ 2) := by
  cases x <;> simp [isotropicDirection, directionRoot]

def directionDet {K : Type*} [Field K] (x y : Option K) : K :=
  (directionRoot x).1 * (directionRoot y).2 - (directionRoot x).2 * (directionRoot y).1

lemma pairing_directionDet {K : Type*} [Field K] (x y : Option K) :
    pairing (isotropicDirection x) (isotropicDirection y) = -4 * directionDet x y ^ 2 := by
  rw [isotropicDirection_eq_root x, isotropicDirection_eq_root y]
  dsimp [pairing, directionDet]
  ring

def matrixOfDirections {K : Type*} [Field K] (a : K) (x y : Option K) :
    Matrix (Fin 2) (Fin 2) K :=
  !![a * directionDet x y * (directionRoot x).1, a * directionDet x y * (directionRoot x).2;
     (directionRoot y).1, (directionRoot y).2]

lemma det_matrixOfDirections {K : Type*} [Field K] (a : K) (x y : Option K) :
    (matrixOfDirections a x y).det = a * directionDet x y ^ 2 := by
  simp [matrixOfDirections, Matrix.det_fin_two, directionDet]
  ring

lemma transform_matrixOfDirections_first {K : Type*} [Field K] (a : K) (x y : Option K) :
    transform (matrixOfDirections a x y) (1, 0, 0) =
      (a * directionDet x y) ^ 2 • isotropicDirection x := by
  rw [isotropicDirection_eq_root]
  ext <;> simp [transform, matrixOfDirections] <;> ring

lemma transform_matrixOfDirections_second {K : Type*} [Field K] (a : K) (x y : Option K) :
    transform (matrixOfDirections a x y) (0, 0, 1) = isotropicDirection y := by
  rw [isotropicDirection_eq_root]
  ext <;> simp [transform, matrixOfDirections]

/-- The special orthogonal action on this split ternary form comes from `PGL₂`. -/
theorem exists_normalizedTransformIsometry {K : Type*} [Field K] [CharZero K]
    (g : specialDiscrGroup K) :
    ∃ (M : Matrix (Fin 2) (Fin 2) K) (hM : M.det ≠ 0), normalizedTransformIsometry M hM = g := by
  have ht : discr (g.1 (1, 0, 0)) = 0 := by simpa [discr] using g.2.1 (1, 0, 0)
  have hu : discr (g.1 (0, 0, 1)) = 0 := by simpa [discr] using g.2.1 (0, 0, 1)
  have ht0 : g.1 (1, 0, 0) ≠ 0 := by simp
  have hu0 : g.1 (0, 0, 1) ≠ 0 := by simp
  obtain ⟨a, ha, x, hx⟩ := exists_isotropicDirection (by norm_num : (2 : K) ≠ 0) ht ht0
  obtain ⟨b, _, y, hy⟩ := exists_isotropicDirection (by norm_num : (2 : K) ≠ 0) hu hu0
  have hpair : pairing (g.1 (1, 0, 0)) (g.1 (0, 0, 1)) = -4 := by
    simpa [pairing] using pairing_linearEquiv g.1 g.2.1 (1, 0, 0) (0, 0, 1)
  rw [hx, hy, pairing_smul_smul, pairing_directionDet] at hpair
  have hscalar : a * b * directionDet x y ^ 2 = 1 := by
    apply mul_left_cancel₀ (by norm_num : (-4 : K) ≠ 0)
    linear_combination hpair
  have hD : directionDet x y ≠ 0 := by
    intro hz
    simp [hz] at hscalar
  have hdet : (matrixOfDirections a x y).det ≠ 0 := by
    rw [det_matrixOfDirections]
    exact mul_ne_zero ha (pow_ne_zero 2 hD)
  have hinv : (a * directionDet x y ^ 2)⁻¹ = b := by
    apply mul_left_cancel₀ (mul_ne_zero ha (pow_ne_zero 2 hD))
    rw [mul_inv_cancel₀ (mul_ne_zero ha (pow_ne_zero 2 hD))]
    linear_combination -hscalar
  refine ⟨matrixOfDirections a x y, hdet, ?_⟩
  let pair : FormPair K 0 (-4) := ⟨((1, 0, 0), (0, 0, 1)), by simp [discr, pairing]⟩
  apply specialDiscrGroup_ext_of_pair pair (by norm_num)
  · change (normalizedTransformIsometry (matrixOfDirections a x y) hdet).1 (1, 0, 0) = _
    rw [normalizedTransformIsometry_apply, transform_matrixOfDirections_first,
      det_matrixOfDirections, hinv, hx, smul_smul]
    congr 1
    linear_combination a * hscalar
  · change (normalizedTransformIsometry (matrixOfDirections a x y) hdet).1 (0, 0, 1) = _
    rw [normalizedTransformIsometry_apply, transform_matrixOfDirections_second,
      det_matrixOfDirections, hinv, hy]

end Erdos1148.DukeArithmetic
