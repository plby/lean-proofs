import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicMidpointParameterDerivative

/-! # The full first-column derivative at a midpoint target -/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix

open QuaternionicComplexPlane QuaternionicSymmetricMatrices QuaternionicScalars

local notation "ℍ" => Quaternion ℝ

def targetComplexColumn : Fin 2 → ℂ := ![targetAlpha, targetBeta]

def midpointColumnVariation (w : ℂ) (u : unitary ℂ)
    (D : Matrix (Fin 3) (Fin 3) ℂ) (r : Fin 2) : ℍ :=
  normalizedSchurVariation 0 (embed (u.val * targetComplexColumn r)) (embed u.val)
    (midpointRotationVariation w D (remainingRow r) 1)
    (midpointRotationVariation w D (remainingRow r) 0)
    (midpointRotationVariation w D 1 0)
    (midpointRotationVariation w D 1 1) (embed (w + star w))

theorem hasDerivAt_firstColumn_midpoint (s t : ℝ → ℝ) (B : ℝ → Space (Fin 3))
    (a b x : ℝ) (D : Matrix (Fin 3) (Fin 3) ℂ)
    (hs : HasDerivAt s a x) (ht : HasDerivAt t b x)
    (hB : ∀ r q, HasDerivAt (fun y ↦ (B y).val.val r q) (D r q) x)
    (hsx : s x = Real.pi / 2) (htx : t x = Real.pi / 2)
    (u : unitary ℂ) (hBx : (B x).val.val = u.val • targetMatrix targetAlpha targetBeta)
    (r : Fin 2) : HasDerivAt (fun y ↦ firstColumnFormula (s y) (t y) (B y) r)
      (midpointColumnVariation (angularVelocity a b) u D r) x := by
  have hA := hasDerivAt_rotation_entry_midpoint s t B a b x D hs ht hB hsx htx
  have hbase (i j : Fin 3) :
      (rotation (s x) (t x) (B x)).val i j =
        embed ((u.val • targetMatrix targetAlpha targetBeta) i j) := by
    rw [hsx, htx, rotation_midpoint_entry, hBx]
  have hz : (rotation (s x) (t x) (B x)).val 1 0 = 0 := by
    rw [hbase]
    simp [targetMatrix, embed]
  have hp : (rotation (s x) (t x) (B x)).val (remainingRow r) 1 = 0 := by
    rw [hbase]
    fin_cases r <;> simp [targetMatrix, remainingRow, embed, Matrix.cons_val_two]
  have hq : (rotation (s x) (t x) (B x)).val (remainingRow r) 0 =
      embed (u.val * targetComplexColumn r) := by
    rw [hbase]
    fin_cases r <;> simp [targetMatrix, remainingRow, targetComplexColumn, Matrix.cons_val_two]
  have hy : (rotation (s x) (t x) (B x)).val 1 1 = embed u.val := by
    rw [hbase]
    simp [targetMatrix]
  have hnorm : star (-(scalarRotation (s x) (t x) * scalarRotation (s x) (t x))) = 1 := by
    rw [hsx, htx, midpoint_reference, j_mul_j, neg_neg, star_one]
  have he := hasDerivAt_normalizedSchur
    (fun y ↦ (rotation (s y) (t y) (B y)).val (remainingRow r) 1)
    (fun y ↦ (rotation (s y) (t y) (B y)).val (remainingRow r) 0)
    (fun y ↦ (rotation (s y) (t y) (B y)).val 1 0)
    (fun y ↦ (rotation (s y) (t y) (B y)).val 1 1)
    (fun y ↦ star (-(scalarRotation (s y) (t y) * scalarRotation (s y) (t y))))
    _ _ _ _ _ x (hA _ _) (hA _ _) (hA _ _) (hA _ _)
    (hasDerivAt_referenceNormalization_midpoint s t a b x hs ht hsx htx) hz hnorm
  rw [hp, hq, hy] at he
  exact he

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix
