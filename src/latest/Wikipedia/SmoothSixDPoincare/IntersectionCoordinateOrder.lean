import Wikipedia.SmoothSixDPoincare.IntersectionBlockDeterminant

/-!
# The fixed coordinate order in the actual two-sheet determinant

The disk-first joint operator is conjugate to the actual tangent sum under
one fixed identification of its sheet product. Consequently their
determinants agree exactly, including the coordinate permutation signs.
-/

noncomputable section

namespace Wikipedia.SmoothSixDPoincare.IntersectionCoordinates

open PlaneImmersion (Plane)

variable {A B F : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The same disk-first rearrangement used in the native joint intersection operator. -/
def pairCoordinates (j : (A × B) ≃L[ℝ] F) :
    ((ℝ × A) × (ℝ × B)) ≃L[ℝ] (Plane × F) :=
  (ContinuousLinearEquiv.prodProdProdComm ℝ ℝ A ℝ B).trans
    (ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ Plane) j)

/-- The coordinate rearrangement contributes no unrecorded sign: the operators are conjugate. -/
theorem det_jointBlock_eq_tangentSum (j : (A × B) ≃L[ℝ] F)
    (P : (ℝ × A) →L[ℝ] (Plane × F)) (Q : (ℝ × B) →L[ℝ] (Plane × F)) :
    (jointBlock j P Q).det =
      ((pairCoordinates j).symm.toContinuousLinearMap.comp (P.coprod Q)).det := by
  let k := ContinuousLinearEquiv.prodProdProdComm ℝ ℝ A ℝ B
  let T := (pairCoordinates j).symm.toContinuousLinearMap.comp (P.coprod Q)
  have heq : (jointBlock j P Q).toLinearMap =
      k.toLinearEquiv.toLinearMap.comp (T.toLinearMap.comp k.symm.toLinearEquiv.toLinearMap) := by
    apply LinearMap.ext
    intro z
    rfl
  change (jointBlock j P Q).toLinearMap.det = T.toLinearMap.det
  rw [heq]
  exact LinearMap.det_conj T.toLinearMap k.toLinearEquiv

end Wikipedia.SmoothSixDPoincare.IntersectionCoordinates
