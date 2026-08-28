import Wikipedia.HopfProblem.ConifoldPolarHermitian
import Wikipedia.HopfProblem.ConifoldPolarTargetInverse
import Wikipedia.HopfProblem.ConifoldPolarRegularity
import Wikipedia.HopfProblem.ConifoldPolarCircleAlgebra

/-!
# The explicit global polar homeomorphism for determinant-one complex matrices

The forward map extracts the three coordinates of the positive Hermitian
factor and the four real coordinates of the unitary factor's second column.
Both directions use the original subspace topologies and original matrix
formulas.  This identifies a standard model, not a threefold complement.
-/

noncomputable section

namespace Wikipedia.HopfProblem.ConifoldPolar

open ConifoldStandardBoundary

theorem normalCoordinates_unitaryPart_mem_sphere (M : SpecialLinear) :
    normalCoordinates (unitaryPart M.val) ∈ NormalSphere := by
  rw [Metric.mem_sphere, dist_zero_right]
  exact norm_normalCoordinates_eq_one (unitaryPart M.val)
    (adjointAdjugate_unitaryPart M.val) (det_unitaryPart M.val M.property)

/-- The literal global polar coordinates on the original determinant-one matrix group. -/
def forward (M : SpecialLinear) : Base × NormalSphere :=
  (baseCoordinates (positivePart M.val),
    ⟨normalCoordinates (unitaryPart M.val), normalCoordinates_unitaryPart_mem_sphere M⟩)

/-- The explicit reverse map `P(b) U(z)` into the existing matrix group. -/
def inverse (q : Base × NormalSphere) : SpecialLinear :=
  ⟨inverseMatrix q.1 q.2.val,
    det_inverseMatrix q.1 q.2.val (StandardSixSphereCircleModel.normalSphere_norm q.2)⟩

@[simp] theorem forward_fst (M : SpecialLinear) :
    (forward M).1 = baseCoordinates (positivePart M.val) := rfl

@[simp] theorem forward_snd_val (M : SpecialLinear) :
    (forward M).2.val = normalCoordinates (unitaryPart M.val) := rfl

@[simp] theorem inverse_val (q : Base × NormalSphere) :
    (inverse q).val = positiveMatrix q.1 * unitaryMatrix q.2.val := rfl

theorem inverse_forward (M : SpecialLinear) : inverse (forward M) = M := by
  apply Subtype.ext
  change positiveMatrix (baseCoordinates (positivePart M.val)) *
      unitaryMatrix (normalCoordinates (unitaryPart M.val)) = M.val
  rw [positiveMatrix_baseCoordinates (positivePart_isHermitian M.val M.property)
      (det_positivePart M.val M.property) (trace_positivePart_re_pos M.val M.property),
    unitaryMatrix_normalCoordinates _ (adjointAdjugate_unitaryPart M.val)]
  exact positivePart_mul_unitaryPart M.val M.property

theorem forward_inverse (q : Base × NormalSphere) : forward (inverse q) = q := by
  have hz := StandardSixSphereCircleModel.normalSphere_norm q.2
  apply Prod.ext
  · change baseCoordinates (positivePart (inverseMatrix q.1 q.2.val)) = q.1
    rw [positivePart_inverseMatrix q.1 q.2.val hz, baseCoordinates_positiveMatrix]
  · apply Subtype.ext
    change normalCoordinates (unitaryPart (inverseMatrix q.1 q.2.val)) = q.2.val
    rw [unitaryPart_inverseMatrix q.1 q.2.val hz, normalCoordinates_unitaryMatrix]

theorem forward_continuous : Continuous forward := by
  have hp : Continuous (fun M : SpecialLinear => baseCoordinates (positivePart M.val)) :=
    baseCoordinates_continuous.comp (positivePart_continuous.comp continuous_subtype_val)
  have hu : Continuous (fun M : SpecialLinear => normalCoordinates (unitaryPart M.val)) :=
    normalCoordinates_continuous.comp (unitaryPart_continuous.comp continuous_subtype_val)
  exact hp.prodMk (hu.subtype_mk _)

theorem inverse_continuous : Continuous inverse := by
  have hq : Continuous (fun q : Base × NormalSphere => (q.1, q.2.val)) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  exact (inverseMatrix_continuous.comp hq).subtype_mk _

/-- The genuine explicit global polar homeomorphism, without an assumed decomposition theorem. -/
def homeomorph : SpecialLinear ≃ₜ Base × NormalSphere where
  toFun := forward
  invFun := inverse
  left_inv := inverse_forward
  right_inv := forward_inverse
  continuous_toFun := forward_continuous
  continuous_invFun := inverse_continuous

@[simp] theorem homeomorph_apply (M : SpecialLinear) : homeomorph M = forward M := rfl

@[simp] theorem homeomorph_symm_apply (q : Base × NormalSphere) :
    homeomorph.symm q = inverse q := rfl

/-- The squared Frobenius norm measures exactly the radial coordinate in real three-space. -/
theorem frobeniusSq_eq (M : SpecialLinear) :
    frobeniusSq M.val = 2 + 4 * ‖(forward M).1‖ ^ 2 := by
  calc
    frobeniusSq M.val = frobeniusSq (inverse (forward M)).val :=
      congrArg (fun N : SpecialLinear => frobeniusSq N.val) (inverse_forward M).symm
    _ = 2 + 4 * ‖(forward M).1‖ ^ 2 :=
      frobeniusSq_inverseMatrix (forward M).1 (forward M).2.val
        (StandardSixSphereCircleModel.normalSphere_norm (forward M).2)

theorem two_le_frobeniusSq (M : SpecialLinear) : 2 ≤ frobeniusSq M.val := by
  rw [frobeniusSq_eq]
  nlinarith [sq_nonneg ‖(forward M).1‖]

/-- The exact right diagonal circle map fixes the base and rotates the original normal vector. -/
theorem forward_circleAction (u : ℂ) (hu : ‖u‖ = 1) (M : SpecialLinear) :
    forward (circleAction u hu M) = ((forward M).1, sphereRotation u hu (forward M).2) := by
  apply Prod.ext
  · change baseCoordinates (positivePart (rightCircle u M.val)) =
      baseCoordinates (positivePart M.val)
    rw [positivePart_rightCircle u hu]
  · apply Subtype.ext
    change normalCoordinates (unitaryPart (rightCircle u M.val)) =
      normalRotation u (normalCoordinates (unitaryPart M.val))
    rw [unitaryPart_rightCircle u hu, normalCoordinates_rightCircle]

theorem homeomorph_circleAction (u : ℂ) (hu : ‖u‖ = 1) (M : SpecialLinear) :
    homeomorph (circleAction u hu M) =
      ((homeomorph M).1, sphereRotation u hu (homeomorph M).2) :=
  forward_circleAction u hu M

end Wikipedia.HopfProblem.ConifoldPolar
