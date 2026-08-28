import Wikipedia.HopfProblem.ConifoldPolarNativeFramingComplement
import Wikipedia.HopfProblem.ConifoldPolarRegions
import Wikipedia.HopfProblem.StandardSixSphereCircleModelRegions

/-!
# The literal smoothing cap and corrected standard closed exterior

The Frobenius bound `17/4` is exactly polar radius `3/4`.  Under the explicit
orthogonal correction and positive rescaling, it becomes the closed exterior
of the existing standard normal tube of radius `1/2`.  The homeomorphism below
is a restriction of the corrected global map, with the original subspace
topologies and unchanged formulas in both directions.
-/

namespace Wikipedia.HopfProblem.ConifoldPolar.NativeFraming

open ConifoldStandardBoundary
open StandardSixSphereCircleModel (closedExterior exteriorInComplement exteriorAsComplement)

/-- The cap is defined by the original matrix's literal squared Frobenius bound. -/
def smoothingCap : Set SpecialLinear := frobeniusBound (17 / 4)

abbrev SmoothingCap := ↥smoothingCap

theorem mem_smoothingCap_iff_norm_forward_le (M : SpecialLinear) :
    M ∈ smoothingCap ↔ ‖(ConifoldPolar.forward M).1‖ ≤ (3 / 4 : ℝ) := by
  change frobeniusSq M.val ≤ (17 / 4 : ℝ) ↔ _
  rw [frobeniusSq_eq, ← sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 3 / 4)]
  constructor <;> intro h <;> nlinarith

theorem correctedBaseEquiv_norm_le_sqrt_three_iff (b : Base) :
    ‖correctedBaseEquiv b‖ ≤ Real.sqrt 3 ↔ ‖b‖ ≤ (3 / 4 : ℝ) := by
  rw [correctedBaseEquiv_norm, ← rescalingFactor_mul_three_quarters]
  exact mul_le_mul_iff_right₀ rescalingFactor_pos

/-- Exact membership in the standard exterior, while retaining the global complement map. -/
theorem mem_smoothingCap_iff_exterior (M : SpecialLinear) :
    M ∈ smoothingCap ↔
      correctedComplementHomeomorph M ∈ exteriorInComplement (1 / 2 : ℝ) := by
  change M ∈ smoothingCap ↔
    (1 / 2 : ℝ) ≤ StandardSixSphereCircleModel.normalRadius (correctedComplementHomeomorph M)
  rw [StandardSixSphereCircleModel.le_normalRadius_iff_norm_forward_le
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1),
    forward_correctedComplementHomeomorph]
  simp only [half_boundaryProductRadius, correctedBaseEquiv_norm_le_sqrt_three_iff]
  exact mem_smoothingCap_iff_norm_forward_le M

/-- The same membership equivalence on the actual original standard sphere. -/
theorem mem_smoothingCap_iff_closedExterior (M : SpecialLinear) :
    M ∈ smoothingCap ↔
      (correctedComplementHomeomorph M).val ∈ closedExterior (1 / 2 : ℝ) :=
  mem_smoothingCap_iff_exterior M

/-- Restrict the corrected global formula to the literal cap and native closed exterior. -/
noncomputable def correctedCapHomeomorph :
    SmoothingCap ≃ₜ ↥(closedExterior (1 / 2 : ℝ)) :=
  (correctedComplementHomeomorph.subtype mem_smoothingCap_iff_exterior).trans
    (exteriorAsComplement (1 / 2) (by norm_num)).symm

@[simp] theorem correctedCapHomeomorph_apply_val (M : SmoothingCap) :
    (correctedCapHomeomorph M).val = (correctedComplementHomeomorph M.val).val := rfl

@[simp] theorem correctedCapHomeomorph_symm_apply_val
    (p : ↥(closedExterior (1 / 2 : ℝ))) :
    (correctedCapHomeomorph.symm p).val = correctedComplementHomeomorph.symm
      ((exteriorAsComplement (1 / 2) (by norm_num)) p).val := rfl

end Wikipedia.HopfProblem.ConifoldPolar.NativeFraming
