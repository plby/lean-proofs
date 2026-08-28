import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryShortLog
import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryExponentialStep

/-! # Continuous short segments in the symmetric determinant-one space -/

noncomputable section

open scoped Matrix.Norms.Frobenius Topology unitInterval Manifold ContDiff

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.ShortLog

variable {N : Type*} [Fintype N] [DecidableEq N]

def segment (B C : SpecialSpace N) (h : (B, C) ∈ domain N) (t : ℝ) : SpecialSpace N :=
  reversibleStep B (generator B C) (generator_trace h) (generator_reversible h) t

theorem segment_unitary (B C : SpecialSpace N) (h : (B, C) ∈ domain N) (t : ℝ) :
    (segment B C h t).val.val =
      B.val.val * ComplexSkewMatrices.exponential (t • generator B C) := rfl

theorem segment_matrix (B C : SpecialSpace N) (h : (B, C) ∈ domain N) (t : ℝ) :
    (segment B C h t).val.val.val =
      B.val.val.val * NormedSpace.exp (t • (generator B C).val) := rfl

theorem segment_zero (B C : SpecialSpace N) (h : (B, C) ∈ domain N) : segment B C h 0 = B :=
  reversibleStep_zero B _ _ _

theorem segment_one (B C : SpecialSpace N) (h : (B, C) ∈ domain N) : segment B C h 1 = C := by
  apply Subtype.ext
  apply Subtype.ext
  rw [segment_unitary, one_smul, exp_generator h, relative, mul_inv_cancel_left]

theorem segment_self (B : SpecialSpace N) (t : ℝ) :
    segment B B (diagonal_mem_domain B) t = B := by
  apply Subtype.ext
  apply Subtype.ext
  rw [segment_unitary, generator_self, smul_zero, ComplexSkewMatrices.exponential_zero, mul_one]

theorem continuous_segment :
    Continuous (fun p : domain N × ℝ ↦ segment p.1.val.1 p.1.val.2 p.1.property p.2) := by
  have hb : Continuous (fun p : domain N × ℝ ↦ p.1.val.1.val.val) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp
      (continuous_fst.comp (continuous_subtype_val.comp continuous_fst)))
  have hg : Continuous (fun p : domain N × ℝ ↦ generator p.1.val.1 p.1.val.2) :=
    continuous_generator.comp continuous_fst
  have he : Continuous (fun p : domain N × ℝ ↦
      ComplexSkewMatrices.exponential (p.2 • generator p.1.val.1 p.1.val.2)) :=
    ComplexSkewMatrices.continuous_exponential.comp (continuous_snd.smul hg)
  exact ((hb.mul he).subtype_mk _).subtype_mk _

def family : C(domain N × ℝ, SpecialSpace N) :=
  ⟨fun p ↦ segment p.1.val.1 p.1.val.2 p.1.property p.2, continuous_segment⟩

def path (B C : SpecialSpace N) (h : (B, C) ∈ domain N) : Path B C where
  toFun t := segment B C h t
  continuous_toFun := by
    have hc : Continuous (segment B C h) :=
      (contMDiff_reversibleStep B (generator B C) (generator_trace h)
        (generator_reversible h)).continuous
    exact hc.comp continuous_subtype_val
  source' := segment_zero B C h
  target' := segment_one B C h

theorem segment_reverse (B C : SpecialSpace N) (h : (B, C) ∈ domain N) (t : ℝ) :
    segment C B (swap_mem_domain h) t = segment B C h (1 - t) := by
  apply Subtype.ext
  apply Subtype.ext
  rw [segment_unitary, segment_unitary, generator_swap h]
  have hend : C.val.val = B.val.val * ComplexSkewMatrices.exponential (generator B C) := by
    rw [exp_generator h, relative, mul_inv_cancel_left]
  rw [hend, mul_assoc]
  have hneg : t • -(generator B C) = (-t) • generator B C := by
    exact (smul_neg t (generator B C)).trans (neg_smul t (generator B C)).symm
  rw [hneg]
  have hone : ComplexSkewMatrices.exponential (generator B C) =
      ComplexSkewMatrices.exponential ((1 : ℝ) • generator B C) := by rw [one_smul]
  rw [hone, ← ComplexSkewMatrices.exponential_add_smul]
  exact congrArg (fun s : ℝ ↦ B.val.val * ComplexSkewMatrices.exponential (s • generator B C))
    (by ring)

theorem segment_orthogonal (B C : SpecialSpace N) (h : (B, C) ∈ domain N) (t : ℝ) :
    ComplexMatrixRealRepresentation.specialOrthogonal (segment B C h t) =
      ComplexMatrixRealRepresentation.specialOrthogonal B *
        NoExoticSixSphere.OrthogonalExponential.exp
          (t • ComplexSkewMatrices.toOrthogonalSkew (generator B C)) := by
  change ComplexMatrixRealRepresentation.orthogonal (segment B C h t).val.val = _
  rw [segment_unitary, map_mul, ComplexSkewMatrices.orthogonal_exponential, map_smul]
  rfl

theorem contMDiff_segment (B C : SpecialSpace N) (h : (B, C) ∈ domain N) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, RealSymmetricMixing.DirectionSpace N) ∞ (segment B C h) :=
  contMDiff_reversibleStep B (generator B C) (generator_trace h) (generator_reversible h)

theorem hasDerivAt_segment_matrix (B C : SpecialSpace N) (h : (B, C) ∈ domain N) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ (segment B C h s).val.val.val)
      ((segment B C h t).val.val.val * (generator B C).val) t :=
  hasDerivAt_reversibleStep_matrix B (generator B C) (generator_trace h) (generator_reversible h) t

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.ShortLog
