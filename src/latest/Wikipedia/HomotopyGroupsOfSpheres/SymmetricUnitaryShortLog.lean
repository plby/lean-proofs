import Wikipedia.HomotopyGroupsOfSpheres.UnitaryUniformSubdivision

/-! # Short relative logarithms within the symmetric determinant-one space -/

noncomputable section

open scoped Matrix.Norms.Frobenius Topology unitInterval
open Set

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.ShortLog

open NoExoticSixSphere.UniformTimePartition

variable {N : Type*} [Fintype N] [DecidableEq N]

def relative (B C : SpecialSpace N) : unitary (Matrix N N ℂ) := B.val.val⁻¹ * C.val.val

theorem relative_self (B : SpecialSpace N) : relative B B = 1 := inv_mul_cancel _

theorem relative_swap (B C : SpecialSpace N) : relative C B = (relative B C)⁻¹ := by
  simp only [relative, mul_inv_rev, inv_inv]

theorem relative_reversible (B C : SpecialSpace N) :
    (relative B C).val.transpose * B.val.val.val = B.val.val.val * (relative B C).val := by
  have hstar : (star B.val.val.val).transpose = star B.val.val.val :=
    congrArg star B.val.property
  change (star B.val.val.val * C.val.val.val).transpose * B.val.val.val =
    B.val.val.val * (star B.val.val.val * C.val.val.val)
  rw [Matrix.transpose_mul, C.val.property, hstar, mul_assoc,
    Unitary.star_mul_self_of_mem B.val.val.property, mul_one, ← mul_assoc,
    Unitary.mul_star_self_of_mem B.val.val.property, one_mul]

theorem relative_det (B C : SpecialSpace N) : (relative B C).val.det = 1 := by
  have hb : B.val.val.val.det = 1 := congrArg (fun z : Circle ↦ (z : ℂ)) B.property
  have hc : C.val.val.val.det = 1 := congrArg (fun z : Circle ↦ (z : ℂ)) C.property
  have hi : (star B.val.val.val).det = 1 := by
    have h := congrArg Matrix.det (Unitary.star_mul_self_of_mem B.val.val.property)
    simpa only [Matrix.det_mul, hb, mul_one, Matrix.det_one] using h
  change (star B.val.val.val * C.val.val.val).det = 1
  rw [Matrix.det_mul, hi, hc, one_mul]

theorem continuous_relative : Continuous (fun p : SpecialSpace N × SpecialSpace N ↦
    relative p.1 p.2) := by
  have hb : Continuous (fun p : SpecialSpace N × SpecialSpace N ↦ p.1.val.val) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst)
  have hc : Continuous (fun p : SpecialSpace N × SpecialSpace N ↦ p.2.val.val) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)
  exact hb.inv.mul hc

def domain (N : Type*) [Fintype N] [DecidableEq N] : Set (SpecialSpace N × SpecialSpace N) :=
  {p | relative p.1 p.2 ∈ ComplexSkewMatrices.CompatibleLog.domain N}

theorem isOpen_domain : IsOpen (domain N) :=
  ComplexSkewMatrices.CompatibleLog.isOpen_domain.preimage continuous_relative

theorem diagonal_mem_domain (B : SpecialSpace N) : (B, B) ∈ domain N := by
  change relative B B ∈ ComplexSkewMatrices.CompatibleLog.domain N
  rw [relative_self]
  exact ComplexSkewMatrices.CompatibleLog.one_mem_domain

def generator (B C : SpecialSpace N) : ComplexSkewMatrices.Space N :=
  ComplexSkewMatrices.logarithm (relative B C)

theorem generator_self (B : SpecialSpace N) : generator B B = 0 := by
  rw [generator, relative_self, ComplexSkewMatrices.logarithm_one]

theorem generator_reversible {B C : SpecialSpace N} (h : (B, C) ∈ domain N) :
    (generator B C).val.transpose * B.val.val.val = B.val.val.val * (generator B C).val := by
  change (ComplexSkewMatrices.logarithm (relative B C)).val.transpose * B.val.val.val =
    B.val.val.val * (ComplexSkewMatrices.logarithm (relative B C)).val
  rw [ComplexSkewMatrices.logarithm_val _ h.1]
  exact ComplexMatrixLocalLogarithm.logarithm_reversible B.val.val (relative B C) h.1
    (relative_reversible B C)

theorem generator_trace {B C : SpecialSpace N} (h : (B, C) ∈ domain N) :
    (generator B C).val.trace = 0 := by
  change (ComplexSkewMatrices.logarithm (relative B C)).val.trace = 0
  rw [ComplexSkewMatrices.logarithm_val _ h.1]
  exact ComplexMatrixLocalLogarithm.logarithm_trace_zero _ h.1 (relative_det B C)

theorem exp_generator {B C : SpecialSpace N} (h : (B, C) ∈ domain N) :
    ComplexSkewMatrices.exponential (generator B C) = relative B C :=
  ComplexSkewMatrices.exponential_logarithm _ h.1

theorem swap_mem_domain {B C : SpecialSpace N} (h : (B, C) ∈ domain N) : (C, B) ∈ domain N := by
  change relative C B ∈ ComplexSkewMatrices.CompatibleLog.domain N
  rw [relative_swap]
  exact ComplexSkewMatrices.CompatibleLog.inverse_mem_domain _ h

theorem generator_swap {B C : SpecialSpace N} (h : (B, C) ∈ domain N) :
    generator C B = -generator B C := by
  rw [generator, relative_swap]
  exact ComplexSkewMatrices.logarithm_inverse _ h.1

theorem orthogonal_relative (B C : SpecialSpace N) :
    ComplexMatrixRealRepresentation.orthogonal (relative B C) =
      (ComplexMatrixRealRepresentation.specialOrthogonal B)⁻¹ *
        ComplexMatrixRealRepresentation.specialOrthogonal C := by
  rw [relative, map_mul, map_inv]
  rfl

theorem orthogonal_logarithm_eq {B C : SpecialSpace N} (h : (B, C) ∈ domain N) :
    NoExoticSixSphere.OrthogonalExponential.logarithmChart (2 * Fintype.card N)
      ((ComplexMatrixRealRepresentation.specialOrthogonal B)⁻¹ *
        ComplexMatrixRealRepresentation.specialOrthogonal C) =
      ComplexSkewMatrices.toOrthogonalSkew (generator B C) := by
  rw [← orthogonal_relative]
  exact ComplexSkewMatrices.CompatibleLog.orthogonal_logarithm_eq _ h

theorem continuous_generator : Continuous (fun p : domain N ↦ generator p.val.1 p.val.2) :=
  ComplexSkewMatrices.continuousOn_logarithm.comp_continuous
    (continuous_relative.comp continuous_subtype_val) (fun p ↦ p.property.1)

theorem exists_uniform_partition {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (H : C(I × X, SpecialSpace N)) (lower : ℕ) :
    ∃ m : ℕ, lower ≤ m ∧ ∀ i : Fin (m + 1),
      ∀ u ∈ Icc (unitTime m i.castSucc) (unitTime m i.succ), ∀ x,
        (H (unitTime m i.castSucc, x), H (u, x)) ∈ domain N := by
  let F : C(I × X, unitary (Matrix N N ℂ)) :=
    ⟨fun z ↦ (H z).val.val, continuous_subtype_val.comp
      (continuous_subtype_val.comp H.continuous)⟩
  exact ComplexSkewMatrices.CompatibleLog.exists_uniform_increment_partition F _
    (ComplexSkewMatrices.CompatibleLog.isOpen_domain.mem_nhds
      (ComplexSkewMatrices.CompatibleLog.one_mem_domain (N := N))) lower

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.ShortLog
