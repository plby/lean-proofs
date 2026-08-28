import Wikipedia.HomotopyGroupsOfSpheres.RealUnitaryMatrices

/-! # Compactness of the actual symmetric determinant-one matrix space -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices

variable {N : Type*} [Fintype N] [DecidableEq N]

open scoped Matrix.Norms.Elementwise in
theorem isCompact_complex_unitary :
    IsCompact (unitary (Matrix N N ℂ) : Set (Matrix N N ℂ)) := by
  have hclosed : IsClosed (unitary (Matrix N N ℂ) : Set (Matrix N N ℂ)) := by
    have hm : Continuous (fun U : Matrix N N ℂ ↦ star U * U) :=
      continuous_star.matrix_mul continuous_id
    have hm' : Continuous (fun U : Matrix N N ℂ ↦ U * star U) :=
      continuous_id.matrix_mul continuous_star
    exact (isClosed_eq hm continuous_const).inter (isClosed_eq hm' continuous_const)
  apply (isCompact_closedBall (0 : Matrix N N ℂ) 1).of_isClosed_subset hclosed
  intro U hU
  simpa only [Metric.mem_closedBall, dist_zero_right] using entrywise_sup_norm_bound_of_unitary hU

instance complexUnitary_compactSpace : CompactSpace (unitary (Matrix N N ℂ)) :=
  isCompact_iff_compactSpace.mp isCompact_complex_unitary

theorem isClosed_symmetricLocus :
    IsClosed {B : unitary (Matrix N N ℂ) | B.val.transpose = B.val} :=
  isClosed_eq continuous_subtype_val.matrix_transpose continuous_subtype_val

instance symmetricUnitary_compactSpace : CompactSpace (Space N) :=
  isCompact_iff_compactSpace.mp (isClosed_symmetricLocus (N := N)).isCompact

instance specialSpace_compactSpace : CompactSpace (SpecialSpace N) :=
  isCompact_iff_compactSpace.mp (isClosed_specialLocus (N := N)).isCompact

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices
