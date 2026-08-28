import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryVertexSpace

/-! # Global continuity of the actual inverse vertex charts -/

open scoped Matrix.Norms.Frobenius

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.VertexSpace

variable {N : Type*} [Fintype N] [DecidableEq N] {m : ℕ}

theorem continuous_atVertices_symm (v : Space N m) : Continuous (atVertices v).symm := by
  apply continuous_iff_continuousAt.mpr
  intro K
  apply continuousAt_pi.mpr
  intro i
  exact tendsto_subtype_rng.mpr (tendsto_subtype_rng.mpr (tendsto_subtype_rng.mpr
    (contDiff_symm_matrix_eval v i).continuous.continuousAt))

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.VertexSpace
