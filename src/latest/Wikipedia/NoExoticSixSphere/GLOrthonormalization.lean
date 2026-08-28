import Wikipedia.NoExoticSixSphere.ContinuousGramSchmidt
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Orthonormalizing an actual invertible real operator

The columns of an invertible operator are independent. Continuous Gram--Schmidt
therefore produces an actual orthogonal operator, continuously in operator norm.
The positive diagonal of its triangular coordinate change is recorded for the
general-linear deformation argument.
-/

open InnerProductSpace Module

namespace NoExoticSixSphere.GLOrthonormalization

abbrev Vector (n : ℕ) := EuclideanSpace ℝ (Fin n)

variable (n : ℕ)

/-- The columns of an actual invertible operator in the standard orthonormal basis. -/
noncomputable def columns (a : InvertibleOperators (Vector n)) (i : Fin n) : Vector n :=
  a.1 (EuclideanSpace.basisFun (Fin n) ℝ i)

/-- Every such column family is linearly independent. -/
theorem columns_linearIndependent (a : InvertibleOperators (Vector n)) :
    LinearIndependent ℝ (columns n a) :=
  (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.linearIndependent.map'
    a.1.toLinearMap (LinearMap.ker_eq_bot.mpr a.2.injective)

/-- Each column depends continuously on the input operator. -/
theorem continuous_columns (i : Fin n) : Continuous (fun a ↦ columns n a i) :=
  continuous_subtype_val.clm_apply continuous_const

/-- The actual orthonormal basis obtained from the columns. -/
noncomputable def basis (a : InvertibleOperators (Vector n)) :
    OrthonormalBasis (Fin n) ℝ (Vector n) :=
  gramSchmidtOrthonormalBasis (by simp only [finrank_euclideanSpace_fin, Fintype.card_fin])
    (columns n a)

/-- The resulting basis vectors vary continuously. -/
theorem continuous_basis (i : Fin n) : Continuous (fun a ↦ basis n a i) :=
  continuous_gramSchmidtOrthonormalBasis _ (columns n) (continuous_columns n)
    (columns_linearIndependent n) i

/-- The corresponding genuine linear isometry equivalence. -/
noncomputable def orthogonalEquiv (a : InvertibleOperators (Vector n)) : Vector n ≃ₗᵢ[ℝ] Vector n :=
  (EuclideanSpace.basisFun (Fin n) ℝ).equiv (basis n a) (Equiv.refl _)

/-- The orthogonalized operator, with its usual operator-norm topology. -/
noncomputable def operator (a : InvertibleOperators (Vector n)) : Vector n →L[ℝ] Vector n :=
  (orthogonalEquiv n a).toContinuousLinearEquiv.toContinuousLinearMap

/-- Orthonormalization is continuous in operator norm, not only pointwise on basis vectors. -/
theorem continuous_operator : Continuous (operator n) := by
  apply continuous_clm_apply.mpr
  intro w
  have heq : (fun a ↦ operator n a w) = fun a ↦ ∑ i, w i • basis n a i := by
    funext a
    exact OrthonormalBasis.equiv_apply_euclideanSpace (basis n a) w
  rw [heq]
  exact continuous_finsetSum _ (fun i _ ↦ (continuous_basis n i).const_smul (w i))

/-- The orthogonalized operator sends each standard basis vector to the constructed basis. -/
theorem operator_basis (a : InvertibleOperators (Vector n)) (i : Fin n) :
    operator n a (EuclideanSpace.basisFun (Fin n) ℝ i) = basis n a i := by
  exact OrthonormalBasis.equiv_apply_basis _ _ _ i

/-- Gram--Schmidt gives positive diagonal entries in the new orthonormal coordinates. -/
theorem inner_basis_columns_pos (a : InvertibleOperators (Vector n)) (i : Fin n) :
    0 < inner ℝ (basis n a i) (columns n a i) := by
  have hne : gramSchmidtNormed ℝ (columns n a) i ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [gramSchmidtNormed_unit_length i (columns_linearIndependent n a)]
    exact one_ne_zero
  change 0 < inner ℝ (gramSchmidtOrthonormalBasis _ (columns n a) i) (columns n a i)
  rw [gramSchmidtOrthonormalBasis_apply _ hne]
  exact inner_gramSchmidtNormed_diagonal_pos (columns n a) (columns_linearIndependent n a) i

end NoExoticSixSphere.GLOrthonormalization
