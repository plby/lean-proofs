import Wikipedia.NoExoticSixSphere.EquatorDimension
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Normed.Module.Span

/-!
# Orthogonal coordinates adapted to one unit column

Split the ambient space isometrically into the given unit-vector line and its
actual orthogonal complement. The complement is identified with the smaller
Euclidean model. These are genuine isometries used to identify column fibers,
not a dimension-only replacement of an orthogonal operator space.
-/

open Module

namespace NoExoticSixSphere.ColumnCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A unit vector identifies its actual linear span isometrically with the real line. -/
noncomputable def line (v : UnitSphere E) : ℝ ≃ₗᵢ[ℝ] (ℝ ∙ (v : E)) where
  toLinearEquiv := LinearEquiv.toSpanNonzeroSingleton ℝ E (v : E) (ne_zero_of_mem_unit_sphere v)
  norm_map' t := by
    simpa only [ClosedHemisphere.unit_norm, one_mul] using
      LinearEquiv.toSpanNonzeroSingleton_homothety (𝕜 := ℝ) (v : E)
        (ne_zero_of_mem_unit_sphere v) t

/-- The line coordinate is the scalar multiple of the specified unit vector. -/
theorem line_apply (v : UnitSphere E) (t : ℝ) : ((line v t : ℝ ∙ (v : E)) : E) = t • (v : E) :=
  rfl

variable {r : ℕ} [FiniteDimensional ℝ E] [Fact (finrank ℝ E = r + 1)]

/-- Orthonormal coordinates on the actual complement of the specified unit vector. -/
noncomputable def complement (v : UnitSphere E) :
    (ℝ ∙ (v : E))ᗮ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r) :=
  (OrthonormalBasis.fromOrthogonalSpanSingleton r (ne_zero_of_mem_unit_sphere v)).repr

/-- Full ambient coordinates split off the chosen unit vector as the first real coordinate. -/
noncomputable def split (v : UnitSphere E) :
    E ≃ₗᵢ[ℝ] WithLp 2 (ℝ × EuclideanSpace ℝ (Fin r)) :=
  (ℝ ∙ (v : E)).orthogonalDecomposition.trans
    (LinearIsometryEquiv.withLpProdCongr 2 (line v).symm (complement v))

omit [FiniteDimensional ℝ E] in
/-- Reconstruct an actual ambient vector from its scalar and complement coordinates. -/
theorem split_symm_apply (v : UnitSphere E) (z : WithLp 2 (ℝ × EuclideanSpace ℝ (Fin r))) :
    (split v).symm z = z.fst • (v : E) + ((complement v).symm z.snd : E) :=
  rfl

omit [FiniteDimensional ℝ E] in
/-- The chosen unit column is precisely the first coordinate vector. -/
theorem split_self (v : UnitSphere E) :
    split (r := r) v (v : E) = WithLp.toLp 2 ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin r))) := by
  apply (split v).symm.injective
  rw [LinearIsometryEquiv.symm_apply_apply, split_symm_apply]
  simp

omit [FiniteDimensional ℝ E] in
/-- The first coordinate is the actual inner product with the distinguished unit vector. -/
theorem split_fst (v : UnitSphere E) (x : E) :
    (split (r := r) v x).fst = inner ℝ (v : E) x := by
  have hs : (split (r := r) v x).fst =
      (line v).symm ((ℝ ∙ (v : E)).orthogonalProjectionOnto x) := by
    simp only [split, LinearIsometryEquiv.trans_apply, Submodule.orthogonalDecomposition_apply,
      LinearIsometryEquiv.withLpProdCongr_apply]
    rfl
  rw [hs]
  apply (line v).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  apply Subtype.ext
  change (ℝ ∙ (v : E)).starProjection x = inner ℝ (v : E) x • (v : E)
  rw [Submodule.starProjection_singleton]
  simp only [ClosedHemisphere.unit_norm, one_pow, RCLike.ofReal_one, div_one]

omit [FiniteDimensional ℝ E] in
/-- The other coordinates are orthogonal projection onto the actual complement. -/
theorem split_snd (v : UnitSphere E) (x : E) :
    (split (r := r) v x).snd = complement v ((ℝ ∙ (v : E))ᗮ.orthogonalProjectionOnto x) := by
  simp only [split, LinearIsometryEquiv.trans_apply, Submodule.orthogonalDecomposition_apply,
    LinearIsometryEquiv.withLpProdCongr_apply]
  rfl

end NoExoticSixSphere.ColumnCoordinates
