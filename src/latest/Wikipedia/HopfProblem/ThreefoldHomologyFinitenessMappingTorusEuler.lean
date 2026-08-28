import Wikipedia.HopfProblem.ThreefoldHomologyFinitenessMappingTorus
import Wikipedia.HopfProblem.ThreefoldHomologyFinitenessAlgebraRank

/-!
# Euler characteristic of an actual four-torus mapping torus

The literal Wang maps are rationalized by tensoring with `ℚ`. Exactness
shows that the image ranks of the fibre map and the outgoing Wang boundary
agree in the same fibre degree.  Consequently the mapping-torus Betti
numbers are successive sums of the actual fibre-image ranks, which cancel
in the alternating sum. No rank of an unspecified monodromy matrix, or
torsion-freeness of the mapping-torus homology, is assumed.
-/

noncomputable section

open Module
open scoped TensorProduct

namespace Wikipedia.HopfProblem.ThreefoldHomologyFinitenessMappingTorus

open SingularMayerVietoris PeriodTorusHigherHomology MappingTorusHomology
open ThreefoldHomologyFinitenessAlgebra

/-- The rational rank of the actual integral mapping-torus homology. -/
def rationalBetti (f : RealTorus₄ ≃ₜ RealTorus₄) (n : ℕ) : ℕ :=
  finrank ℚ (ℚ ⊗[ℤ] SingularHomology (MappingTorus.Torus f) n)

/-- Rationalized actual torus homology is finite-dimensional in every degree. -/
theorem rational_realTorus_finite (n : ℕ) :
    Module.Finite ℚ (ℚ ⊗[ℤ] SingularHomology RealTorus₄ n) := by
  let := realTorus_homology_finite n
  exact rationalization_finite _

/-- This finiteness is derived from the actual integral Wang sequence. -/
theorem rational_homology_finite (f : RealTorus₄ ≃ₜ RealTorus₄) (n : ℕ) :
    Module.Finite ℚ (ℚ ⊗[ℤ] SingularHomology (MappingTorus.Torus f) n) := by
  let := homology_finite f n
  exact rationalization_finite _

attribute [local instance] rational_realTorus_finite rational_homology_finite

/-- Exactness at the actual fibre after literal rational tensor base change. -/
theorem rational_wang_exact_at_fibre (f : RealTorus₄ ≃ₜ RealTorus₄) (n : ℕ) :
    Function.Exact ((wangDifference f n).baseChange ℚ)
      ((fibreHomologyMap f n).baseChange ℚ) :=
  rationalization_exact _ _ (LinearMap.exact_iff.mpr (wang_exact_at_fibre f n).symm)

/-- Exactness at the actual mapping torus after literal rational tensor base change. -/
theorem rational_wang_exact_at_mappingTorus (f : RealTorus₄ ≃ₜ RealTorus₄) (n : ℕ) :
    Function.Exact ((fibreHomologyMap f (n + 1)).baseChange ℚ)
      ((wangBoundary f n).baseChange ℚ) :=
  rationalization_exact _ _ (fibre_wang_exact f n)

/-- The outgoing rationalized Wang boundary still maps onto the actual invariant kernel. -/
theorem rational_wang_exact_at_difference (f : RealTorus₄ ≃ₜ RealTorus₄) (n : ℕ) :
    Function.Exact ((wangBoundary f n).baseChange ℚ)
      ((wangDifference f n).baseChange ℚ) :=
  rationalization_exact _ _ (LinearMap.exact_iff.mpr (wangBoundary_range f n).symm)

/-- The image rank of the actual fibre inclusion, not an assumed monodromy coordinate. -/
def fibreImageRank (f : RealTorus₄ ≃ₜ RealTorus₄) (n : ℕ) : ℕ :=
  finrank ℚ (LinearMap.range ((fibreHomologyMap f n).baseChange ℚ))

/-- Exactness at the two copies of actual fibre homology equates these two image ranks. -/
theorem wangBoundary_imageRank_eq (f : RealTorus₄ ≃ₜ RealTorus₄) (n : ℕ) :
    finrank ℚ (LinearMap.range ((wangBoundary f n).baseChange ℚ)) = fibreImageRank f n := by
  have hf := rational_finrank_eq_add_ranges_of_exact
    ((wangDifference f n).baseChange ℚ) ((fibreHomologyMap f n).baseChange ℚ)
    (rational_wang_exact_at_fibre f n)
  have hd := rational_finrank_eq_add_ranges_of_exact
    ((wangBoundary f n).baseChange ℚ) ((wangDifference f n).baseChange ℚ)
    (rational_wang_exact_at_difference f n)
  unfold fibreImageRank
  omega

/-- Every positive Betti number is the sum of successive actual fibre-image ranks. -/
theorem rationalBetti_succ (f : RealTorus₄ ≃ₜ RealTorus₄) (n : ℕ) :
    rationalBetti f (n + 1) = fibreImageRank f (n + 1) + fibreImageRank f n := by
  have h := rational_finrank_eq_add_ranges_of_exact
    ((fibreHomologyMap f (n + 1)).baseChange ℚ) ((wangBoundary f n).baseChange ℚ)
    (rational_wang_exact_at_mappingTorus f n)
  rw [wangBoundary_imageRank_eq] at h
  exact h

/-- The degree-zero endpoint is the image of the actual fibre inclusion. -/
theorem rationalBetti_zero (f : RealTorus₄ ≃ₜ RealTorus₄) :
    rationalBetti f 0 = fibreImageRank f 0 := by
  unfold fibreImageRank
  rw [LinearMap.range_eq_top.mpr
    (rationalization_surjective (fibreHomologyMap f 0) (fibreHomologyMap_zero_surjective f)),
    finrank_top]
  rfl

/-- Above fibre degree four, the actual fibre-image rank is zero. -/
theorem fibreImageRank_eq_zero_of_lt (f : RealTorus₄ ≃ₜ RealTorus₄)
    {n : ℕ} (hn : 4 < n) : fibreImageRank f n = 0 := by
  let := realTorus_homology_subsingleton_of_lt hn
  have : Subsingleton (LinearMap.range ((fibreHomologyMap f n).baseChange ℚ)) :=
    ((fibreHomologyMap f n).baseChange ℚ).surjective_rangeRestrict.subsingleton
  exact Module.finrank_zero_of_subsingleton

/-- The finite support is a consequence of the proved integral vanishing. -/
theorem rationalBetti_eq_zero_of_lt (f : RealTorus₄ ≃ₜ RealTorus₄)
    {n : ℕ} (hn : 5 < n) : rationalBetti f n = 0 := by
  let := homology_subsingleton_of_lt f hn
  exact Module.finrank_zero_of_subsingleton

/-- The complete alternating sum, using the proved degree-five support bound. -/
def eulerCharacteristic (f : RealTorus₄ ≃ₜ RealTorus₄) : ℤ :=
  ∑ n ∈ Finset.range 6, (-1 : ℤ) ^ n * (rationalBetti f n : ℤ)

/-- Every actual four-torus mapping torus has Euler characteristic zero. -/
theorem eulerCharacteristic_eq_zero (f : RealTorus₄ ≃ₜ RealTorus₄) :
    eulerCharacteristic f = 0 := by
  have h0 := rationalBetti_zero f
  have h1 := rationalBetti_succ f 0
  have h2 := rationalBetti_succ f 1
  have h3 := rationalBetti_succ f 2
  have h4 := rationalBetti_succ f 3
  have h5 := rationalBetti_succ f 4
  have h6 := fibreImageRank_eq_zero_of_lt f (n := 5) (by decide)
  norm_num at h1 h2 h3 h4 h5
  norm_num [eulerCharacteristic, Finset.sum_range_succ]
  omega

/-- The alternating sum is independent of any larger finite cutoff. -/
theorem euler_sum_eq_zero (f : RealTorus₄ ≃ₜ RealTorus₄) (N : ℕ) (hN : 6 ≤ N) :
    (∑ n ∈ Finset.range N, (-1 : ℤ) ^ n * (rationalBetti f n : ℤ)) = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  rw [Finset.sum_range_add]
  change eulerCharacteristic f + _ = 0
  rw [eulerCharacteristic_eq_zero, zero_add]
  apply Finset.sum_eq_zero
  intro n _
  rw [rationalBetti_eq_zero_of_lt f (by omega), Nat.cast_zero, mul_zero]

end Wikipedia.HopfProblem.ThreefoldHomologyFinitenessMappingTorus
