import Wikipedia.HopfProblem.NormalCrossing
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Coordinate permutations for the cusp normal forms

Permuting the three complex coordinates gives an actual complex-linear
biholomorphism. A product of one or two distinct coordinates can therefore
be put in the forms `w 0` and `w 0 * w 1` without changing the center.
-/

noncomputable section

open Set
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.CuspNormalForms

open ToricCharts

local notation "E₃" => CoordinateSpace 3
local notation "I₃" => modelWithCornersSelf ℂ E₃

/-- The complex-linear coordinate permutation, with inverse given by
precomposition with the original index permutation. -/
def coordinatePermutationLinear (σ : Equiv.Perm (Fin 3)) : E₃ ≃L[ℂ] E₃ where
  toFun z j := z (σ.symm j)
  invFun z j := z (σ j)
  left_inv z := by ext j; simp
  right_inv z := by ext j; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := continuous_pi fun j => continuous_apply (σ.symm j)
  continuous_invFun := continuous_pi fun j => continuous_apply (σ j)

/-- An analytic self-diffeomorphism for the standard complex coordinate atlas. -/
def coordinatePermutation (σ : Equiv.Perm (Fin 3)) :
    Diffeomorph I₃ I₃ E₃ E₃ ω where
  toEquiv := (coordinatePermutationLinear σ).toLinearEquiv.toEquiv
  contMDiff_toFun := (coordinatePermutationLinear σ).contDiff.contMDiff
  contMDiff_invFun := (coordinatePermutationLinear σ).symm.contDiff.contMDiff

@[simp] theorem coordinatePermutation_apply (σ : Equiv.Perm (Fin 3)) (z : E₃)
    (j : Fin 3) : coordinatePermutation σ z j = z (σ.symm j) := rfl

@[simp] theorem coordinatePermutation_symm_apply (σ : Equiv.Perm (Fin 3)) (z : E₃)
    (j : Fin 3) : (coordinatePermutation σ).symm z j = z (σ j) := rfl

@[simp] theorem coordinatePermutation_zero (σ : Equiv.Perm (Fin 3)) :
    coordinatePermutation σ 0 = 0 := rfl

@[simp] theorem coordinatePermutation_symm_zero (σ : Equiv.Perm (Fin 3)) :
    (coordinatePermutation σ).symm 0 = 0 := rfl

/-- The coordinate product is reindexed by the actual inverse biholomorphism. -/
theorem product_coordinatePermutation_symm (J : Finset (Fin 3))
    (σ : Equiv.Perm (Fin 3)) (w : E₃) :
    (∏ j ∈ J, (coordinatePermutation σ).symm w j) =
      ∏ j ∈ J.map σ.toEmbedding, w j := by
  simp only [Finset.prod_map, Equiv.coe_toEmbedding, coordinatePermutation_symm_apply]

/-- Two distinct indices can be moved to the first two coordinate positions. -/
theorem exists_permutation_pair (i j : Fin 3) (hij : i ≠ j) :
    ∃ σ : Equiv.Perm (Fin 3), σ i = 0 ∧ σ j = 1 := by
  let a := Equiv.swap i 0
  have ha0 : a i = 0 := Equiv.swap_apply_left i 0
  have hj0 : a j ≠ 0 := by
    rw [← ha0]
    exact a.injective.ne hij.symm
  refine ⟨a.trans (Equiv.swap (a j) 1), ?_, ?_⟩
  · change Equiv.swap (a j) 1 (a i) = 0
    rw [ha0]
    exact Equiv.swap_apply_of_ne_of_ne hj0.symm (by decide)
  · exact Equiv.swap_apply_left (a j) 1

/-- A single coordinate factor is the first coordinate in a centered
analytic coordinate system. -/
theorem exists_coordinate_normalization_card_one (J : Finset (Fin 3))
    (hJ : J.card = 1) :
    ∃ d : Diffeomorph I₃ I₃ E₃ E₃ ω, d 0 = 0 ∧
      ∀ w : E₃, (∏ j ∈ J, d.symm w j) = w 0 := by
  obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hJ
  refine ⟨coordinatePermutation (Equiv.swap i 0), coordinatePermutation_zero _, ?_⟩
  intro w
  simp

/-- Two distinct coordinate factors are the first two coordinates in a
centered analytic coordinate system. -/
theorem exists_coordinate_normalization_card_two (J : Finset (Fin 3))
    (hJ : J.card = 2) :
    ∃ d : Diffeomorph I₃ I₃ E₃ E₃ ω, d 0 = 0 ∧
      ∀ w : E₃, (∏ j ∈ J, d.symm w j) = w 0 * w 1 := by
  obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp hJ
  obtain ⟨σ, hσi, hσj⟩ := exists_permutation_pair i j hij
  refine ⟨coordinatePermutation σ, coordinatePermutation_zero _, ?_⟩
  intro w
  simp only [Finset.prod_pair hij, coordinatePermutation_symm_apply, hσi, hσj]

/-- Three distinct factors use every coordinate, so no permutation is needed. -/
theorem product_eq_three_of_card (J : Finset (Fin 3)) (hJ : J.card = 3) (w : E₃) :
    (∏ j ∈ J, w j) = w 0 * w 1 * w 2 := by
  have hJu : J = Finset.univ :=
    Finset.eq_of_subset_of_card_le (Finset.subset_univ J) (by simp [hJ])
  rw [hJu, Fin.prod_univ_three]

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.CuspNormalForms
