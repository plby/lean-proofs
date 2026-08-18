/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos984.HunterRotation
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Fourier characters on finite unit tori

We use explicit products of Mathlib's circle monomials.  The main result in
this file is their Haar orthogonality on a finite product torus.
-/

open Set Function MeasureTheory
open scoped BigOperators ComplexConjugate
open AddCircle

namespace Erdos984

noncomputable section

/-- The Fourier character of a finite unit torus indexed by an integer
frequency vector. -/
def torusFourier {D : Type*} [Fintype D] (ξ : D → ℤ)
    (x : UnitAddTorus D) : ℂ :=
  ∏ j, fourier (ξ j) (x j)

@[simp] lemma torusFourier_zero {D : Type*} [Fintype D]
    (x : UnitAddTorus D) : torusFourier (fun _ ↦ 0) x = 1 := by
  simp [torusFourier]

lemma torusFourier_add_frequency {D : Type*} [Fintype D]
    (ξ η : D → ℤ) (x : UnitAddTorus D) :
    torusFourier (ξ + η) x = torusFourier ξ x * torusFourier η x := by
  simp only [torusFourier, Pi.add_apply, fourier_add]
  exact Finset.prod_mul_distrib

lemma torusFourier_neg {D : Type*} [Fintype D]
    (ξ : D → ℤ) (x : UnitAddTorus D) :
    torusFourier (-ξ) x = conj (torusFourier ξ x) := by
  simp [torusFourier, map_prod]

lemma torusFourier_add_point {D : Type*} [Fintype D]
    (ξ : D → ℤ) (x y : UnitAddTorus D) :
    torusFourier ξ (x + y) = torusFourier ξ x * torusFourier ξ y := by
  simp only [torusFourier, Pi.add_apply, fourier_apply, zsmul_add,
    toCircle_add, Circle.coe_mul]
  exact Finset.prod_mul_distrib

@[simp] lemma norm_torusFourier {D : Type*} [Fintype D]
    (ξ : D → ℤ) (x : UnitAddTorus D) : ‖torusFourier ξ x‖ = 1 := by
  simp only [torusFourier, norm_prod, fourier_apply]
  apply Finset.prod_eq_one
  intro j _hj
  exact Circle.norm_coe _

lemma integral_unitAddCircle_fourier (n : ℤ) :
    ∫ x : UnitAddCircle, fourier n x = if n = 0 then 1 else 0 := by
  by_cases hn : n = 0
  · subst n
    rw [if_pos rfl]
    simp only [fourier_zero]
    rw [integral_const]
    simp [AddCircle.volume_eq_smul_haarAddCircle]
  · simp only [hn, ↓reduceIte]
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simp only [ENNReal.ofReal_one, one_smul]
    convert integral_eq_zero_of_add_right_eq_neg
      (μ := AddCircle.haarAddCircle)
      (fourier_add_half_inv_index (T := (1 : ℝ)) hn (by norm_num))

/-- Orthogonality of product-torus characters. -/
lemma integral_torusFourier {D : Type*} [Fintype D] (ξ : D → ℤ) :
    ∫ x : UnitAddTorus D, torusFourier ξ x = if ξ = 0 then 1 else 0 := by
  classical
  change (∫ x : UnitAddTorus D, ∏ j, fourier (ξ j) (x j)) = _
  rw [integral_fintype_prod_volume_eq_prod]
  simp_rw [integral_unitAddCircle_fourier]
  by_cases hξ : ξ = 0
  · simp [hξ]
  · simp only [hξ, ↓reduceIte]
    have hex : ∃ j, ξ j ≠ 0 := by
      simpa [funext_iff] using hξ
    obtain ⟨j, hj⟩ := hex
    exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)

/-- Pairwise character orthogonality in the form used to integrate squares
of finite Fourier sums. -/
lemma integral_torusFourier_mul_conj
    {D : Type*} [Fintype D] (ξ η : D → ℤ) :
    ∫ x : UnitAddTorus D, torusFourier ξ x * conj (torusFourier η x) =
      if ξ = η then 1 else 0 := by
  simp_rw [← torusFourier_neg η, ← torusFourier_add_frequency]
  rw [integral_torusFourier]
  by_cases hξη : ξ = η
  · subst ξ
    simp
  · rw [if_neg hξη, if_neg]
    intro hzero
    apply hξη
    funext j
    have hj := congrFun hzero j
    simp only [Pi.add_apply, Pi.neg_apply, Pi.zero_apply] at hj
    omega

end

end Erdos984
