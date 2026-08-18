/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos984.HunterKernel

/-!
# Pointwise bounds for the localized cosine kernel

The centered representative of a circle point lies in `[-1/2,1/2]`.
Jordan's sine inequality therefore gives the quadratic decay needed away
from the origin.
-/

open Set Function MeasureTheory AddCircle
open scoped BigOperators

namespace Erdos984

noncomputable section

lemma circleCosSq_re_eq_centered (x : UnitAddCircle) :
    (circleCosSq x).re =
      Real.cos (Real.pi * centeredCircleLift x) ^ 2 := by
  calc
    (circleCosSq x).re =
        (circleCosSq ((centeredCircleLift x : ℝ) : UnitAddCircle)).re := by
      rw [coe_centeredCircleLift]
    _ = Real.cos (Real.pi * centeredCircleLift x) ^ 2 := by
      have h := congrArg Complex.re
        (circleCosSq_coe (centeredCircleLift x))
      simpa only [Complex.ofReal_re] using h

lemma circleCosSq_re_nonneg (x : UnitAddCircle) :
    0 ≤ (circleCosSq x).re := circleCosSq_nonneg x

lemma circleCosSq_re_le_one (x : UnitAddCircle) :
    (circleCosSq x).re ≤ 1 := by
  rw [circleCosSq_re_eq_centered]
  nlinarith [Real.sin_sq_add_cos_sq
    (Real.pi * centeredCircleLift x),
    sq_nonneg (Real.sin (Real.pi * centeredCircleLift x))]

/-- Quadratic decay of the circle factor in terms of the centered lift. -/
lemma circleCosSq_re_le_one_sub_four_sq (x : UnitAddCircle) :
    (circleCosSq x).re ≤
      1 - 4 * centeredCircleLift x ^ 2 := by
  let t := centeredCircleLift x
  have ht : |t| ≤ (1 : ℝ) / 2 := centeredCircleLift_abs_le x
  have hangle : |Real.pi * t| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have hsin := Real.mul_abs_le_abs_sin hangle
  have htwo : 2 * |t| ≤ |Real.sin (Real.pi * t)| := by
    calc
      2 * |t| = 2 / Real.pi * |Real.pi * t| := by
        rw [abs_mul, abs_of_pos Real.pi_pos]
        field_simp [Real.pi_ne_zero]
      _ ≤ |Real.sin (Real.pi * t)| := hsin
  have hsq : (2 * |t|) ^ 2 ≤ |Real.sin (Real.pi * t)| ^ 2 :=
    (sq_le_sq₀ (by positivity) (abs_nonneg _)).2 htwo
  have htrig := Real.sin_sq_add_cos_sq (Real.pi * t)
  rw [circleCosSq_re_eq_centered]
  dsimp [t] at ht hangle hsin htwo hsq htrig ⊢
  nlinarith [sq_abs (centeredCircleLift x),
    sq_abs (Real.sin (Real.pi * centeredCircleLift x))]

lemma circleCosSq_re_le_exp (x : UnitAddCircle) :
    (circleCosSq x).re ≤
      Real.exp (-4 * centeredCircleLift x ^ 2) := by
  refine (circleCosSq_re_le_one_sub_four_sq x).trans ?_
  nlinarith [Real.add_one_le_exp (-4 * centeredCircleLift x ^ 2)]

/-- The complex product kernel is the coercion of the product of its real
nonnegative coordinate factors. -/
lemma torusCosineKernel_eq_ofReal_prod {D : Type*} [Fintype D]
    (k : ℕ) (x : UnitAddTorus D) :
    torusCosineKernel k x =
      ((∏ j, (circleCosSq (x j)).re ^ k : ℝ) : ℂ) := by
  rw [torusCosineKernel]
  push_cast
  apply Finset.prod_congr rfl
  intro j _hj
  have hz : circleCosSq (x j) =
      (((circleCosSq (x j)).re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using circleCosSq_real (x j)
  exact congrArg (fun z : ℂ ↦ z ^ k) hz

lemma torusCosineKernel_re_eq_prod {D : Type*} [Fintype D]
    (k : ℕ) (x : UnitAddTorus D) :
    (torusCosineKernel k x).re =
      ∏ j, (circleCosSq (x j)).re ^ k := by
  rw [torusCosineKernel_eq_ofReal_prod]
  exact Complex.ofReal_re _

lemma torusCosineKernel_re_nonneg {D : Type*} [Fintype D]
    (k : ℕ) (x : UnitAddTorus D) :
    0 ≤ (torusCosineKernel k x).re := by
  rw [torusCosineKernel_re_eq_prod]
  exact Finset.prod_nonneg fun j _hj ↦
    pow_nonneg (circleCosSq_re_nonneg _) _

/-- Product decay in the full Euclidean squared norm of the centered lift. -/
lemma torusCosineKernel_re_le_exp_squaredNorm
    {D : Type*} [Fintype D] (k : ℕ) (x : UnitAddTorus D) :
    (torusCosineKernel k x).re ≤
      Real.exp (-4 * k * squaredNorm (centeredTorusLift x)) := by
  classical
  rw [torusCosineKernel_re_eq_prod]
  calc
    ∏ j : D, (circleCosSq (x j)).re ^ k ≤
        ∏ j : D, Real.exp (-4 * k * centeredCircleLift (x j) ^ 2) := by
      apply Finset.prod_le_prod
      · intro j _hj
        exact pow_nonneg (circleCosSq_re_nonneg _) _
      · intro j _hj
        calc
          (circleCosSq (x j)).re ^ k ≤
              (Real.exp (-4 * centeredCircleLift (x j) ^ 2)) ^ k :=
            pow_le_pow_left₀ (circleCosSq_re_nonneg _)
              (circleCosSq_re_le_exp _) k
          _ = Real.exp (-4 * k * centeredCircleLift (x j) ^ 2) := by
            rw [← Real.exp_nat_mul]
            congr 1
            ring
    _ = Real.exp (∑ j : D, -4 * k * centeredCircleLift (x j) ^ 2) := by
      rw [Real.exp_sum]
    _ = Real.exp (-4 * k * squaredNorm (centeredTorusLift x)) := by
      congr 1
      rw [squaredNorm, EuclideanSpace.real_norm_sq_eq]
      simp only [centeredTorusLift_apply, Finset.mul_sum]

/-- If one coordinate has centered size at least `ρ`, the product kernel
decays exponentially at rate `4kρ²`. -/
lemma torusCosineKernel_re_le_exp_of_lt_norm
    {D : Type*} [Fintype D] [Nonempty D]
    (k : ℕ) (x : UnitAddTorus D) {rho : ℝ} (hrho : 0 ≤ rho)
    (hx : rho < ‖x‖) :
    (torusCosineKernel k x).re ≤
      Real.exp (-4 * k * rho ^ 2) := by
  classical
  have hex : ∃ j : D, rho < ‖x j‖ := by
    by_contra h
    push_neg at h
    have hall : ‖x‖ ≤ rho := by
      rw [pi_norm_le_iff_of_nonempty]
      exact h
    exact (not_le_of_gt hx) hall
  obtain ⟨j, hj⟩ := hex
  rw [norm_eq_abs_centeredCircleLift] at hj
  have hfactor_nonneg : ∀ i : D, 0 ≤ (circleCosSq (x i)).re ^ k :=
    fun i ↦ pow_nonneg (circleCosSq_re_nonneg _) _
  have hfactor_one : ∀ i : D, (circleCosSq (x i)).re ^ k ≤ 1 := by
    intro i
    simpa using pow_le_one₀ (circleCosSq_re_nonneg _) (circleCosSq_re_le_one _)
  rw [torusCosineKernel_re_eq_prod]
  calc
    ∏ i : D, (circleCosSq (x i)).re ^ k ≤
        (circleCosSq (x j)).re ^ k := by
      calc
        ∏ i : D, (circleCosSq (x i)).re ^ k =
            (circleCosSq (x j)).re ^ k *
              ∏ i ∈ (Finset.univ.erase j),
                (circleCosSq (x i)).re ^ k := by
          exact (Finset.mul_prod_erase Finset.univ
            (fun i ↦ (circleCosSq (x i)).re ^ k)
            (Finset.mem_univ j)).symm
        _ ≤ (circleCosSq (x j)).re ^ k * 1 := by
          apply mul_le_mul_of_nonneg_left
          · exact Finset.prod_le_one
              (fun i _hi ↦ hfactor_nonneg i)
              (fun i _hi ↦ hfactor_one i)
          · exact hfactor_nonneg j
        _ = (circleCosSq (x j)).re ^ k := by ring
    _ ≤ (Real.exp (-4 * centeredCircleLift (x j) ^ 2)) ^ k := by
      exact pow_le_pow_left₀ (circleCosSq_re_nonneg _)
        (circleCosSq_re_le_exp _) k
    _ = Real.exp (-4 * k * centeredCircleLift (x j) ^ 2) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ Real.exp (-4 * k * rho ^ 2) := by
      apply Real.exp_le_exp.mpr
      have hsquares : rho ^ 2 ≤ centeredCircleLift (x j) ^ 2 := by
        simpa only [abs_of_nonneg hrho, sq_abs] using
          ((sq_le_sq₀ hrho (abs_nonneg _)).2 hj.le)
      have hk : (0 : ℝ) ≤ k := by positivity
      nlinarith

end

end Erdos984
