/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.AdditiveCharacterOrthogonality
import ErdosProblems.Erdos387.RationalWeilProbe
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Cancellation of high rational Artin coefficients

Translation by the derivative probe preserves all values at the poles.  It
therefore preserves the zero/nonzero convention in `polynomialWeight`, while
its logarithmic derivative changes in one nonzero affine direction.  Summing
that translated weight over the prime field gives zero by additive-character
orthogonality.
-/

namespace Erdos387

open Polynomial
open scoped BigOperators

namespace RationalWeil

/-- The nonzero phase direction produced by the selected derivative probe. -/
noncomputable def probeSlope
    {p : ℕ} [NeZero p] (coeff : ZMod p → ZMod p)
    (F : (ZMod p)[X]) (r : ZMod p) : ZMod p :=
  -(coeff r * eval r (derivativeProbe coeff r).derivative *
      (eval r F)⁻¹)

/-- Adding a polynomial which vanishes at every pole changes the logarithmic
derivative only through its derivative values. -/
theorem logarithmicDerivativePhase_add_of_eval_eq_zero
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) (F G : (ZMod p)[X])
    (hG : ∀ s ∈ InverseRational.poleSupport coeff, eval s G = 0) :
    logarithmicDerivativePhase coeff (F + G) =
      logarithmicDerivativePhase coeff F -
        ∑ s ∈ InverseRational.poleSupport coeff,
          coeff s * eval s G.derivative * (eval s F)⁻¹ := by
  classical
  simp only [logarithmicDerivativePhase, derivative_add, eval_add]
  have hsum :
      (∑ s ∈ InverseRational.poleSupport coeff,
          coeff s * (eval s F.derivative + eval s G.derivative) *
            (eval s F + eval s G)⁻¹) =
        (∑ s ∈ InverseRational.poleSupport coeff,
          coeff s * eval s F.derivative * (eval s F)⁻¹) +
        ∑ s ∈ InverseRational.poleSupport coeff,
          coeff s * eval s G.derivative * (eval s F)⁻¹ := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    rw [hG s hs, add_zero]
    ring
  rw [hsum]
  ring

/-- Translation by a scalar multiple of the probe changes the phase by the
corresponding scalar multiple of `probeSlope`. -/
theorem logarithmicDerivativePhase_add_probe
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) (F : (ZMod p)[X])
    {r : ZMod p} (hr : r ∈ InverseRational.poleSupport coeff)
    (t : ZMod p) :
    logarithmicDerivativePhase coeff
        (F + C t * derivativeProbe coeff r) =
      logarithmicDerivativePhase coeff F + t * probeSlope coeff F r := by
  classical
  rw [logarithmicDerivativePhase_add_of_eval_eq_zero coeff F
    (C t * derivativeProbe coeff r) (by
      intro s hs
      simp [eval_derivativeProbe_eq_zero coeff r hs])]
  have hsum :
      (∑ s ∈ InverseRational.poleSupport coeff,
          coeff s * eval s (C t * derivativeProbe coeff r).derivative *
            (eval s F)⁻¹) =
        t * coeff r * eval r (derivativeProbe coeff r).derivative *
          (eval r F)⁻¹ := by
    rw [Finset.sum_eq_single r]
    · simp only [derivative_mul, derivative_C, zero_mul, zero_add,
        eval_mul, eval_C]
      ring
    · intro s hs hsr
      simp only [derivative_mul, derivative_C, zero_mul, zero_add,
        eval_mul, eval_C,
        eval_derivative_derivativeProbe_at_other coeff hr hs hsr,
        mul_zero, zero_mul]
    · exact fun hnot => (hnot hr).elim
  rw [hsum]
  unfold probeSlope
  ring

/-- The selected affine direction is nonzero for every polynomial avoiding
the pole support. -/
theorem probeSlope_ne_zero
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) {F : (ZMod p)[X]} {r : ZMod p}
    (hr : r ∈ InverseRational.poleSupport coeff)
    (hF : AvoidsPoleSupport coeff F) :
    probeSlope coeff F r ≠ 0 := by
  unfold probeSlope
  exact neg_ne_zero.mpr <| mul_ne_zero
    (mul_ne_zero ((InverseRational.mem_poleSupport coeff r).mp hr)
      (eval_derivative_derivativeProbe_at_selected_ne_zero coeff hr))
    (inv_ne_zero (hF r hr))

/-- The weight along a probe line is an affine additive character whenever
the starting polynomial avoids all poles. -/
theorem polynomialWeight_add_probe_of_avoids
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) {F : (ZMod p)[X]} {r : ZMod p}
    (hr : r ∈ InverseRational.poleSupport coeff)
    (hF : AvoidsPoleSupport coeff F) (t : ZMod p) :
    polynomialWeight coeff (F + C t * derivativeProbe coeff r) =
      polynomialWeight coeff F * ZMod.stdAddChar (t * probeSlope coeff F r) := by
  classical
  rw [polynomialWeight, polynomialWeight,
    if_pos hF,
    if_pos ((avoidsPoleSupport_add_C_mul_derivativeProbe_iff
      coeff r t F).2 hF),
    logarithmicDerivativePhase_add_probe coeff F hr t,
    AddChar.map_add_eq_mul]

/-- Every complete affine probe line has total weight zero. -/
theorem sum_polynomialWeight_add_probe_eq_zero
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) (F : (ZMod p)[X])
    {r : ZMod p} (hr : r ∈ InverseRational.poleSupport coeff) :
    ∑ t : ZMod p,
      polynomialWeight coeff (F + C t * derivativeProbe coeff r) = 0 := by
  classical
  by_cases hF : AvoidsPoleSupport coeff F
  · simp_rw [polynomialWeight_add_probe_of_avoids coeff hr hF]
    rw [← Finset.mul_sum,
      AdditiveOrthogonality.sum_stdAddChar_mul p (probeSlope coeff F r),
      if_neg (probeSlope_ne_zero coeff hr hF), mul_zero]
  · apply Finset.sum_eq_zero
    intro t _ht
    rw [polynomialWeight, if_neg]
    exact fun h => hF
      ((avoidsPoleSupport_add_C_mul_derivativeProbe_iff coeff r t F).1 h)

/-! ## Cancellation after summing over monic polynomials -/

/-- The lower-degree polynomial represented by a coefficient vector. -/
noncomputable def lowerPolynomial
    {K : Type*} [Field K] (n : ℕ) (c : Fin n → K) : K[X] :=
  ((degreeLTEquiv K n).symm c).1

/-- The monic polynomial with the prescribed lower coefficient vector. -/
noncomputable def monicPolynomial
    {K : Type*} [Field K] (n : ℕ) (c : Fin n → K) : K[X] :=
  X ^ n + lowerPolynomial n c

theorem lowerPolynomial_mem
    {K : Type*} [Field K] (n : ℕ) (c : Fin n → K) :
    lowerPolynomial n c ∈ degreeLT K n :=
  ((degreeLTEquiv K n).symm c).2

theorem lowerPolynomial_add
    {K : Type*} [Field K] (n : ℕ) (c d : Fin n → K) :
    lowerPolynomial n (c + d) =
      lowerPolynomial n c + lowerPolynomial n d := by
  change (((degreeLTEquiv K n).symm (c + d)).1 : K[X]) = _
  rw [map_add]
  rfl

theorem lowerPolynomial_smul
    {K : Type*} [Field K] (n : ℕ) (t : K) (c : Fin n → K) :
    lowerPolynomial n (t • c) = C t * lowerPolynomial n c := by
  change (((degreeLTEquiv K n).symm (t • c)).1 : K[X]) = _
  rw [map_smul]
  change t • lowerPolynomial n c = C t * lowerPolynomial n c
  exact smul_eq_C_mul t

/-- The coefficient vector of a polynomial known to have degree below `n`. -/
noncomputable def lowerCoefficientVector
    {K : Type*} [Field K] (n : ℕ) (H : K[X])
    (hH : H ∈ degreeLT K n) : Fin n → K :=
  degreeLTEquiv K n ⟨H, hH⟩

theorem lowerPolynomial_lowerCoefficientVector
    {K : Type*} [Field K] (n : ℕ) (H : K[X])
    (hH : H ∈ degreeLT K n) :
    lowerPolynomial n (lowerCoefficientVector n H hH) = H := by
  change (((degreeLTEquiv K n).symm
    (degreeLTEquiv K n ⟨H, hH⟩)).1 : K[X]) = H
  rw [LinearEquiv.symm_apply_apply]

/-- Translating the lower coefficient vector translates the corresponding
monic polynomial by the same lower-degree polynomial. -/
theorem monicPolynomial_add_smul_lowerCoefficientVector
    {K : Type*} [Field K] (n : ℕ) (c : Fin n → K)
    (t : K) (H : K[X]) (hH : H ∈ degreeLT K n) :
    monicPolynomial n
        (c + t • lowerCoefficientVector n H hH) =
      monicPolynomial n c + C t * H := by
  rw [monicPolynomial, monicPolynomial, lowerPolynomial_add,
    lowerPolynomial_smul,
    lowerPolynomial_lowerCoefficientVector n H hH]
  ring

/-- Complete cancellation of the rational Euler weight over monic
polynomials of every degree at least twice the pole count. -/
theorem sum_polynomialWeight_monicPolynomial_eq_zero
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) {n : ℕ}
    (hn : 2 * (InverseRational.poleSupport coeff).card ≤ n)
    (hne : (InverseRational.poleSupport coeff).Nonempty) :
    ∑ c : Fin n → ZMod p,
      polynomialWeight coeff (monicPolynomial n c) = 0 := by
  classical
  obtain ⟨r, hr⟩ := hne
  let H : (ZMod p)[X] := derivativeProbe coeff r
  have hmpos : 0 < (InverseRational.poleSupport coeff).card :=
    Finset.card_pos.mpr ⟨r, hr⟩
  have hHdegree : H.natDegree < n := by
    change (derivativeProbe coeff r).natDegree < n
    rw [natDegree_derivativeProbe coeff hr]
    omega
  have hH : H ∈ degreeLT (ZMod p) n := by
    rw [mem_degreeLT, ← natDegree_lt_iff_degree_lt
      (monic_derivativeProbe coeff r).ne_zero]
    exact hHdegree
  let v : Fin n → ZMod p := lowerCoefficientVector n H hH
  let w : (Fin n → ZMod p) → ℂ := fun c =>
    polynomialWeight coeff (monicPolynomial n c)
  have htranslate (t : ZMod p) :
      (∑ c : Fin n → ZMod p, w (c + t • v)) = ∑ c, w c := by
    let e : (Fin n → ZMod p) ≃ (Fin n → ZMod p) :=
      Equiv.addRight (t • v)
    change (∑ c, w (e c)) = ∑ c, w c
    exact e.sum_comp w
  have hline (c : Fin n → ZMod p) :
      ∑ t : ZMod p, w (c + t • v) = 0 := by
    have hpoly (t : ZMod p) :
        monicPolynomial n (c + t • v) =
          monicPolynomial n c + C t * derivativeProbe coeff r := by
      simpa only [v, H] using
        monicPolynomial_add_smul_lowerCoefficientVector n c t H hH
    simp_rw [w, hpoly]
    exact sum_polynomialWeight_add_probe_eq_zero coeff
      (monicPolynomial n c) hr
  have hpMul :
      (p : ℂ) * (∑ c : Fin n → ZMod p, w c) = 0 := by
    calc
      (p : ℂ) * (∑ c : Fin n → ZMod p, w c) =
          ∑ t : ZMod p, ∑ c : Fin n → ZMod p, w c := by
        simp [ZMod.card]
      _ = ∑ t : ZMod p, ∑ c : Fin n → ZMod p, w (c + t • v) := by
        apply Finset.sum_congr rfl
        intro t _ht
        exact (htranslate t).symm
      _ = ∑ c : Fin n → ZMod p, ∑ t : ZMod p, w (c + t • v) := by
        rw [Finset.sum_comm]
      _ = 0 := by simp only [hline, Finset.sum_const_zero]
  have hpComplex : (p : ℂ) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  exact mul_left_cancel₀ hpComplex (by simpa only [mul_zero] using hpMul)

end RationalWeil

end Erdos387
