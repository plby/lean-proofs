/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Algebra.Order.Chebyshev
import ErdosProblems.Erdos378.VanDerCorput

/-!
# Elementary exponential-sum estimates for Erdős 378

This file develops the finite first-derivative estimate needed in the
Granville--Ramaré reciprocal-phase argument.  It is deliberately stated for
finite sequences; later files specialize it to `x / n` and its iterated
finite differences.
-/

open scoped BigOperators ComplexConjugate

namespace Erdos378
namespace ReciprocalExponential

/-- The analytic-number-theory convention `e(x) = exp(2 π i x)`. -/
noncomputable def e (x : ℝ) : ℂ :=
  Complex.exp (Complex.I * (2 * Real.pi * x))

@[simp] theorem norm_e (x : ℝ) : ‖e x‖ = 1 := by
  rw [e, Complex.norm_exp]
  simp

@[simp] theorem e_add (x y : ℝ) : e (x + y) = e x * e y := by
  unfold e
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

@[simp] theorem e_sub (x y : ℝ) : e (x - y) = e x * conj (e y) := by
  rw [sub_eq_add_neg, e_add]
  congr 1
  unfold e
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_I]
  have hreal : (starRingEnd ℂ)
      (2 * (Real.pi : ℂ) * (y : ℂ)) = 2 * (Real.pi : ℂ) * (y : ℂ) := by
    calc
      (starRingEnd ℂ) (2 * (Real.pi : ℂ) * (y : ℂ)) =
          (starRingEnd ℂ) ((2 * Real.pi * y : ℝ) : ℂ) := by
            congr 2
            push_cast
            rfl
      _ = ((2 * Real.pi * y : ℝ) : ℂ) := Complex.conj_ofReal _
      _ = 2 * (Real.pi : ℂ) * (y : ℂ) := by
        push_cast
        rfl
  rw [hreal]
  push_cast
  ring

/-- On the first half-period, the chord from `1` has a linear lower bound. -/
theorem four_mul_le_norm_e_sub_one {x : ℝ} (hx0 : 0 ≤ x)
    (hxhalf : x ≤ 1 / 2) :
    4 * x ≤ ‖e x - 1‖ := by
  have hnorm := Complex.norm_exp_I_mul_ofReal_sub_one (2 * Real.pi * x)
  have heq : ‖e x - 1‖ =
      ‖Complex.exp (Complex.I * (2 * Real.pi * x : ℝ)) - 1‖ := by
    unfold e
    congr 4
    push_cast
    rfl
  rw [heq, hnorm]
  have hxpi0 : 0 ≤ Real.pi * x := mul_nonneg Real.pi_pos.le hx0
  have hxpihalf : Real.pi * x ≤ Real.pi / 2 := by
    nlinarith [Real.pi_pos]
  have hsin := Real.mul_le_sin hxpi0 hxpihalf
  have hsin0 : 0 ≤ Real.sin (Real.pi * x) :=
    (mul_nonneg (by positivity : 0 ≤ (2 : ℝ) / Real.pi) hxpi0).trans hsin
  have hcollapse : 2 / Real.pi * (Real.pi * x) = 2 * x := by
    field_simp
  rw [show (2 * Real.pi * x) / 2 = Real.pi * x by ring]
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hsin0)]
  rw [hcollapse] at hsin
  nlinarith

/-- The standard additive character is globally Lipschitz, with a deliberately
coarse rational constant convenient for later estimates. -/
theorem norm_e_sub_e_le_eight_mul_abs_sub (x y : ℝ) :
    ‖e x - e y‖ ≤ 8 * |x - y| := by
  have hfactor : e x - e y = e y * (e (x - y) - 1) := by
    rw [mul_sub, mul_one, ← e_add]
    congr 2
    ring
  rw [hfactor, norm_mul, norm_e, one_mul]
  have hphase := Real.norm_exp_I_mul_ofReal_sub_one_le
    (x := 2 * Real.pi * (x - y))
  have heq : ‖e (x - y) - 1‖ =
      ‖Complex.exp (Complex.I * (2 * Real.pi * (x - y) : ℝ)) - 1‖ := by
    unfold e
    congr 4
    push_cast
    rfl
  rw [heq]
  calc
    ‖Complex.exp (Complex.I * (2 * Real.pi * (x - y) : ℝ)) - 1‖ ≤
        ‖2 * Real.pi * (x - y)‖ := hphase
    _ = 2 * Real.pi * |x - y| := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_pos Real.pi_pos]
    _ ≤ 8 * |x - y| := by
      gcongr
      linarith [Real.pi_le_four]

/-- Coefficient used to turn one phase term into a first difference. -/
noncomputable def phaseCoeff (x : ℝ) : ℂ := (e x - 1)⁻¹

theorem e_sub_one_ne_zero {x : ℝ} (hx : 0 < x) (hxhalf : x ≤ 1 / 2) :
    e x - 1 ≠ 0 := by
  intro hzero
  have hnormzero : ‖e x - 1‖ = 0 := by rw [hzero, norm_zero]
  have hlower := four_mul_le_norm_e_sub_one hx.le hxhalf
  rw [hnormzero] at hlower
  nlinarith

/-- Uniform inverse-chord bound away from the integral phase. -/
theorem norm_phaseCoeff_le {m x : ℝ} (hm : 0 < m) (hmx : m ≤ x)
    (hxhalf : x ≤ 1 / 2) :
    ‖phaseCoeff x‖ ≤ 1 / (4 * m) := by
  have hx : 0 < x := hm.trans_le hmx
  have hlower := four_mul_le_norm_e_sub_one hx.le hxhalf
  have hdenpos : 0 < ‖e x - 1‖ := norm_pos_iff.mpr (e_sub_one_ne_zero hx hxhalf)
  unfold phaseCoeff
  rw [norm_inv, one_div]
  apply (inv_le_inv₀ hdenpos (by positivity : 0 < 4 * m)).2
  exact (mul_le_mul_of_nonneg_left hmx (by norm_num : (0 : ℝ) ≤ 4)).trans hlower

/-- The inverse-chord coefficient has controlled variation on `[m,1/2]`. -/
theorem norm_phaseCoeff_sub_le {m x y : ℝ} (hm : 0 < m)
    (hmx : m ≤ x) (hmy : m ≤ y) (hxhalf : x ≤ 1 / 2)
    (hyhalf : y ≤ 1 / 2) :
    ‖phaseCoeff x - phaseCoeff y‖ ≤
      8 * |x - y| * (1 / (4 * m)) ^ 2 := by
  have hx : 0 < x := hm.trans_le hmx
  have hy : 0 < y := hm.trans_le hmy
  have hdx : e x - 1 ≠ 0 := e_sub_one_ne_zero hx hxhalf
  have hdy : e y - 1 ≠ 0 := e_sub_one_ne_zero hy hyhalf
  have hcx := norm_phaseCoeff_le hm hmx hxhalf
  have hcy := norm_phaseCoeff_le hm hmy hyhalf
  have hchar := norm_e_sub_e_le_eight_mul_abs_sub y x
  unfold phaseCoeff
  rw [inv_sub_inv' hdx hdy, norm_mul, norm_mul]
  calc
    ‖(e x - 1)⁻¹‖ * ‖(e y - 1) - (e x - 1)‖ * ‖(e y - 1)⁻¹‖ ≤
        (1 / (4 * m)) * (8 * |x - y|) * (1 / (4 * m)) := by
          rw [show (e y - 1) - (e x - 1) = e y - e x by ring]
          rw [abs_sub_comm y x] at hchar
          change ‖(e x - 1)⁻¹‖ ≤ 1 / (4 * m) at hcx
          change ‖(e y - 1)⁻¹‖ ≤ 1 / (4 * m) at hcy
          gcongr
    _ = 8 * |x - y| * (1 / (4 * m)) ^ 2 := by ring

/-- When the two phase gaps are ordered, the inverse-chord variation is
bounded by a telescoping difference of reciprocals.  This sharper form is
what changes the first-derivative estimate from a quadratic to a linear
loss in the minimum gap. -/
theorem norm_phaseCoeff_sub_le_inv_sub {x y : ℝ}
    (hy : 0 < y) (hyx : y ≤ x) (hxhalf : x ≤ 1 / 2) :
    ‖phaseCoeff y - phaseCoeff x‖ ≤ (1 / y - 1 / x) / 2 := by
  have hx : 0 < x := hy.trans_le hyx
  have hyhalf : y ≤ 1 / 2 := hyx.trans hxhalf
  have hdy : e y - 1 ≠ 0 := e_sub_one_ne_zero hy hyhalf
  have hdx : e x - 1 ≠ 0 := e_sub_one_ne_zero hx hxhalf
  have hcy : ‖phaseCoeff y‖ ≤ 1 / (4 * y) :=
    norm_phaseCoeff_le hy le_rfl hyhalf
  have hcx : ‖phaseCoeff x‖ ≤ 1 / (4 * x) :=
    norm_phaseCoeff_le hx le_rfl hxhalf
  have hchar := norm_e_sub_e_le_eight_mul_abs_sub x y
  have habs : |x - y| = x - y := abs_of_nonneg (sub_nonneg.mpr hyx)
  rw [habs] at hchar
  unfold phaseCoeff
  rw [inv_sub_inv' hdy hdx, norm_mul, norm_mul]
  have hmiddle : ‖(e x - 1) - (e y - 1)‖ ≤ 8 * (x - y) := by
    simpa [show (e x - 1) - (e y - 1) = e x - e y by ring] using hchar
  have hbound :
      ‖(e y - 1)⁻¹‖ * ‖(e x - 1) - (e y - 1)‖ * ‖(e x - 1)⁻¹‖ ≤
        (1 / (4 * y)) * (8 * (x - y)) * (1 / (4 * x)) := by
    change ‖phaseCoeff y‖ * ‖(e x - 1) - (e y - 1)‖ *
      ‖phaseCoeff x‖ ≤ _
    gcongr
  calc
    ‖(e y - 1)⁻¹‖ * ‖(e x - 1) - (e y - 1)‖ * ‖(e x - 1)⁻¹‖ ≤
        (1 / (4 * y)) * (8 * (x - y)) * (1 / (4 * x)) := hbound
    _ = (1 / y - 1 / x) / 2 := by
      field_simp
      ring

/-- Telescoping sum of consecutive differences in a real sequence. -/
theorem sum_real_succ_sub (a : ℕ → ℝ) (j : ℕ) :
    (∑ i ∈ Finset.range j, (a (i + 1) - a i)) = a j - a 0 := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Finset.sum_range_succ, ih]
      ring

theorem phaseCoeff_mul_e_sub_one {x : ℝ} (hx : 0 < x)
    (hxhalf : x ≤ 1 / 2) :
    phaseCoeff x * (e x - 1) = 1 := by
  unfold phaseCoeff
  exact inv_mul_cancel₀ (e_sub_one_ne_zero hx hxhalf)

/-- Each phase term is an inverse-chord coefficient times the next first
difference. -/
theorem e_eq_phaseCoeff_mul_sub (f : ℕ → ℝ) (i : ℕ)
    (hpos : 0 < f (i + 1) - f i) (hhalf : f (i + 1) - f i ≤ 1 / 2) :
    e (f i) = phaseCoeff (f (i + 1) - f i) *
      (e (f (i + 1)) - e (f i)) := by
  have hnext : e (f (i + 1)) = e (f i) * e (f (i + 1) - f i) := by
    rw [← e_add]
    congr 1
    ring
  rw [hnext, show e (f i) * e (f (i + 1) - f i) - e (f i) =
      e (f i) * (e (f (i + 1) - f i) - 1) by ring]
  calc
    e (f i) = e (f i) * 1 := (mul_one _).symm
    _ = e (f i) *
        (phaseCoeff (f (i + 1) - f i) *
          (e (f (i + 1) - f i) - 1)) := by
            rw [phaseCoeff_mul_e_sub_one hpos hhalf]
    _ = phaseCoeff (f (i + 1) - f i) *
        (e (f i) * (e (f (i + 1) - f i) - 1)) := by ring

/-- Telescoping sum of consecutive first differences. -/
theorem sum_phaseDifferences (z : ℕ → ℂ) (j : ℕ) :
    (∑ i ∈ Finset.range j, (z (i + 1) - z i)) = z j - z 0 := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- Exact summation-by-parts identity behind the first-derivative estimate. -/
theorem sum_e_eq_boundary_sub_variation (f : ℕ → ℝ) (N : ℕ) (hN : 2 ≤ N)
    (hpos : ∀ i < N - 1, 0 < f (i + 1) - f i)
    (hhalf : ∀ i < N - 1, f (i + 1) - f i ≤ 1 / 2) :
    (∑ i ∈ Finset.range N, e (f i)) =
      e (f (N - 1)) +
        phaseCoeff (f (N - 1) - f (N - 2)) *
          (e (f (N - 1)) - e (f 0)) -
        ∑ i ∈ Finset.range (N - 2),
          (phaseCoeff (f (i + 2) - f (i + 1)) -
            phaseCoeff (f (i + 1) - f i)) *
          (e (f (i + 1)) - e (f 0)) := by
  let z : ℕ → ℂ := fun i ↦ e (f i)
  let c : ℕ → ℂ := fun i ↦ phaseCoeff (f (i + 1) - f i)
  let g : ℕ → ℂ := fun i ↦ z (i + 1) - z i
  have hterm : ∀ i < N - 1, z i = c i * g i := by
    intro i hi
    exact e_eq_phaseCoeff_mul_sub f i (hpos i hi) (hhalf i hi)
  have hsum : (∑ i ∈ Finset.range (N - 1), z i) =
      ∑ i ∈ Finset.range (N - 1), c i * g i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hterm i (Finset.mem_range.mp hi)
  have hparts := Finset.sum_range_by_parts c g (N - 1)
  simp only [smul_eq_mul] at hparts
  have htel : ∀ j : ℕ, (∑ i ∈ Finset.range j, g i) = z j - z 0 := by
    intro j
    exact sum_phaseDifferences z j
  have hsub : N - 1 - 1 = N - 2 := by omega
  have hsucc : N - 1 + 1 = N := by omega
  calc
    (∑ i ∈ Finset.range N, e (f i)) =
        (∑ i ∈ Finset.range (N - 1), z i) + z (N - 1) := by
          rw [← Finset.sum_range_succ]
          rw [hsucc]
    _ = (∑ i ∈ Finset.range (N - 1), c i * g i) + z (N - 1) := by rw [hsum]
    _ = (c (N - 2) * (z (N - 1) - z 0) -
          ∑ i ∈ Finset.range (N - 2),
            (c (i + 1) - c i) * (z (i + 1) - z 0)) + z (N - 1) := by
          rw [hparts, hsub]
          simp_rw [htel]
    _ = _ := by
      dsimp [z, c]
      rw [show N - 2 + 1 = N - 1 by omega]
      simp_rw [show ∀ i : ℕ, i + 1 + 1 = i + 2 by omega]
      ring

/-- Total variation of an antitone finite real sequence telescopes. -/
theorem sum_abs_succ_sub_of_antitone (a : ℕ → ℝ) (hanti : Antitone a)
    (L : ℕ) :
    (∑ i ∈ Finset.range L, |a (i + 1) - a i|) = a 0 - a L := by
  induction L with
  | zero => simp
  | succ L ih =>
      rw [Finset.sum_range_succ, ih]
      rw [abs_of_nonpos (sub_nonpos.mpr (hanti (Nat.le_succ L)))]
      ring

/-- The accumulated inverse-chord variation for an antitone phase derivative. -/
theorem sum_norm_phaseCoeff_variation_le (f : ℕ → ℝ) (N : ℕ) (hN : 2 ≤ N)
    (m : ℝ) (hm : 0 < m)
    (hlower : ∀ i < N - 1, m ≤ f (i + 1) - f i)
    (hupper : ∀ i < N - 1, f (i + 1) - f i ≤ 1 / 2)
    (hanti : Antitone (fun i ↦ f (i + 1) - f i)) :
    (∑ i ∈ Finset.range (N - 2),
      ‖phaseCoeff (f (i + 2) - f (i + 1)) -
        phaseCoeff (f (i + 1) - f i)‖) ≤
      (8 * (1 / (4 * m)) ^ 2) / 2 := by
  let d : ℕ → ℝ := fun i ↦ f (i + 1) - f i
  let C : ℝ := 8 * (1 / (4 * m)) ^ 2
  have hpoint : ∀ i < N - 2,
      ‖phaseCoeff (d (i + 1)) - phaseCoeff (d i)‖ ≤
        C * |d (i + 1) - d i| := by
    intro i hi
    have hi0 : i < N - 1 := by omega
    have hi1 : i + 1 < N - 1 := by omega
    have h := norm_phaseCoeff_sub_le hm (hlower (i + 1) hi1)
      (hlower i hi0) (hupper (i + 1) hi1) (hupper i hi0)
    dsimp [C, d]
    convert h using 1 <;> ring
  have hsum : (∑ i ∈ Finset.range (N - 2),
      ‖phaseCoeff (d (i + 1)) - phaseCoeff (d i)‖) ≤
      ∑ i ∈ Finset.range (N - 2), C * |d (i + 1) - d i| := by
    exact Finset.sum_le_sum fun i hi ↦ hpoint i (Finset.mem_range.mp hi)
  have hvariation : (∑ i ∈ Finset.range (N - 2),
      |d (i + 1) - d i|) = d 0 - d (N - 2) :=
    sum_abs_succ_sub_of_antitone d hanti (N - 2)
  have hC : 0 ≤ C := by positivity
  have hlast : 0 ≤ d (N - 2) := by
    have hidx : N - 2 < N - 1 := by omega
    exact (hm.trans_le (hlower (N - 2) hidx)).le
  have hfirst : d 0 ≤ 1 / 2 := hupper 0 (by omega)
  calc
    (∑ i ∈ Finset.range (N - 2),
      ‖phaseCoeff (f (i + 2) - f (i + 1)) -
        phaseCoeff (f (i + 1) - f i)‖) =
        ∑ i ∈ Finset.range (N - 2),
          ‖phaseCoeff (d (i + 1)) - phaseCoeff (d i)‖ := by rfl
    _ ≤ ∑ i ∈ Finset.range (N - 2), C * |d (i + 1) - d i| := hsum
    _ = C * (d 0 - d (N - 2)) := by
      rw [← Finset.mul_sum, hvariation]
    _ ≤ C * (1 / 2) := by gcongr <;> linarith
    _ = (8 * (1 / (4 * m)) ^ 2) / 2 := by
      dsimp [C]
      ring

/-- Sharper accumulated inverse-chord variation.  Monotonicity makes the
reciprocal gaps telescope, leaving only a linear inverse-gap loss. -/
theorem sum_norm_phaseCoeff_variation_le_inv (f : ℕ → ℝ) (N : ℕ)
    (hN : 2 ≤ N) (m : ℝ) (hm : 0 < m)
    (hlower : ∀ i < N - 1, m ≤ f (i + 1) - f i)
    (hupper : ∀ i < N - 1, f (i + 1) - f i ≤ 1 / 2)
    (hanti : Antitone (fun i ↦ f (i + 1) - f i)) :
    (∑ i ∈ Finset.range (N - 2),
      ‖phaseCoeff (f (i + 2) - f (i + 1)) -
        phaseCoeff (f (i + 1) - f i)‖) ≤ 1 / (2 * m) := by
  let d : ℕ → ℝ := fun i ↦ f (i + 1) - f i
  have hpoint : ∀ i < N - 2,
      ‖phaseCoeff (d (i + 1)) - phaseCoeff (d i)‖ ≤
        (1 / d (i + 1) - 1 / d i) / 2 := by
    intro i hi
    have hi0 : i < N - 1 := by omega
    have hi1 : i + 1 < N - 1 := by omega
    apply norm_phaseCoeff_sub_le_inv_sub
    · exact hm.trans_le (hlower (i + 1) hi1)
    · exact hanti (Nat.le_succ i)
    · exact hupper i hi0
  have hsum :
      (∑ i ∈ Finset.range (N - 2),
        ‖phaseCoeff (d (i + 1)) - phaseCoeff (d i)‖) ≤
      ∑ i ∈ Finset.range (N - 2),
        (1 / d (i + 1) - 1 / d i) / 2 := by
    exact Finset.sum_le_sum fun i hi ↦ hpoint i (Finset.mem_range.mp hi)
  have htel :
      (∑ i ∈ Finset.range (N - 2),
        (1 / d (i + 1) - 1 / d i) / 2) =
        (1 / d (N - 2) - 1 / d 0) / 2 := by
    simp only [div_eq_mul_inv, one_mul]
    rw [← Finset.sum_mul,
      sum_real_succ_sub (fun i ↦ (d i)⁻¹) (N - 2)]
  have hlastIdx : N - 2 < N - 1 := by omega
  have hdlast : m ≤ d (N - 2) := hlower (N - 2) hlastIdx
  have hdlastPos : 0 < d (N - 2) := hm.trans_le hdlast
  have hinvlast : 1 / d (N - 2) ≤ 1 / m := by
    exact one_div_le_one_div_of_le hm hdlast
  have hd0 : 0 < d 0 := hm.trans_le (hlower 0 (by omega))
  have hinv0 : 0 ≤ 1 / d 0 := by positivity
  have hfinal : (1 / d (N - 2) - 1 / d 0) / 2 ≤ 1 / (2 * m) := by
    have heq : 1 / (2 * m) = (1 / m) / 2 := by
      field_simp
    rw [heq]
    linarith
  calc
    (∑ i ∈ Finset.range (N - 2),
      ‖phaseCoeff (f (i + 2) - f (i + 1)) -
        phaseCoeff (f (i + 1) - f i)‖) =
        ∑ i ∈ Finset.range (N - 2),
          ‖phaseCoeff (d (i + 1)) - phaseCoeff (d i)‖ := by rfl
    _ ≤ ∑ i ∈ Finset.range (N - 2),
        (1 / d (i + 1) - 1 / d i) / 2 := hsum
    _ = (1 / d (N - 2) - 1 / d 0) / 2 := htel
    _ ≤ 1 / (2 * m) := hfinal

/-- A finite Kusmin--Landau first-derivative estimate.  The constants are
coarser than the classical cotangent bound, but the dependence on the
derivative gap is explicit and is sufficient for iterated differencing. -/
theorem norm_sum_e_le_of_antitone_phaseDiff (f : ℕ → ℝ) (N : ℕ)
    (hN : 2 ≤ N) (m : ℝ) (hm : 0 < m)
    (hlower : ∀ i < N - 1, m ≤ f (i + 1) - f i)
    (hupper : ∀ i < N - 1, f (i + 1) - f i ≤ 1 / 2)
    (hanti : Antitone (fun i ↦ f (i + 1) - f i)) :
    ‖∑ i ∈ Finset.range N, e (f i)‖ ≤
      1 + 2 * (1 / (4 * m)) + 8 * (1 / (4 * m)) ^ 2 := by
  let C : ℝ := 1 / (4 * m)
  let D : ℝ := 8 * C ^ 2
  have hidx : N - 2 < N - 1 := by omega
  have hboundary :
      ‖phaseCoeff (f (N - 1) - f (N - 2)) *
        (e (f (N - 1)) - e (f 0))‖ ≤ 2 * C := by
    rw [norm_mul]
    have hc : ‖phaseCoeff (f (N - 1) - f (N - 2))‖ ≤ C := by
      have h := norm_phaseCoeff_le hm (hlower (N - 2) hidx)
        (hupper (N - 2) hidx)
      simpa [C, show N - 2 + 1 = N - 1 by omega] using h
    have hz : ‖e (f (N - 1)) - e (f 0)‖ ≤ 2 := by
      calc
        ‖e (f (N - 1)) - e (f 0)‖ ≤
            ‖e (f (N - 1))‖ + ‖e (f 0)‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_e, norm_e]; norm_num
    calc
      ‖phaseCoeff (f (N - 1) - f (N - 2))‖ *
          ‖e (f (N - 1)) - e (f 0)‖ ≤ C * 2 := by gcongr
      _ = 2 * C := by ring
  have hcoeff :
      (∑ i ∈ Finset.range (N - 2),
        ‖phaseCoeff (f (i + 2) - f (i + 1)) -
          phaseCoeff (f (i + 1) - f i)‖) ≤ D / 2 := by
    have h := sum_norm_phaseCoeff_variation_le f N hN m hm hlower hupper hanti
    simpa [D, C] using h
  have hvariation :
      ‖∑ i ∈ Finset.range (N - 2),
        (phaseCoeff (f (i + 2) - f (i + 1)) -
          phaseCoeff (f (i + 1) - f i)) *
        (e (f (i + 1)) - e (f 0))‖ ≤ D := by
    calc
      ‖∑ i ∈ Finset.range (N - 2),
        (phaseCoeff (f (i + 2) - f (i + 1)) -
          phaseCoeff (f (i + 1) - f i)) *
        (e (f (i + 1)) - e (f 0))‖ ≤
          ∑ i ∈ Finset.range (N - 2),
            ‖(phaseCoeff (f (i + 2) - f (i + 1)) -
              phaseCoeff (f (i + 1) - f i)) *
              (e (f (i + 1)) - e (f 0))‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range (N - 2),
          2 * ‖phaseCoeff (f (i + 2) - f (i + 1)) -
            phaseCoeff (f (i + 1) - f i)‖ := by
            apply Finset.sum_le_sum
            intro i hi
            rw [norm_mul]
            have hz : ‖e (f (i + 1)) - e (f 0)‖ ≤ 2 := by
              calc
                ‖e (f (i + 1)) - e (f 0)‖ ≤
                    ‖e (f (i + 1))‖ + ‖e (f 0)‖ := norm_sub_le _ _
                _ = 2 := by rw [norm_e, norm_e]; norm_num
            nlinarith [norm_nonneg
              (phaseCoeff (f (i + 2) - f (i + 1)) -
                phaseCoeff (f (i + 1) - f i))]
      _ = 2 * (∑ i ∈ Finset.range (N - 2),
          ‖phaseCoeff (f (i + 2) - f (i + 1)) -
            phaseCoeff (f (i + 1) - f i)‖) := by
              rw [Finset.mul_sum]
      _ ≤ 2 * (D / 2) := by gcongr
      _ = D := by ring
  rw [sum_e_eq_boundary_sub_variation f N hN
    (fun i hi ↦ hm.trans_le (hlower i hi)) hupper]
  calc
    ‖e (f (N - 1)) +
          phaseCoeff (f (N - 1) - f (N - 2)) *
            (e (f (N - 1)) - e (f 0)) -
        ∑ i ∈ Finset.range (N - 2),
          (phaseCoeff (f (i + 2) - f (i + 1)) -
            phaseCoeff (f (i + 1) - f i)) *
          (e (f (i + 1)) - e (f 0))‖ ≤
        ‖e (f (N - 1)) +
          phaseCoeff (f (N - 1) - f (N - 2)) *
            (e (f (N - 1)) - e (f 0))‖ +
        ‖∑ i ∈ Finset.range (N - 2),
          (phaseCoeff (f (i + 2) - f (i + 1)) -
            phaseCoeff (f (i + 1) - f i)) *
          (e (f (i + 1)) - e (f 0))‖ := norm_sub_le _ _
    _ ≤ (‖e (f (N - 1))‖ +
        ‖phaseCoeff (f (N - 1) - f (N - 2)) *
          (e (f (N - 1)) - e (f 0))‖) + D := by
            gcongr
            exact norm_add_le _ _
    _ ≤ (1 + 2 * C) + D := by
      rw [norm_e]
      gcongr
    _ = 1 + 2 * (1 / (4 * m)) + 8 * (1 / (4 * m)) ^ 2 := by
      dsimp [C, D]

/-- Sharpened finite Kusmin--Landau estimate.  The dependence on the
minimum phase gap is linear, as in the classical first-derivative test. -/
theorem norm_sum_e_le_of_antitone_phaseDiff_sharp (f : ℕ → ℝ) (N : ℕ)
    (hN : 2 ≤ N) (m : ℝ) (hm : 0 < m)
    (hlower : ∀ i < N - 1, m ≤ f (i + 1) - f i)
    (hupper : ∀ i < N - 1, f (i + 1) - f i ≤ 1 / 2)
    (hanti : Antitone (fun i ↦ f (i + 1) - f i)) :
    ‖∑ i ∈ Finset.range N, e (f i)‖ ≤ 1 + 3 / (2 * m) := by
  have hidx : N - 2 < N - 1 := by omega
  have hboundary :
      ‖phaseCoeff (f (N - 1) - f (N - 2)) *
        (e (f (N - 1)) - e (f 0))‖ ≤ 1 / (2 * m) := by
    rw [norm_mul]
    have hc : ‖phaseCoeff (f (N - 1) - f (N - 2))‖ ≤
        1 / (4 * m) := by
      have h := norm_phaseCoeff_le hm (hlower (N - 2) hidx)
        (hupper (N - 2) hidx)
      simpa [show N - 2 + 1 = N - 1 by omega] using h
    have hz : ‖e (f (N - 1)) - e (f 0)‖ ≤ 2 := by
      calc
        ‖e (f (N - 1)) - e (f 0)‖ ≤
            ‖e (f (N - 1))‖ + ‖e (f 0)‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_e, norm_e]; norm_num
    calc
      ‖phaseCoeff (f (N - 1) - f (N - 2))‖ *
          ‖e (f (N - 1)) - e (f 0)‖ ≤ (1 / (4 * m)) * 2 := by
            gcongr
      _ = 1 / (2 * m) := by field_simp <;> norm_num
  have hcoeff := sum_norm_phaseCoeff_variation_le_inv
    f N hN m hm hlower hupper hanti
  have hvariation :
      ‖∑ i ∈ Finset.range (N - 2),
        (phaseCoeff (f (i + 2) - f (i + 1)) -
          phaseCoeff (f (i + 1) - f i)) *
        (e (f (i + 1)) - e (f 0))‖ ≤ 1 / m := by
    calc
      ‖∑ i ∈ Finset.range (N - 2),
        (phaseCoeff (f (i + 2) - f (i + 1)) -
          phaseCoeff (f (i + 1) - f i)) *
        (e (f (i + 1)) - e (f 0))‖ ≤
          ∑ i ∈ Finset.range (N - 2),
            ‖(phaseCoeff (f (i + 2) - f (i + 1)) -
              phaseCoeff (f (i + 1) - f i)) *
              (e (f (i + 1)) - e (f 0))‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range (N - 2),
          2 * ‖phaseCoeff (f (i + 2) - f (i + 1)) -
            phaseCoeff (f (i + 1) - f i)‖ := by
            apply Finset.sum_le_sum
            intro i hi
            rw [norm_mul]
            have hz : ‖e (f (i + 1)) - e (f 0)‖ ≤ 2 := by
              calc
                ‖e (f (i + 1)) - e (f 0)‖ ≤
                    ‖e (f (i + 1))‖ + ‖e (f 0)‖ := norm_sub_le _ _
                _ = 2 := by rw [norm_e, norm_e]; norm_num
            nlinarith [norm_nonneg
              (phaseCoeff (f (i + 2) - f (i + 1)) -
                phaseCoeff (f (i + 1) - f i))]
      _ = 2 * (∑ i ∈ Finset.range (N - 2),
          ‖phaseCoeff (f (i + 2) - f (i + 1)) -
            phaseCoeff (f (i + 1) - f i)‖) := by
              rw [Finset.mul_sum]
      _ ≤ 2 * (1 / (2 * m)) := by gcongr
      _ = 1 / m := by field_simp
  rw [sum_e_eq_boundary_sub_variation f N hN
    (fun i hi ↦ hm.trans_le (hlower i hi)) hupper]
  calc
    ‖e (f (N - 1)) +
          phaseCoeff (f (N - 1) - f (N - 2)) *
            (e (f (N - 1)) - e (f 0)) -
        ∑ i ∈ Finset.range (N - 2),
          (phaseCoeff (f (i + 2) - f (i + 1)) -
            phaseCoeff (f (i + 1) - f i)) *
          (e (f (i + 1)) - e (f 0))‖ ≤
        ‖e (f (N - 1))‖ +
          ‖phaseCoeff (f (N - 1) - f (N - 2)) *
            (e (f (N - 1)) - e (f 0))‖ +
          ‖∑ i ∈ Finset.range (N - 2),
            (phaseCoeff (f (i + 2) - f (i + 1)) -
              phaseCoeff (f (i + 1) - f i)) *
            (e (f (i + 1)) - e (f 0))‖ := by
              calc
                ‖e (f (N - 1)) +
                    phaseCoeff (f (N - 1) - f (N - 2)) *
                      (e (f (N - 1)) - e (f 0)) - _‖ ≤
                    ‖e (f (N - 1)) +
                      phaseCoeff (f (N - 1) - f (N - 2)) *
                        (e (f (N - 1)) - e (f 0))‖ + _ := norm_sub_le _ _
                _ ≤ _ := by gcongr; exact norm_add_le _ _
    _ ≤ 1 + 1 / (2 * m) + 1 / m := by
      rw [norm_e]
      gcongr
    _ = 1 + 3 / (2 * m) := by field_simp; ring

/-! ## The reciprocal phase -/

/-- The phase `-X/(A+i)` on a translated finite interval. -/
noncomputable def reciprocalPhase (X : ℝ) (A i : ℕ) : ℝ :=
  -X / (A + i : ℕ)

theorem reciprocalPhase_succ_sub (X : ℝ) {A : ℕ} (hA : 0 < A) (i : ℕ) :
    reciprocalPhase X A (i + 1) - reciprocalPhase X A i =
      X / (((A + i : ℕ) : ℝ) * ((A + i + 1 : ℕ) : ℝ)) := by
  unfold reciprocalPhase
  have hAi : (((A + i : ℕ) : ℝ)) ≠ 0 := by positivity
  have hAi1 : (((A + i + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

theorem reciprocalPhaseDiff_antitone (X : ℝ) (hX : 0 ≤ X)
    {A : ℕ} (hA : 0 < A) :
    Antitone (fun i ↦ reciprocalPhase X A (i + 1) - reciprocalPhase X A i) := by
  intro i j hij
  change reciprocalPhase X A (j + 1) - reciprocalPhase X A j ≤
    reciprocalPhase X A (i + 1) - reciprocalPhase X A i
  rw [reciprocalPhase_succ_sub X hA, reciprocalPhase_succ_sub X hA]
  apply div_le_div_of_nonneg_left hX
  · positivity
  · have h1 : (((A + i : ℕ) : ℝ)) ≤ ((A + j : ℕ) : ℝ) := by exact_mod_cast Nat.add_le_add_left hij A
    have h2 : (((A + i + 1 : ℕ) : ℝ)) ≤ ((A + j + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.add_le_add_right (Nat.add_le_add_left hij A) 1
    exact mul_le_mul h1 h2 (by positivity) (by positivity)

/-- Lower reciprocal derivative bound on a finite interval. -/
theorem reciprocalPhaseDiff_lower (X : ℝ) (hX : 0 ≤ X)
    {A N i : ℕ} (hA : 0 < A) (hi : i < N - 1) :
    X / (((A + N : ℕ) : ℝ) ^ 2) ≤
      reciprocalPhase X A (i + 1) - reciprocalPhase X A i := by
  rw [reciprocalPhase_succ_sub X hA]
  apply div_le_div_of_nonneg_left hX
  · positivity
  · have hiN : i + 1 ≤ N := by omega
    have hiN' : i ≤ N := by omega
    have h1 : (((A + i : ℕ) : ℝ)) ≤ ((A + N : ℕ) : ℝ) := by
      exact_mod_cast Nat.add_le_add_left hiN' A
    have h2 : (((A + i + 1 : ℕ) : ℝ)) ≤ ((A + N : ℕ) : ℝ) := by
      exact_mod_cast Nat.add_le_add_left hiN A
    simpa [pow_two] using mul_le_mul h1 h2 (by positivity) (by positivity)

/-- Upper reciprocal derivative bound inherited from the left endpoint. -/
theorem reciprocalPhaseDiff_upper (X : ℝ) (hX : 0 ≤ X)
    {A i : ℕ} (hA : 0 < A) :
    reciprocalPhase X A (i + 1) - reciprocalPhase X A i ≤
      X / ((A : ℝ) ^ 2) := by
  rw [reciprocalPhase_succ_sub X hA]
  apply div_le_div_of_nonneg_left hX
  · positivity
  · have h1 : (A : ℝ) ≤ ((A + i : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_add_right A i
    have h2 : (A : ℝ) ≤ ((A + i + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show A ≤ A + i + 1 by omega)
    simpa [pow_two] using mul_le_mul h1 h2 (by positivity) (by positivity)

/-- Reciprocal exponential-sum estimate on a translated interval.  This is a
coarse, fully finite version of Granville--Ramaré Proposition 8.1(a). -/
theorem norm_sum_e_reciprocalPhase_le (X : ℝ) {A N : ℕ}
    (hX : 0 < X) (hA : 0 < A) (hN : 2 ≤ N)
    (hsmall : X / ((A : ℝ) ^ 2) ≤ 1 / 2) :
    ‖∑ i ∈ Finset.range N, e (reciprocalPhase X A i)‖ ≤
      1 + 2 * (1 / (4 * (X / (((A + N : ℕ) : ℝ) ^ 2)))) +
        8 * (1 / (4 * (X / (((A + N : ℕ) : ℝ) ^ 2)))) ^ 2 := by
  apply norm_sum_e_le_of_antitone_phaseDiff
      (reciprocalPhase X A) N hN
      (X / (((A + N : ℕ) : ℝ) ^ 2))
  · positivity
  · intro i hi
    exact reciprocalPhaseDiff_lower X hX.le hA hi
  · intro i hi
    exact (reciprocalPhaseDiff_upper X hX.le hA).trans hsmall
  · exact reciprocalPhaseDiff_antitone X hX.le hA

/-! ## A norm-only van der Corput inequality -/

/-- Reindex the positive integer interval `1, ..., N` by a zero-based
range. -/
theorem sum_Icc_one_eq_sum_range {R : Type*} [AddCommMonoid R]
    (F : ℕ → R) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, F n) = ∑ i ∈ Finset.range N, F (i + 1) := by
  classical
  have hset : Finset.Icc 1 N =
      (Finset.range N).image (fun i : ℕ ↦ i + 1) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · intro hn
      exact ⟨n - 1, by omega, by omega⟩
    · rintro ⟨i, hi, rfl⟩
      omega
  rw [hset, Finset.sum_image (fun i _hi j _hj hij ↦ by omega)]

/-- A convenient norm-only consequence of van der Corput's fundamental
inequality.  All terms of `u` in the summation interval have norm at most
one; the real parts of the correlations are replaced by their norms.  This
is the form that can be iterated without carrying signs of correlations. -/
theorem vdc_norm_sq_mul_le (u : ℕ → ℂ) {N L : ℕ}
    (hL : 1 ≤ L) (hLN : L ≤ N)
    (hu : ∀ n ∈ Finset.Icc 1 N, ‖u n‖ ≤ 1) :
    (L : ℝ) ^ 2 * ‖∑ n ∈ Finset.Icc 1 N, u n‖ ^ 2 ≤
      2 * (L : ℝ) * (N : ℝ) ^ 2 +
        4 * (N : ℝ) * (L : ℝ) *
          ∑ ℓ ∈ Finset.Icc 1 (L - 1),
            ‖∑ n ∈ Finset.Icc 1 (N - ℓ),
              u n * conj (u (n + ℓ))‖ := by
  have hN : 1 ≤ N := hL.trans hLN
  have hfund := vanDerCorput_fundamental_inequality 1 N (by omega) u L
    (by simpa using hL) (by simpa using hLN)
  have hspan :
      (N : ℝ) + (1 : ℝ) * ((L : ℝ) - 1) ≤ 2 * (N : ℝ) := by
    have hLR : (L : ℝ) ≤ N := by exact_mod_cast hLN
    nlinarith
  have henergy :
      (∑ n ∈ Finset.Icc 1 N, ‖u n‖ ^ 2) ≤ (N : ℝ) := by
    calc
      (∑ n ∈ Finset.Icc 1 N, ‖u n‖ ^ 2) ≤
          ∑ _n ∈ Finset.Icc 1 N, (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro n hn
            nlinarith [norm_nonneg (u n), hu n hn]
      _ = (N : ℝ) := by simp
  have hcorr :
      (∑ ℓ ∈ Finset.Icc 1 (L - 1), ((L : ℝ) - (ℓ : ℝ)) *
          (∑ n ∈ Finset.Icc 1 (N - ℓ),
            u n * conj (u (n + ℓ))).re) ≤
        (L : ℝ) *
          ∑ ℓ ∈ Finset.Icc 1 (L - 1),
            ‖∑ n ∈ Finset.Icc 1 (N - ℓ),
              u n * conj (u (n + ℓ))‖ := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ℓ hℓ
    have hℓL : ℓ ≤ L := by
      simp only [Finset.mem_Icc] at hℓ
      omega
    have hweight : 0 ≤ (L : ℝ) - (ℓ : ℝ) := by
      exact sub_nonneg.mpr (by exact_mod_cast hℓL)
    have hweightL : (L : ℝ) - (ℓ : ℝ) ≤ L := by
      exact sub_le_self _ (by positivity)
    let C : ℂ := ∑ n ∈ Finset.Icc 1 (N - ℓ),
      u n * conj (u (n + ℓ))
    calc
      ((L : ℝ) - (ℓ : ℝ)) * C.re ≤
          ((L : ℝ) - (ℓ : ℝ)) * ‖C‖ := by
            gcongr
            exact Complex.re_le_norm C
      _ ≤ (L : ℝ) * ‖C‖ := by gcongr
  have hdiag :
      (L : ℝ) * ((N : ℝ) + (L : ℝ) - 1) *
          (∑ n ∈ Finset.Icc 1 N, ‖u n‖ ^ 2) ≤
        2 * (L : ℝ) * (N : ℝ) ^ 2 := by
    have hL0 : 0 ≤ (L : ℝ) := by positivity
    have hspan0 : 0 ≤ (N : ℝ) + (L : ℝ) - 1 := by
      have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have hLR : 0 ≤ (L : ℝ) := by positivity
      linarith
    calc
      (L : ℝ) * ((N : ℝ) + (L : ℝ) - 1) *
          (∑ n ∈ Finset.Icc 1 N, ‖u n‖ ^ 2) ≤
          (L : ℝ) * (2 * (N : ℝ)) * (N : ℝ) := by
            gcongr
            nlinarith [hspan]
      _ = 2 * (L : ℝ) * (N : ℝ) ^ 2 := by ring
  have hoff :
      2 * ((N : ℝ) + (L : ℝ) - 1) *
          (∑ ℓ ∈ Finset.Icc 1 (L - 1), ((L : ℝ) - (ℓ : ℝ)) *
            (∑ n ∈ Finset.Icc 1 (N - ℓ),
              u n * conj (u (n + ℓ))).re) ≤
        4 * (N : ℝ) * (L : ℝ) *
          ∑ ℓ ∈ Finset.Icc 1 (L - 1),
            ‖∑ n ∈ Finset.Icc 1 (N - ℓ),
              u n * conj (u (n + ℓ))‖ := by
    have hspan0 : 0 ≤ (N : ℝ) + (L : ℝ) - 1 := by
      have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have hLR : 0 ≤ (L : ℝ) := by positivity
      linarith
    have hsum0 : 0 ≤
        ∑ ℓ ∈ Finset.Icc 1 (L - 1),
          ‖∑ n ∈ Finset.Icc 1 (N - ℓ),
            u n * conj (u (n + ℓ))‖ := by positivity
    calc
      2 * ((N : ℝ) + (L : ℝ) - 1) *
          (∑ ℓ ∈ Finset.Icc 1 (L - 1), ((L : ℝ) - (ℓ : ℝ)) *
            (∑ n ∈ Finset.Icc 1 (N - ℓ),
              u n * conj (u (n + ℓ))).re) ≤
          2 * ((N : ℝ) + (L : ℝ) - 1) *
            ((L : ℝ) * ∑ ℓ ∈ Finset.Icc 1 (L - 1),
              ‖∑ n ∈ Finset.Icc 1 (N - ℓ),
                u n * conj (u (n + ℓ))‖) := by
            have hcoef0 : 0 ≤ 2 * ((N : ℝ) + (L : ℝ) - 1) := by
              positivity
            gcongr
      _ ≤ 2 * (2 * (N : ℝ)) *
            ((L : ℝ) * ∑ ℓ ∈ Finset.Icc 1 (L - 1),
              ‖∑ n ∈ Finset.Icc 1 (N - ℓ),
                u n * conj (u (n + ℓ))‖) := by
            gcongr
            nlinarith [hspan]
      _ = 4 * (N : ℝ) * (L : ℝ) *
          ∑ ℓ ∈ Finset.Icc 1 (L - 1),
            ‖∑ n ∈ Finset.Icc 1 (N - ℓ),
              u n * conj (u (n + ℓ))‖ := by ring
  have hfund' :
      (L : ℝ) ^ 2 * ‖∑ n ∈ Finset.Icc 1 N, u n‖ ^ 2 ≤
        (L : ℝ) * ((N : ℝ) + (L : ℝ) - 1) *
            ∑ n ∈ Finset.Icc 1 N, ‖u n‖ ^ 2 +
          2 * ((N : ℝ) + (L : ℝ) - 1) *
            ∑ ℓ ∈ Finset.Icc 1 (L - 1), ((L : ℝ) - (ℓ : ℝ)) *
              (∑ n ∈ Finset.Icc 1 (N - ℓ),
                u n * conj (u (n + ℓ))).re := by
    simpa only [Nat.cast_one, one_mul, sub_eq_add_neg, add_assoc] using hfund
  exact hfund'.trans (add_le_add hdiag hoff)

/-! ## Iterated finite differences -/

/-- Successive positive forward differences of a real function. -/
def forwardDifferences : List ℝ → (ℝ → ℝ) → ℝ → ℝ
  | [], f => f
  | r :: rs, f => fun t ↦
      forwardDifferences rs f (t + r) - forwardDifferences rs f t

@[simp] theorem forwardDifferences_nil (f : ℝ → ℝ) :
    forwardDifferences [] f = f := rfl

@[simp] theorem forwardDifferences_cons (r : ℝ) (rs : List ℝ)
    (f : ℝ → ℝ) (t : ℝ) :
    forwardDifferences (r :: rs) f t =
      forwardDifferences rs f (t + r) - forwardDifferences rs f t := rfl

/-- Differentiation commutes with a finite list of nonnegative forward
differences on the positive half-line. -/
theorem hasDerivAt_forwardDifferences {f f' : ℝ → ℝ} {rs : List ℝ}
    (hrs : ∀ r ∈ rs, 0 ≤ r)
    (hf : ∀ t : ℝ, 0 < t → HasDerivAt f (f' t) t) :
    ∀ {t : ℝ}, 0 < t →
      HasDerivAt (forwardDifferences rs f)
        (forwardDifferences rs f' t) t := by
  induction rs generalizing f f' with
  | nil =>
      intro t ht
      exact hf t ht
  | cons r rs ih =>
      intro t ht
      have hr : 0 ≤ r := hrs r (by simp)
      have hrs' : ∀ s ∈ rs, 0 ≤ s := by
        intro s hs
        exact hrs s (by simp [hs])
      have hbase : ∀ {x : ℝ}, 0 < x →
          HasDerivAt (forwardDifferences rs f)
            (forwardDifferences rs f' x) x := ih hrs' hf
      have hshift : HasDerivAt
          (fun x ↦ forwardDifferences rs f (x + r))
          (forwardDifferences rs f' (t + r)) t := by
        exact (hbase (add_pos_of_pos_of_nonneg ht hr)).comp_add_const t r
      have hstay : HasDerivAt (forwardDifferences rs f)
          (forwardDifferences rs f' t) t := hbase ht
      change HasDerivAt
        (fun x ↦ forwardDifferences rs f (x + r) - forwardDifferences rs f x)
        (forwardDifferences rs f' (t + r) - forwardDifferences rs f' t) t
      exact hshift.sub hstay

/-- Iterated mean-value theorem: a finite difference equals the product of
the shifts times a higher derivative at an intermediate point. -/
theorem exists_forwardDifferences_eq_prod_deriv
    (F : ℕ → ℝ → ℝ)
    (hF : ∀ k : ℕ, ∀ t : ℝ, 0 < t →
      HasDerivAt (F k) (F (k + 1) t) t)
    (rs : List ℝ) (hrs : ∀ r ∈ rs, 0 < r)
    {t : ℝ} (ht : 0 < t) :
    ∃ y : ℝ, t ≤ y ∧ y ≤ t + rs.sum ∧
      forwardDifferences rs (F 0) t = rs.prod * F rs.length y := by
  induction rs generalizing F t with
  | nil =>
      refine ⟨t, le_rfl, ?_, ?_⟩
      · simp
      · simp
  | cons r rs ih =>
      have hr : 0 < r := hrs r (by simp)
      have hrs' : ∀ s ∈ rs, 0 < s := by
        intro s hs
        exact hrs s (by simp [hs])
      let G : ℝ → ℝ := forwardDifferences rs (F 0)
      let G' : ℝ → ℝ := forwardDifferences rs (F 1)
      have hrsNonneg : ∀ s ∈ rs, 0 ≤ s := fun s hs ↦ (hrs' s hs).le
      have hG : ∀ {x : ℝ}, 0 < x → HasDerivAt G (G' x) x := by
        intro x hx
        have h := hasDerivAt_forwardDifferences hrsNonneg (hF 0) hx
        simpa [G, G'] using h
      have hcont : ContinuousOn G (Set.Icc t (t + r)) := by
        intro x hx
        exact (hG (ht.trans_le hx.1)).continuousAt.continuousWithinAt
      have hmvt := exists_hasDerivAt_eq_slope G G' (lt_add_of_pos_right t hr)
        hcont (fun x hx ↦ hG (ht.trans hx.1))
      obtain ⟨c, hc, hcderiv⟩ := hmvt
      let F' : ℕ → ℝ → ℝ := fun k ↦ F (k + 1)
      have hF' : ∀ k : ℕ, ∀ x : ℝ, 0 < x →
          HasDerivAt (F' k) (F' (k + 1) x) x := by
        intro k x hx
        simpa [F', Nat.add_assoc] using hF (k + 1) x hx
      obtain ⟨y, hcy, hy, heq⟩ :=
        ih (F := F') hF' hrs' (t := c) (ht.trans hc.1)
      refine ⟨y, (le_of_lt hc.1).trans hcy, ?_, ?_⟩
      · dsimp only [List.sum_cons]
        calc
          y ≤ c + rs.sum := hy
          _ ≤ (t + r) + rs.sum := add_le_add hc.2.le le_rfl
          _ = t + (r + rs.sum) := by ring
      · have hdiff : G (t + r) - G t = r * G' c := by
          have hr0 : r ≠ 0 := ne_of_gt hr
          have hden : t + r - t = r := by ring
          rw [hden] at hcderiv
          calc
            G (t + r) - G t = (G (t + r) - G t) / r * r :=
              (div_mul_cancel₀ _ hr0).symm
            _ = G' c * r := by rw [← hcderiv]
            _ = r * G' c := by ring
        rw [forwardDifferences_cons]
        change G (t + r) - G t = _
        rw [hdiff]
        have hG'eq : G' c = forwardDifferences rs (F' 0) c := by rfl
        rw [hG'eq, heq]
        simp only [List.prod_cons, List.length_cons, F']
        ring

/-! ### Higher derivatives of the reciprocal -/

/-- The `k`-th derivative of the reciprocal phase `t ↦ -X / t` on the
positive half-line.  It is recorded as an explicit integer power so that the
finite-difference mean-value theorem can use it without any smoothness
black box. -/
noncomputable def reciprocalDeriv (X : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  -X * ((-1 : ℝ) ^ k * (k.factorial : ℝ) * t ^ (-1 - (k : ℤ)))

@[simp] theorem reciprocalDeriv_zero (X t : ℝ) :
    reciprocalDeriv X 0 t = -X / t := by
  simp [reciprocalDeriv, div_eq_mul_inv]

/-- Successive members of `reciprocalDeriv` really are successive
derivatives at every positive point. -/
theorem hasDerivAt_reciprocalDeriv (X : ℝ) (k : ℕ) {t : ℝ}
    (ht : 0 < t) :
    HasDerivAt (reciprocalDeriv X k) (reciprocalDeriv X (k + 1) t) t := by
  have hz := hasDerivAt_zpow (-1 - (k : ℤ)) t
    (Or.inl (ne_of_gt ht))
  have hmul := hz.const_mul
    (-X * ((-1 : ℝ) ^ k * (k.factorial : ℝ)))
  unfold reciprocalDeriv
  have hfun :
      (fun y : ℝ ↦ -X *
        ((-1 : ℝ) ^ k * (k.factorial : ℝ) * y ^ (-1 - (k : ℤ)))) =
      (fun y : ℝ ↦
        (-X * ((-1 : ℝ) ^ k * (k.factorial : ℝ))) *
          y ^ (-1 - (k : ℤ))) := by
    funext y
    ring
  rw [hfun]
  have hder :
      -X * ((-1 : ℝ) ^ (k + 1) * ((k + 1).factorial : ℝ) *
          t ^ (-1 - ((k + 1 : ℕ) : ℤ))) =
        (-X * ((-1 : ℝ) ^ k * (k.factorial : ℝ))) *
          (((-1 - (k : ℤ) : ℤ) : ℝ) * t ^ (-1 - (k : ℤ) - 1)) := by
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      pow_succ]
    have hexp : -1 - ((k : ℤ) + 1) = -1 - (k : ℤ) - 1 := by
      ring
    rw [hexp]
    push_cast
    ring
  rw [hder]
  exact hmul

/-- A list of positive shifts turns a reciprocal finite difference into the
product of the shifts times the corresponding explicit higher derivative at
an intermediate point.  This is Granville--Ramaré Lemma 8.5 for the
reciprocal function. -/
theorem exists_forwardDifferences_reciprocal_eq (X : ℝ)
    (rs : List ℝ) (hrs : ∀ r ∈ rs, 0 < r) {t : ℝ} (ht : 0 < t) :
    ∃ y : ℝ, t ≤ y ∧ y ≤ t + rs.sum ∧
      forwardDifferences rs (fun x ↦ -X / x) t =
        rs.prod * reciprocalDeriv X rs.length y := by
  have hzero : reciprocalDeriv X 0 = fun x ↦ -X / x := by
    funext x
    exact reciprocalDeriv_zero X x
  rw [← hzero]
  exact exists_forwardDifferences_eq_prod_deriv (reciprocalDeriv X)
    (fun k x hx ↦ hasDerivAt_reciprocalDeriv X k hx) rs hrs ht

/-! ### Second finite differences of a reciprocal phase -/

/-- A positive-shift correlation phase for the reciprocal sequence. -/
noncomputable def reciprocalDifferencePhase (X : ℝ) (A ℓ i : ℕ) : ℝ :=
  reciprocalPhase X A i - reciprocalPhase X A (i + ℓ)

/-- The first difference of a correlation phase is the negative of the
two-fold forward difference with shifts `ℓ` and `1`. -/
theorem reciprocalDifferencePhase_succ_sub (X : ℝ) (A ℓ i : ℕ) :
    reciprocalDifferencePhase X A ℓ (i + 1) -
        reciprocalDifferencePhase X A ℓ i =
      -forwardDifferences [(ℓ : ℝ), 1] (fun x ↦ -X / x) (A + i : ℕ) := by
  simp only [reciprocalDifferencePhase, reciprocalPhase,
    forwardDifferences_cons, forwardDifferences_nil, List.map, List.sum_cons]
  push_cast
  ring

/-- Mean-value form of the positive second reciprocal difference. -/
theorem exists_reciprocalDifferencePhase_succ_sub
    (X : ℝ) {A ℓ i : ℕ} (hA : 0 < A) (hℓ : 0 < ℓ) :
    ∃ y : ℝ, (A + i : ℕ) ≤ y ∧
      y ≤ (A + i : ℕ) + ℓ + 1 ∧
      reciprocalDifferencePhase X A ℓ (i + 1) -
          reciprocalDifferencePhase X A ℓ i =
        2 * X * ℓ / y ^ 3 := by
  have ht : 0 < ((A + i : ℕ) : ℝ) := by positivity
  have hrs : ∀ r ∈ [(ℓ : ℝ), 1], 0 < r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact_mod_cast hℓ
    · norm_num
  obtain ⟨y, hty, hy, hfd⟩ :=
    exists_forwardDifferences_reciprocal_eq X [(ℓ : ℝ), 1] hrs ht
  refine ⟨y, hty, ?_, ?_⟩
  · simpa [add_assoc] using hy
  · rw [reciprocalDifferencePhase_succ_sub, hfd]
    have hy0 : y ≠ 0 := ne_of_gt (ht.trans_le hty)
    norm_num [reciprocalDeriv, zpow_neg]
    field_simp

/-- Uniform lower bound for the positive second difference on a finite
interval. -/
theorem reciprocalDifferencePhase_gap_lower
    (X : ℝ) (hX : 0 < X) {A ℓ N i : ℕ} (hA : 0 < A) (hℓ : 0 < ℓ)
    (hi : i < N - ℓ - 1) :
    2 * X * ℓ / ((A + N : ℕ) : ℝ) ^ 3 ≤
      reciprocalDifferencePhase X A ℓ (i + 1) -
        reciprocalDifferencePhase X A ℓ i := by
  obtain ⟨y, hty, hy, hgap⟩ :=
    exists_reciprocalDifferencePhase_succ_sub X hA hℓ (i := i)
  rw [hgap]
  have hypos : 0 < y := (by positivity : 0 < ((A + i : ℕ) : ℝ)).trans_le hty
  have hyN : y ≤ ((A + N : ℕ) : ℝ) := by
    calc
      y ≤ ((A + i : ℕ) : ℝ) + ℓ + 1 := hy
      _ ≤ ((A + N : ℕ) : ℝ) := by
        have hnat : A + i + ℓ + 1 ≤ A + N := by omega
        exact_mod_cast hnat
  apply div_le_div_of_nonneg_left (by positivity)
  · positivity
  · gcongr

/-- Uniform upper bound for a positive second reciprocal difference. -/
theorem reciprocalDifferencePhase_gap_upper
    (X : ℝ) (hX : 0 < X) {A ℓ i : ℕ} (hA : 0 < A) (hℓ : 0 < ℓ) :
    reciprocalDifferencePhase X A ℓ (i + 1) -
        reciprocalDifferencePhase X A ℓ i ≤
      2 * X * ℓ / (A : ℝ) ^ 3 := by
  obtain ⟨y, hty, hy, hgap⟩ :=
    exists_reciprocalDifferencePhase_succ_sub X hA hℓ (i := i)
  rw [hgap]
  have hAy : (A : ℝ) ≤ y := by
    exact (by exact_mod_cast Nat.le_add_right A i : (A : ℝ) ≤ (A + i : ℕ)).trans hty
  have hApos : 0 < (A : ℝ) := by exact_mod_cast hA
  apply div_le_div_of_nonneg_left (by positivity)
  · positivity
  · gcongr

/-- A third forward difference measures the successive change of the
second-difference gaps. -/
theorem reciprocalDifferencePhase_gap_succ_sub (X : ℝ) (A ℓ i : ℕ) :
    (reciprocalDifferencePhase X A ℓ (i + 2) -
        reciprocalDifferencePhase X A ℓ (i + 1)) -
      (reciprocalDifferencePhase X A ℓ (i + 1) -
        reciprocalDifferencePhase X A ℓ i) =
      -forwardDifferences [(1 : ℝ), ℓ, 1]
        (fun x ↦ -X / x) (A + i : ℕ) := by
  simp only [reciprocalDifferencePhase, reciprocalPhase,
    forwardDifferences_cons, forwardDifferences_nil]
  push_cast
  ring

/-- The positive second reciprocal differences decrease along the interval. -/
theorem reciprocalDifferencePhase_gap_antitone
    (X : ℝ) (hX : 0 ≤ X) {A ℓ : ℕ} (hA : 0 < A) (hℓ : 0 < ℓ) :
    Antitone (fun i ↦ reciprocalDifferencePhase X A ℓ (i + 1) -
      reciprocalDifferencePhase X A ℓ i) := by
  apply antitone_nat_of_succ_le
  intro i
  have ht : 0 < ((A + i : ℕ) : ℝ) := by positivity
  have hrs : ∀ r ∈ [(1 : ℝ), ℓ, 1], 0 < r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · exact_mod_cast hℓ
    · norm_num
  obtain ⟨y, hty, hy, hfd⟩ :=
    exists_forwardDifferences_reciprocal_eq X [(1 : ℝ), ℓ, 1] hrs ht
  have hypos : 0 < y := ht.trans_le hty
  have hderiv : 0 ≤ reciprocalDeriv X 3 y := by
    norm_num [reciprocalDeriv, zpow_neg]
    positivity
  have hfdnonneg : 0 ≤ forwardDifferences [(1 : ℝ), ℓ, 1]
      (fun x ↦ -X / x) (A + i : ℕ) := by
    rw [hfd]
    simp only [List.prod_cons, List.prod_nil, mul_one]
    positivity
  have hchange := reciprocalDifferencePhase_gap_succ_sub X A ℓ i
  linarith

/-! ### Third finite differences of a reciprocal phase -/

/-- The correlation phase after two positive van der Corput shifts. -/
noncomputable def reciprocalDoubleDifferencePhase
    (X : ℝ) (A ℓ₁ ℓ₂ i : ℕ) : ℝ :=
  reciprocalDifferencePhase X A ℓ₁ i -
    reciprocalDifferencePhase X A ℓ₁ (i + ℓ₂)

/-- The gap of a double-correlation phase is a three-fold forward
difference of the reciprocal. -/
theorem reciprocalDoubleDifferencePhase_succ_sub
    (X : ℝ) (A ℓ₁ ℓ₂ i : ℕ) :
    reciprocalDoubleDifferencePhase X A ℓ₁ ℓ₂ (i + 1) -
        reciprocalDoubleDifferencePhase X A ℓ₁ ℓ₂ i =
      forwardDifferences [(ℓ₁ : ℝ), (ℓ₂ : ℝ), 1]
        (fun x ↦ -X / x) (A + i : ℕ) := by
  simp only [reciprocalDoubleDifferencePhase, reciprocalDifferencePhase,
    reciprocalPhase, forwardDifferences_cons, forwardDifferences_nil]
  push_cast
  ring

/-- Mean-value form of the positive third reciprocal difference. -/
theorem exists_reciprocalDoubleDifferencePhase_succ_sub
    (X : ℝ) {A ℓ₁ ℓ₂ i : ℕ}
    (hA : 0 < A) (hℓ₁ : 0 < ℓ₁) (hℓ₂ : 0 < ℓ₂) :
    ∃ y : ℝ, (A + i : ℕ) ≤ y ∧
      y ≤ (A + i : ℕ) + ℓ₁ + ℓ₂ + 1 ∧
      reciprocalDoubleDifferencePhase X A ℓ₁ ℓ₂ (i + 1) -
          reciprocalDoubleDifferencePhase X A ℓ₁ ℓ₂ i =
        6 * X * ℓ₁ * ℓ₂ / y ^ 4 := by
  have ht : 0 < ((A + i : ℕ) : ℝ) := by positivity
  have hrs : ∀ r ∈ [(ℓ₁ : ℝ), (ℓ₂ : ℝ), 1], 0 < r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact_mod_cast hℓ₁
    · exact_mod_cast hℓ₂
    · norm_num
  obtain ⟨y, hty, hy, hfd⟩ :=
    exists_forwardDifferences_reciprocal_eq X
      [(ℓ₁ : ℝ), (ℓ₂ : ℝ), 1] hrs ht
  refine ⟨y, hty, ?_, ?_⟩
  · simpa [add_assoc] using hy
  · rw [reciprocalDoubleDifferencePhase_succ_sub, hfd]
    have hy0 : y ≠ 0 := ne_of_gt (ht.trans_le hty)
    norm_num [reciprocalDeriv, zpow_neg]
    field_simp

/-- Uniform lower bound for the positive third reciprocal difference. -/
theorem reciprocalDoubleDifferencePhase_gap_lower
    (X : ℝ) (hX : 0 < X) {A ℓ₁ ℓ₂ N i : ℕ}
    (hA : 0 < A) (hℓ₁ : 0 < ℓ₁) (hℓ₂ : 0 < ℓ₂)
    (hi : i < N - ℓ₁ - ℓ₂ - 1) :
    6 * X * ℓ₁ * ℓ₂ / ((A + N : ℕ) : ℝ) ^ 4 ≤
      reciprocalDoubleDifferencePhase X A ℓ₁ ℓ₂ (i + 1) -
        reciprocalDoubleDifferencePhase X A ℓ₁ ℓ₂ i := by
  obtain ⟨y, hty, hy, hgap⟩ :=
    exists_reciprocalDoubleDifferencePhase_succ_sub X hA hℓ₁ hℓ₂ (i := i)
  rw [hgap]
  have hypos : 0 < y := (by positivity : 0 < ((A + i : ℕ) : ℝ)).trans_le hty
  have hyN : y ≤ ((A + N : ℕ) : ℝ) := by
    calc
      y ≤ ((A + i : ℕ) : ℝ) + ℓ₁ + ℓ₂ + 1 := hy
      _ ≤ ((A + N : ℕ) : ℝ) := by
        have hnat : A + i + ℓ₁ + ℓ₂ + 1 ≤ A + N := by omega
        exact_mod_cast hnat
  apply div_le_div_of_nonneg_left (by positivity)
  · positivity
  · gcongr

/-- Uniform upper bound for a positive third reciprocal difference. -/
theorem reciprocalDoubleDifferencePhase_gap_upper
    (X : ℝ) (hX : 0 < X) {A ℓ₁ ℓ₂ i : ℕ}
    (hA : 0 < A) (hℓ₁ : 0 < ℓ₁) (hℓ₂ : 0 < ℓ₂) :
    reciprocalDoubleDifferencePhase X A ℓ₁ ℓ₂ (i + 1) -
        reciprocalDoubleDifferencePhase X A ℓ₁ ℓ₂ i ≤
      6 * X * ℓ₁ * ℓ₂ / (A : ℝ) ^ 4 := by
  obtain ⟨y, hty, hy, hgap⟩ :=
    exists_reciprocalDoubleDifferencePhase_succ_sub X hA hℓ₁ hℓ₂ (i := i)
  rw [hgap]
  have hAy : (A : ℝ) ≤ y := by
    exact (by exact_mod_cast Nat.le_add_right A i :
      (A : ℝ) ≤ (A + i : ℕ)).trans hty
  have hApos : 0 < (A : ℝ) := by exact_mod_cast hA
  apply div_le_div_of_nonneg_left (by positivity)
  · positivity
  · gcongr

/-- A fourth forward difference is the successive change of the third
difference gaps. -/
theorem reciprocalDoubleDifferencePhase_gap_succ_sub
    (X : ℝ) (A ℓ₁ ℓ₂ i : ℕ) :
    (reciprocalDoubleDifferencePhase X A ℓ₁ ℓ₂ (i + 2) -
        reciprocalDoubleDifferencePhase X A ℓ₁ ℓ₂ (i + 1)) -
      (reciprocalDoubleDifferencePhase X A ℓ₁ ℓ₂ (i + 1) -
        reciprocalDoubleDifferencePhase X A ℓ₁ ℓ₂ i) =
      forwardDifferences [(1 : ℝ), (ℓ₁ : ℝ), (ℓ₂ : ℝ), 1]
        (fun x ↦ -X / x) (A + i : ℕ) := by
  simp only [reciprocalDoubleDifferencePhase, reciprocalDifferencePhase,
    reciprocalPhase, forwardDifferences_cons, forwardDifferences_nil]
  push_cast
  ring

/-- The positive third reciprocal differences decrease along the interval. -/
theorem reciprocalDoubleDifferencePhase_gap_antitone
    (X : ℝ) (hX : 0 ≤ X) {A ℓ₁ ℓ₂ : ℕ}
    (hA : 0 < A) (hℓ₁ : 0 < ℓ₁) (hℓ₂ : 0 < ℓ₂) :
    Antitone (fun i ↦
      reciprocalDoubleDifferencePhase X A ℓ₁ ℓ₂ (i + 1) -
        reciprocalDoubleDifferencePhase X A ℓ₁ ℓ₂ i) := by
  apply antitone_nat_of_succ_le
  intro i
  have ht : 0 < ((A + i : ℕ) : ℝ) := by positivity
  have hrs : ∀ r ∈ [(1 : ℝ), (ℓ₁ : ℝ), (ℓ₂ : ℝ), 1], 0 < r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · exact_mod_cast hℓ₁
    · exact_mod_cast hℓ₂
    · norm_num
  obtain ⟨y, hty, hy, hfd⟩ :=
    exists_forwardDifferences_reciprocal_eq X
      [(1 : ℝ), (ℓ₁ : ℝ), (ℓ₂ : ℝ), 1] hrs ht
  have hypos : 0 < y := ht.trans_le hty
  have hderiv : reciprocalDeriv X 4 y ≤ 0 := by
    norm_num [reciprocalDeriv, zpow_neg]
    positivity
  have hfdnonpos : forwardDifferences
      [(1 : ℝ), (ℓ₁ : ℝ), (ℓ₂ : ℝ), 1]
        (fun x ↦ -X / x) (A + i : ℕ) ≤ 0 := by
    rw [hfd]
    simp only [List.prod_cons, List.prod_nil, mul_one]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hderiv
  have hchange := reciprocalDoubleDifferencePhase_gap_succ_sub X A ℓ₁ ℓ₂ i
  linarith

/-- The second-level correlation is controlled by the sharp
Kusmin--Landau inequality and the third reciprocal derivative. -/
theorem norm_reciprocal_double_correlation_le
    (X : ℝ) (hX : 0 < X) {A N ℓ₁ ℓ₂ : ℕ} (hA : 0 < A)
    (hℓ₁ : 0 < ℓ₁) (hℓ₂ : 0 < ℓ₂)
    (hsum : ℓ₁ + ℓ₂ ≤ N - 2)
    (hsmall : 6 * X * ℓ₁ * ℓ₂ / (A : ℝ) ^ 4 ≤ 1 / 2) :
    ‖∑ i ∈ Finset.range (N - ℓ₁ - ℓ₂),
        e (reciprocalDoubleDifferencePhase X A ℓ₁ ℓ₂ i)‖ ≤
      1 + 3 / (2 *
        (6 * X * ℓ₁ * ℓ₂ / ((A + N : ℕ) : ℝ) ^ 4)) := by
  let M := N - ℓ₁ - ℓ₂
  have hM : 2 ≤ M := by omega
  let m : ℝ := 6 * X * ℓ₁ * ℓ₂ / ((A + N : ℕ) : ℝ) ^ 4
  have hm : 0 < m := by positivity
  apply norm_sum_e_le_of_antitone_phaseDiff_sharp
    (reciprocalDoubleDifferencePhase X A ℓ₁ ℓ₂) M hM m hm
  · intro i hi
    exact reciprocalDoubleDifferencePhase_gap_lower X hX hA hℓ₁ hℓ₂ (by
      dsimp [M] at hi ⊢
      exact hi)
  · intro i hi
    exact (reciprocalDoubleDifferencePhase_gap_upper X hX hA hℓ₁ hℓ₂).trans hsmall
  · exact reciprocalDoubleDifferencePhase_gap_antitone X hX.le hA hℓ₁ hℓ₂

/-- The first correlation sequence, indexed from one as required by the
norm-only van der Corput inequality. -/
noncomputable def reciprocalCorrelationSequence
    (X : ℝ) (A ℓ : ℕ) (n : ℕ) : ℂ :=
  e (reciprocalPhase X A (n - 1)) *
    conj (e (reciprocalPhase X A (n + ℓ - 1)))

@[simp] theorem norm_reciprocalCorrelationSequence
    (X : ℝ) (A ℓ n : ℕ) :
    ‖reciprocalCorrelationSequence X A ℓ n‖ = 1 := by
  simp [reciprocalCorrelationSequence, norm_e]

/-- A second correlation of the original reciprocal sequence is exactly the
double-difference phase estimated above. -/
theorem norm_second_reciprocal_correlation_le
    (X : ℝ) (hX : 0 < X) {A N ℓ₁ ℓ₂ : ℕ} (hA : 0 < A)
    (hℓ₁ : 0 < ℓ₁) (hℓ₂ : 0 < ℓ₂)
    (hsum : ℓ₁ + ℓ₂ ≤ N - 2)
    (hsmall : 6 * X * ℓ₁ * ℓ₂ / (A : ℝ) ^ 4 ≤ 1 / 2) :
    ‖∑ n ∈ Finset.Icc 1 (N - ℓ₁ - ℓ₂),
        reciprocalCorrelationSequence X A ℓ₁ n *
          conj (reciprocalCorrelationSequence X A ℓ₁ (n + ℓ₂))‖ ≤
      1 + 3 / (2 *
        (6 * X * ℓ₁ * ℓ₂ / ((A + N : ℕ) : ℝ) ^ 4)) := by
  let M := N - ℓ₁ - ℓ₂
  have hsumEq :
      (∑ n ∈ Finset.Icc 1 (N - ℓ₁ - ℓ₂),
          reciprocalCorrelationSequence X A ℓ₁ n *
            conj (reciprocalCorrelationSequence X A ℓ₁ (n + ℓ₂))) =
        ∑ i ∈ Finset.range M,
          e (reciprocalDoubleDifferencePhase X A ℓ₁ ℓ₂ i) := by
    rw [sum_Icc_one_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    have hfirst : i + 1 - 1 = i := by omega
    have hshift₁ : i + 1 + ℓ₁ - 1 = i + ℓ₁ := by omega
    have hshift₂ : i + 1 + ℓ₂ - 1 = i + ℓ₂ := by omega
    have hboth : i + 1 + ℓ₂ + ℓ₁ - 1 = i + ℓ₂ + ℓ₁ := by omega
    rw [reciprocalCorrelationSequence, reciprocalCorrelationSequence,
      hfirst, hshift₁, hshift₂, hboth,
      ← e_sub, ← e_sub, ← e_sub]
    congr 1
  rw [hsumEq]
  exact norm_reciprocal_double_correlation_le X hX hA hℓ₁ hℓ₂ hsum hsmall

/-- Majorant supplied by the second van der Corput stage at the first shift
`ℓ₁`.  It is kept as a finite sum so later parameter estimates can choose
their preferred elementary harmonic bound. -/
noncomputable def reciprocalThirdStageMajorant
    (X : ℝ) (A N L₂ ℓ₁ : ℕ) : ℝ :=
  2 * (L₂ : ℝ) * ((N - ℓ₁ : ℕ) : ℝ) ^ 2 +
    4 * ((N - ℓ₁ : ℕ) : ℝ) * (L₂ : ℝ) *
      ∑ ℓ₂ ∈ Finset.Icc 1 (L₂ - 1),
        (1 + 3 / (2 *
          (6 * X * ℓ₁ * ℓ₂ / ((A + N : ℕ) : ℝ) ^ 4)))

theorem reciprocalThirdStageMajorant_nonneg
    (X : ℝ) (hX : 0 < X) {A N L₂ ℓ₁ : ℕ}
    (hA : 0 < A) (hℓ₁ : 0 < ℓ₁) :
    0 ≤ reciprocalThirdStageMajorant X A N L₂ ℓ₁ := by
  unfold reciprocalThirdStageMajorant
  positivity

/-- Harmonic upper bound for one second-stage correlation majorant. -/
theorem reciprocalThirdStageMajorant_le
    (X : ℝ) (hX : 0 < X) {A N L₂ ℓ₁ : ℕ}
    (hA : 0 < A) (hℓ₁ : 0 < ℓ₁) :
    reciprocalThirdStageMajorant X A N L₂ ℓ₁ ≤
      2 * (L₂ : ℝ) * ((N - ℓ₁ : ℕ) : ℝ) ^ 2 +
        4 * ((N - ℓ₁ : ℕ) : ℝ) * (L₂ : ℝ) *
          ((L₂ : ℝ) +
            ((((A + N : ℕ) : ℝ) ^ 4) / (4 * X * (ℓ₁ : ℝ))) *
              (harmonic (L₂ - 1) : ℝ)) := by
  let C : ℝ := (((A + N : ℕ) : ℝ) ^ 4) / (4 * X * (ℓ₁ : ℝ))
  have hC : 0 ≤ C := by positivity
  have hrewrite : ∀ ℓ₂ ∈ Finset.Icc 1 (L₂ - 1),
      1 + 3 / (2 *
        (6 * X * ℓ₁ * ℓ₂ / ((A + N : ℕ) : ℝ) ^ 4)) =
        1 + C * (1 / (ℓ₂ : ℝ)) := by
    intro ℓ₂ hℓ₂mem
    have hℓ₂ : 0 < ℓ₂ := by
      have := (Finset.mem_Icc.mp hℓ₂mem).1
      omega
    dsimp only [C]
    have hℓ₁R : (ℓ₁ : ℝ) ≠ 0 := by positivity
    have hℓ₂R : (ℓ₂ : ℝ) ≠ 0 := by positivity
    have hAN : ((A + N : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  have hharm :
      (∑ ℓ₂ ∈ Finset.Icc 1 (L₂ - 1), (1 / (ℓ₂ : ℝ))) =
        (harmonic (L₂ - 1) : ℝ) := by
    simpa [one_div, harmonic_eq_sum_Icc]
  have hsum :
      (∑ ℓ₂ ∈ Finset.Icc 1 (L₂ - 1),
        (1 + 3 / (2 *
          (6 * X * ℓ₁ * ℓ₂ / ((A + N : ℕ) : ℝ) ^ 4)))) ≤
        (L₂ : ℝ) + C * (harmonic (L₂ - 1) : ℝ) := by
    calc
      _ = ∑ ℓ₂ ∈ Finset.Icc 1 (L₂ - 1),
          (1 + C * (1 / (ℓ₂ : ℝ))) := Finset.sum_congr rfl hrewrite
      _ = ((Finset.Icc 1 (L₂ - 1)).card : ℝ) +
          C * (∑ ℓ₂ ∈ Finset.Icc 1 (L₂ - 1), 1 / (ℓ₂ : ℝ)) := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one,
          ← Finset.mul_sum]
      _ ≤ (L₂ : ℝ) + C * (harmonic (L₂ - 1) : ℝ) := by
        rw [hharm]
        gcongr
        simp
  unfold reciprocalThirdStageMajorant
  dsimp only [C] at hsum ⊢
  gcongr

/-- Summed harmonic majorant for all first-stage shifts. -/
theorem sum_reciprocalThirdStageMajorant_le
    (X : ℝ) (hX : 0 < X) {A N L₁ L₂ : ℕ} (hA : 0 < A) :
    (∑ ℓ₁ ∈ Finset.Icc 1 (L₁ - 1),
        reciprocalThirdStageMajorant X A N L₂ ℓ₁) ≤
      (L₁ : ℝ) *
          (2 * (L₂ : ℝ) * (N : ℝ) ^ 2 +
            4 * (N : ℝ) * (L₂ : ℝ) ^ 2) +
        4 * (N : ℝ) * (L₂ : ℝ) *
          ((((A + N : ℕ) : ℝ) ^ 4) / (4 * X)) *
          (harmonic (L₂ - 1) : ℝ) *
          (harmonic (L₁ - 1) : ℝ) := by
  let C : ℝ := (((A + N : ℕ) : ℝ) ^ 4) / (4 * X)
  let B : ℝ :=
    2 * (L₂ : ℝ) * (N : ℝ) ^ 2 + 4 * (N : ℝ) * (L₂ : ℝ) ^ 2
  let D : ℝ := 4 * (N : ℝ) * (L₂ : ℝ) * C *
    (harmonic (L₂ - 1) : ℝ)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hH₂ : 0 ≤ (harmonic (L₂ - 1) : ℝ) := by
    have hsum : 0 ≤
        ∑ ℓ₂ ∈ Finset.Icc 1 (L₂ - 1), (1 / (ℓ₂ : ℝ)) := by
      positivity
    simpa [one_div, harmonic_eq_sum_Icc] using hsum
  have hD : 0 ≤ D := by dsimp [D, C]; positivity
  have hpoint : ∀ ℓ₁ ∈ Finset.Icc 1 (L₁ - 1),
      reciprocalThirdStageMajorant X A N L₂ ℓ₁ ≤
        B + D * (1 / (ℓ₁ : ℝ)) := by
    intro ℓ₁ hℓ₁mem
    have hℓ₁ : 0 < ℓ₁ := by
      have := (Finset.mem_Icc.mp hℓ₁mem).1
      omega
    have hbase := reciprocalThirdStageMajorant_le X hX
      (N := N) (L₂ := L₂) (ℓ₁ := ℓ₁) hA hℓ₁
    have hsub : ((N - ℓ₁ : ℕ) : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast Nat.sub_le N ℓ₁
    have hrewrite :
        ((((A + N : ℕ) : ℝ) ^ 4) / (4 * X * (ℓ₁ : ℝ))) =
          C * (1 / (ℓ₁ : ℝ)) := by
      dsimp only [C]
      have hℓ₁R : (ℓ₁ : ℝ) ≠ 0 := by positivity
      field_simp
    calc
      reciprocalThirdStageMajorant X A N L₂ ℓ₁ ≤ _ := hbase
      _ ≤ 2 * (L₂ : ℝ) * (N : ℝ) ^ 2 +
          4 * (N : ℝ) * (L₂ : ℝ) *
            ((L₂ : ℝ) + C * (1 / (ℓ₁ : ℝ)) *
              (harmonic (L₂ - 1) : ℝ)) := by
        rw [hrewrite]
        gcongr
      _ = B + D * (1 / (ℓ₁ : ℝ)) := by
        dsimp only [B, D]
        ring
  have hharm :
      (∑ ℓ₁ ∈ Finset.Icc 1 (L₁ - 1), (1 / (ℓ₁ : ℝ))) =
        (harmonic (L₁ - 1) : ℝ) := by
    simpa [one_div, harmonic_eq_sum_Icc]
  calc
    (∑ ℓ₁ ∈ Finset.Icc 1 (L₁ - 1),
        reciprocalThirdStageMajorant X A N L₂ ℓ₁) ≤
        ∑ ℓ₁ ∈ Finset.Icc 1 (L₁ - 1),
          (B + D * (1 / (ℓ₁ : ℝ))) := Finset.sum_le_sum hpoint
    _ = ((Finset.Icc 1 (L₁ - 1)).card : ℝ) * B +
        D * (harmonic (L₁ - 1) : ℝ) := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
      rw [hharm]
    _ ≤ (L₁ : ℝ) * B + D * (harmonic (L₁ - 1) : ℝ) := by
      gcongr
      simp
    _ = _ := by
      dsimp only [B, D, C]

/-- Fully explicit harmonic majorant for the two-stage reciprocal estimate. -/
noncomputable def reciprocalThirdDerivativeMajorant
    (X : ℝ) (A N L₁ L₂ : ℕ) : ℝ :=
  2 * (L₂ : ℝ) ^ 2 * (2 * (L₁ : ℝ) * (N : ℝ) ^ 2) ^ 2 +
    2 * (4 * (N : ℝ) * (L₁ : ℝ)) ^ 2 * (L₁ : ℝ) *
      ((L₁ : ℝ) *
          (2 * (L₂ : ℝ) * (N : ℝ) ^ 2 +
            4 * (N : ℝ) * (L₂ : ℝ) ^ 2) +
        4 * (N : ℝ) * (L₂ : ℝ) *
          ((((A + N : ℕ) : ℝ) ^ 4) / (4 * X)) *
          (harmonic (L₂ - 1) : ℝ) *
          (harmonic (L₁ - 1) : ℝ))

/-- Two van der Corput stages followed by the sharp third-derivative test.
The fourth-power form avoids introducing square roots and is the convenient
input for bilinear Cauchy--Schwarz. -/
theorem reciprocal_third_derivative_bound
    (X : ℝ) (hX : 0 < X) {A N L₁ L₂ : ℕ} (hA : 0 < A)
    (hN : 4 ≤ N) (hL₁ : 2 ≤ L₁) (hL₂ : 2 ≤ L₂)
    (hshifts : L₁ + L₂ ≤ N)
    (hsmall : 6 * X * L₁ * L₂ / (A : ℝ) ^ 4 ≤ 1 / 2) :
    (L₁ : ℝ) ^ 4 * (L₂ : ℝ) ^ 2 *
        ‖∑ i ∈ Finset.range N, e (reciprocalPhase X A i)‖ ^ 4 ≤
      2 * (L₂ : ℝ) ^ 2 *
          (2 * (L₁ : ℝ) * (N : ℝ) ^ 2) ^ 2 +
        2 * (4 * (N : ℝ) * (L₁ : ℝ)) ^ 2 *
          ((Finset.Icc 1 (L₁ - 1)).card : ℝ) *
            ∑ ℓ₁ ∈ Finset.Icc 1 (L₁ - 1),
              reciprocalThirdStageMajorant X A N L₂ ℓ₁ := by
  let u : ℕ → ℂ := fun n ↦ e (reciprocalPhase X A (n - 1))
  let S : ℝ := ‖∑ i ∈ Finset.range N, e (reciprocalPhase X A i)‖
  let D : ℝ := 2 * (L₁ : ℝ) * (N : ℝ) ^ 2
  let E : ℝ := 4 * (N : ℝ) * (L₁ : ℝ)
  let C : ℕ → ℝ := fun ℓ ↦
    ‖∑ n ∈ Finset.Icc 1 (N - ℓ),
      u n * conj (u (n + ℓ))‖
  let T : ℝ := ∑ ℓ ∈ Finset.Icc 1 (L₁ - 1), C ℓ
  have hL₁N : L₁ ≤ N := by omega
  have hu : ∀ n ∈ Finset.Icc 1 N, ‖u n‖ ≤ 1 := by
    intro n hn
    simp [u]
  have hmainSum :
      (∑ i ∈ Finset.range N, e (reciprocalPhase X A i)) =
        ∑ n ∈ Finset.Icc 1 N, u n := by
    rw [sum_Icc_one_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [u]
    rw [show i + 1 - 1 = i by omega]
  have hfirst := vdc_norm_sq_mul_le u (by omega) hL₁N hu
  rw [← hmainSum] at hfirst
  have hfirst' : (L₁ : ℝ) ^ 2 * S ^ 2 ≤ D + E * T := by
    simpa only [S, D, E, C, T] using hfirst
  have hCnonneg : ∀ ℓ, 0 ≤ C ℓ := fun ℓ ↦ norm_nonneg _
  have hTnonneg : 0 ≤ T := Finset.sum_nonneg fun ℓ hℓ ↦ hCnonneg ℓ
  have hDnonneg : 0 ≤ D := by dsimp [D]; positivity
  have hEnonneg : 0 ≤ E := by dsimp [E]; positivity
  have hfirstSq :
      ((L₁ : ℝ) ^ 2 * S ^ 2) ^ 2 ≤ (D + E * T) ^ 2 := by
    exact (sq_le_sq₀ (by positivity) (by positivity)).mpr hfirst'
  have hTSq : T ^ 2 ≤
      ((Finset.Icc 1 (L₁ - 1)).card : ℝ) *
        ∑ ℓ ∈ Finset.Icc 1 (L₁ - 1), (C ℓ) ^ 2 := by
    dsimp only [T]
    exact sq_sum_le_card_mul_sum_sq
  have hsecond : ∀ ℓ₁ ∈ Finset.Icc 1 (L₁ - 1),
      (L₂ : ℝ) ^ 2 * (C ℓ₁) ^ 2 ≤
        reciprocalThirdStageMajorant X A N L₂ ℓ₁ := by
    intro ℓ₁ hℓ₁mem
    have hℓ₁bounds := Finset.mem_Icc.mp hℓ₁mem
    have hℓ₁ : 0 < ℓ₁ := by omega
    have hL₂N : L₂ ≤ N - ℓ₁ := by omega
    have hv : ∀ n ∈ Finset.Icc 1 (N - ℓ₁),
        ‖reciprocalCorrelationSequence X A ℓ₁ n‖ ≤ 1 := by
      intro n hn
      simp
    have hvdc := vdc_norm_sq_mul_le
      (reciprocalCorrelationSequence X A ℓ₁) (by omega) hL₂N hv
    have hcorrEq : C ℓ₁ =
        ‖∑ n ∈ Finset.Icc 1 (N - ℓ₁),
          reciprocalCorrelationSequence X A ℓ₁ n‖ := by
      rfl
    rw [← hcorrEq] at hvdc
    have hterm : ∀ ℓ₂ ∈ Finset.Icc 1 (L₂ - 1),
        ‖∑ n ∈ Finset.Icc 1 (N - ℓ₁ - ℓ₂),
          reciprocalCorrelationSequence X A ℓ₁ n *
            conj (reciprocalCorrelationSequence X A ℓ₁ (n + ℓ₂))‖ ≤
        1 + 3 / (2 *
          (6 * X * ℓ₁ * ℓ₂ / ((A + N : ℕ) : ℝ) ^ 4)) := by
      intro ℓ₂ hℓ₂mem
      have hℓ₂bounds := Finset.mem_Icc.mp hℓ₂mem
      have hℓ₂ : 0 < ℓ₂ := by omega
      have hsum : ℓ₁ + ℓ₂ ≤ N - 2 := by omega
      have hsmall' : 6 * X * ℓ₁ * ℓ₂ / (A : ℝ) ^ 4 ≤ 1 / 2 := by
        apply (div_le_div_of_nonneg_right ?_ (by positivity)).trans hsmall
        gcongr <;> omega
      exact norm_second_reciprocal_correlation_le
        X hX hA hℓ₁ hℓ₂ hsum hsmall'
    unfold reciprocalThirdStageMajorant
    exact hvdc.trans <| add_le_add le_rfl <|
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (by positivity)
  have hsecondSum :
      (L₂ : ℝ) ^ 2 *
          (∑ ℓ₁ ∈ Finset.Icc 1 (L₁ - 1), (C ℓ₁) ^ 2) ≤
        ∑ ℓ₁ ∈ Finset.Icc 1 (L₁ - 1),
          reciprocalThirdStageMajorant X A N L₂ ℓ₁ := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hsecond
  have hscaledTSq :
      (L₂ : ℝ) ^ 2 * T ^ 2 ≤
        ((Finset.Icc 1 (L₁ - 1)).card : ℝ) *
          ((L₂ : ℝ) ^ 2 *
            ∑ ℓ₁ ∈ Finset.Icc 1 (L₁ - 1), (C ℓ₁) ^ 2) := by
    calc
      (L₂ : ℝ) ^ 2 * T ^ 2 ≤
          (L₂ : ℝ) ^ 2 *
            (((Finset.Icc 1 (L₁ - 1)).card : ℝ) *
              ∑ ℓ₁ ∈ Finset.Icc 1 (L₁ - 1), (C ℓ₁) ^ 2) :=
        mul_le_mul_of_nonneg_left hTSq (sq_nonneg _)
      _ = _ := by ring
  calc
    (L₁ : ℝ) ^ 4 * (L₂ : ℝ) ^ 2 * S ^ 4 =
        (L₂ : ℝ) ^ 2 * (((L₁ : ℝ) ^ 2 * S ^ 2) ^ 2) := by ring
    _ ≤ (L₂ : ℝ) ^ 2 * (D + E * T) ^ 2 := by gcongr
    _ ≤ (L₂ : ℝ) ^ 2 * (2 * D ^ 2 + 2 * (E * T) ^ 2) := by
      gcongr
      nlinarith [sq_nonneg (D - E * T)]
    _ = 2 * (L₂ : ℝ) ^ 2 * D ^ 2 +
        2 * E ^ 2 * ((L₂ : ℝ) ^ 2 * T ^ 2) := by ring
    _ ≤ 2 * (L₂ : ℝ) ^ 2 * D ^ 2 +
        2 * E ^ 2 *
          (((Finset.Icc 1 (L₁ - 1)).card : ℝ) *
            ((L₂ : ℝ) ^ 2 *
              ∑ ℓ₁ ∈ Finset.Icc 1 (L₁ - 1), (C ℓ₁) ^ 2)) := by
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hscaledTSq (by positivity))
    _ ≤ 2 * (L₂ : ℝ) ^ 2 * D ^ 2 +
        2 * E ^ 2 *
          (((Finset.Icc 1 (L₁ - 1)).card : ℝ) *
            ∑ ℓ₁ ∈ Finset.Icc 1 (L₁ - 1),
              reciprocalThirdStageMajorant X A N L₂ ℓ₁) := by
      exact add_le_add le_rfl <| mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hsecondSum (by positivity)) (by positivity)
    _ = _ := by
      dsimp only [D, E]
      ring

/-- The third-derivative estimate with all shift sums and cardinalities
replaced by its explicit harmonic majorant. -/
theorem reciprocal_third_derivative_bound_explicit
    (X : ℝ) (hX : 0 < X) {A N L₁ L₂ : ℕ} (hA : 0 < A)
    (hN : 4 ≤ N) (hL₁ : 2 ≤ L₁) (hL₂ : 2 ≤ L₂)
    (hshifts : L₁ + L₂ ≤ N)
    (hsmall : 6 * X * L₁ * L₂ / (A : ℝ) ^ 4 ≤ 1 / 2) :
    (L₁ : ℝ) ^ 4 * (L₂ : ℝ) ^ 2 *
        ‖∑ i ∈ Finset.range N, e (reciprocalPhase X A i)‖ ^ 4 ≤
      reciprocalThirdDerivativeMajorant X A N L₁ L₂ := by
  have hbase := reciprocal_third_derivative_bound X hX hA hN hL₁ hL₂
    hshifts hsmall
  have hsum := sum_reciprocalThirdStageMajorant_le X hX
    (A := A) (N := N) (L₁ := L₁) (L₂ := L₂) hA
  have hsumNonneg : 0 ≤
      ∑ ℓ₁ ∈ Finset.Icc 1 (L₁ - 1),
        reciprocalThirdStageMajorant X A N L₂ ℓ₁ := by
    exact Finset.sum_nonneg fun ℓ₁ hℓ₁ ↦
      reciprocalThirdStageMajorant_nonneg X hX hA (by
        have := (Finset.mem_Icc.mp hℓ₁).1
        omega)
  have hcard : ((Finset.Icc 1 (L₁ - 1)).card : ℝ) ≤ (L₁ : ℝ) := by
    exact_mod_cast (by simp : (Finset.Icc 1 (L₁ - 1)).card ≤ L₁)
  have hproduct :
      ((Finset.Icc 1 (L₁ - 1)).card : ℝ) *
          (∑ ℓ₁ ∈ Finset.Icc 1 (L₁ - 1),
            reciprocalThirdStageMajorant X A N L₂ ℓ₁) ≤
        (L₁ : ℝ) *
          ((L₁ : ℝ) *
              (2 * (L₂ : ℝ) * (N : ℝ) ^ 2 +
                4 * (N : ℝ) * (L₂ : ℝ) ^ 2) +
            4 * (N : ℝ) * (L₂ : ℝ) *
              ((((A + N : ℕ) : ℝ) ^ 4) / (4 * X)) *
              (harmonic (L₂ - 1) : ℝ) *
              (harmonic (L₁ - 1) : ℝ)) := by
    exact mul_le_mul hcard hsum hsumNonneg (by positivity)
  unfold reciprocalThirdDerivativeMajorant
  apply hbase.trans
  apply add_le_add le_rfl
  calc
    2 * (4 * (N : ℝ) * (L₁ : ℝ)) ^ 2 *
          ((Finset.Icc 1 (L₁ - 1)).card : ℝ) *
            (∑ ℓ₁ ∈ Finset.Icc 1 (L₁ - 1),
              reciprocalThirdStageMajorant X A N L₂ ℓ₁) =
        (2 * (4 * (N : ℝ) * (L₁ : ℝ)) ^ 2) *
          (((Finset.Icc 1 (L₁ - 1)).card : ℝ) *
            (∑ ℓ₁ ∈ Finset.Icc 1 (L₁ - 1),
              reciprocalThirdStageMajorant X A N L₂ ℓ₁)) := by ring
    _ ≤ (2 * (4 * (N : ℝ) * (L₁ : ℝ)) ^ 2) *
        ((L₁ : ℝ) *
          ((L₁ : ℝ) *
              (2 * (L₂ : ℝ) * (N : ℝ) ^ 2 +
                4 * (N : ℝ) * (L₂ : ℝ) ^ 2) +
            4 * (N : ℝ) * (L₂ : ℝ) *
              ((((A + N : ℕ) : ℝ) ^ 4) / (4 * X)) *
              (harmonic (L₂ - 1) : ℝ) *
              (harmonic (L₁ - 1) : ℝ))) :=
      mul_le_mul_of_nonneg_left hproduct (by positivity)
    _ = _ := by ring

/-- Each correlation arising from one van der Corput shift is bounded by
the sharp first-derivative estimate applied to its positive second
difference. -/
theorem norm_reciprocal_correlation_le
    (X : ℝ) (hX : 0 < X) {A N ℓ : ℕ} (hA : 0 < A)
    (hℓ : 0 < ℓ) (hℓN : ℓ ≤ N - 2)
    (hsmall : 2 * X * ℓ / (A : ℝ) ^ 3 ≤ 1 / 2) :
    ‖∑ n ∈ Finset.Icc 1 (N - ℓ),
        e (reciprocalPhase X A (n - 1)) *
          conj (e (reciprocalPhase X A (n + ℓ - 1)))‖ ≤
      1 + 3 / (2 * (2 * X * ℓ /
        (((A + N : ℕ) : ℝ) ^ 3))) := by
  let M := N - ℓ
  let g : ℕ → ℝ := reciprocalDifferencePhase X A ℓ
  have hM : 2 ≤ M := by omega
  have hm : 0 < 2 * X * ℓ / (((A + N : ℕ) : ℝ) ^ 3) := by
    positivity
  have hsum :
      (∑ n ∈ Finset.Icc 1 (N - ℓ),
        e (reciprocalPhase X A (n - 1)) *
          conj (e (reciprocalPhase X A (n + ℓ - 1)))) =
        ∑ i ∈ Finset.range M, e (g i) := by
    rw [sum_Icc_one_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← e_sub]
    congr 1
    simp only [g, reciprocalDifferencePhase]
    have hfirst : i + 1 - 1 = i := by omega
    have hsecond : i + 1 + ℓ - 1 = i + ℓ := by omega
    rw [hfirst, hsecond]
  rw [hsum]
  apply norm_sum_e_le_of_antitone_phaseDiff_sharp g M hM
    (2 * X * ℓ / (((A + N : ℕ) : ℝ) ^ 3)) hm
  · intro i hi
    exact reciprocalDifferencePhase_gap_lower X hX hA hℓ (by
      dsimp [M] at hi ⊢
      exact hi)
  · intro i hi
    exact (reciprocalDifferencePhase_gap_upper X hX hA hℓ).trans hsmall
  · exact reciprocalDifferencePhase_gap_antitone X hX.le hA hℓ

/-- A finite second-derivative estimate for the reciprocal phase.  It keeps
the harmonic correlation loss explicit; later parameter choices only need
the elementary bound `harmonic n ≤ 1 + log n`. -/
theorem reciprocal_second_derivative_bound
    (X : ℝ) (hX : 0 < X) {A N L : ℕ} (hA : 0 < A)
    (hN : 3 ≤ N) (hL : 2 ≤ L) (hLN : L ≤ N - 1)
    (hsmall : 2 * X * L / (A : ℝ) ^ 3 ≤ 1 / 2) :
    (L : ℝ) ^ 2 *
        ‖∑ i ∈ Finset.range N, e (reciprocalPhase X A i)‖ ^ 2 ≤
      2 * (L : ℝ) * (N : ℝ) ^ 2 +
        4 * (N : ℝ) * (L : ℝ) *
          ((L : ℝ) +
            (3 * (((A + N : ℕ) : ℝ) ^ 3) / (4 * X)) *
              (harmonic (L - 1) : ℝ)) := by
  let u : ℕ → ℂ := fun n ↦ e (reciprocalPhase X A (n - 1))
  have hLN' : L ≤ N := hLN.trans (Nat.sub_le N 1)
  have hu : ∀ n ∈ Finset.Icc 1 N, ‖u n‖ ≤ 1 := by
    intro n hn
    simp [u]
  have hvdc := vdc_norm_sq_mul_le u (by omega) hLN' hu
  have hmainSum :
      (∑ i ∈ Finset.range N, e (reciprocalPhase X A i)) =
        ∑ n ∈ Finset.Icc 1 N, u n := by
    rw [sum_Icc_one_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [u]
    rw [show i + 1 - 1 = i by omega]
  rw [← hmainSum] at hvdc
  let C : ℝ := 3 * (((A + N : ℕ) : ℝ) ^ 3) / (4 * X)
  have hC : 0 ≤ C := by positivity
  have hterm : ∀ ℓ ∈ Finset.Icc 1 (L - 1),
      ‖∑ n ∈ Finset.Icc 1 (N - ℓ), u n * conj (u (n + ℓ))‖ ≤
        1 + C * (1 / (ℓ : ℝ)) := by
    intro ℓ hℓmem
    have hℓbounds := Finset.mem_Icc.mp hℓmem
    have hℓ : 0 < ℓ := by omega
    have hℓL : ℓ ≤ L := by omega
    have hℓN : ℓ ≤ N - 2 := by omega
    have hsmallℓ : 2 * X * ℓ / (A : ℝ) ^ 3 ≤ 1 / 2 := by
      apply (div_le_div_of_nonneg_right ?_ (by positivity)).trans hsmall
      gcongr
    have hcorr := norm_reciprocal_correlation_le X hX hA hℓ hℓN hsmallℓ
    have hrewrite :
        1 + 3 / (2 * (2 * X * ℓ /
          (((A + N : ℕ) : ℝ) ^ 3))) =
          1 + C * (1 / (ℓ : ℝ)) := by
      dsimp [C]
      have hℓR : (ℓ : ℝ) ≠ 0 := by positivity
      have hAN : (((A + N : ℕ) : ℝ)) ≠ 0 := by positivity
      field_simp
      ring
    simpa only [u, hrewrite] using hcorr
  have hharm :
      (∑ ℓ ∈ Finset.Icc 1 (L - 1), (1 / (ℓ : ℝ))) =
        (harmonic (L - 1) : ℝ) := by
    simpa [one_div, harmonic_eq_sum_Icc]
  have hcorrSum :
      (∑ ℓ ∈ Finset.Icc 1 (L - 1),
        ‖∑ n ∈ Finset.Icc 1 (N - ℓ),
          u n * conj (u (n + ℓ))‖) ≤
        (L : ℝ) + C * (harmonic (L - 1) : ℝ) := by
    calc
      (∑ ℓ ∈ Finset.Icc 1 (L - 1),
        ‖∑ n ∈ Finset.Icc 1 (N - ℓ),
          u n * conj (u (n + ℓ))‖) ≤
          ∑ ℓ ∈ Finset.Icc 1 (L - 1),
            (1 + C * (1 / (ℓ : ℝ))) :=
              Finset.sum_le_sum hterm
      _ = ((Finset.Icc 1 (L - 1)).card : ℝ) +
          C * (∑ ℓ ∈ Finset.Icc 1 (L - 1), 1 / (ℓ : ℝ)) := by
            rw [Finset.sum_add_distrib]
            simp only [Finset.sum_const, nsmul_eq_mul, mul_one,
              ← Finset.mul_sum]
      _ ≤ (L : ℝ) + C * (harmonic (L - 1) : ℝ) := by
        rw [hharm]
        gcongr
        simp
  have hmul := mul_le_mul_of_nonneg_left hcorrSum
    (show 0 ≤ 4 * (N : ℝ) * (L : ℝ) by positivity)
  have hadd :
      2 * (L : ℝ) * (N : ℝ) ^ 2 +
          4 * (N : ℝ) * (L : ℝ) *
            (∑ ℓ ∈ Finset.Icc 1 (L - 1),
              ‖∑ n ∈ Finset.Icc 1 (N - ℓ),
                u n * conj (u (n + ℓ))‖) ≤
        2 * (L : ℝ) * (N : ℝ) ^ 2 +
          4 * (N : ℝ) * (L : ℝ) *
            ((L : ℝ) + C * (harmonic (L - 1) : ℝ)) := by
    gcongr
  simpa only [C] using hvdc.trans hadd

end ReciprocalExponential
end Erdos378
