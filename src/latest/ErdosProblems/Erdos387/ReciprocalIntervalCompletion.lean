/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.CyclicWeylCompletion
import Waring.Analytic.FourierCoefficientSum

/-!
# Fourier completion of a short reciprocal phase

The existing interval Fourier coefficients are independent of the completed
phase.  This file proves their exact completion identity for `c/(a+x)` and
inserts the cyclic, linearly twisted complete-sum estimate.
-/

namespace Erdos387

open scoped BigOperators

namespace ReciprocalIntervalCompletion

/-- A character sum of an arbitrary prime-field phase over
`M < x ≤ M+m`. -/
noncomputable def shortPhase
    (p : ℕ) [NeZero p] (phase : ZMod p → ZMod p)
    (M : ℤ) (m : ℕ) : ℂ :=
  ∑ x ∈ Finset.Ioc M (M + m), ZMod.stdAddChar (phase (x : ZMod p))

/-- The complete linear Fourier twist of an arbitrary phase. -/
noncomputable def completeTwistedPhase
    (p : ℕ) [NeZero p] (phase : ZMod p → ZMod p)
    (h : ZMod p) : ℂ :=
  ∑ y : ZMod p, ZMod.stdAddChar (h * y + phase y)

private theorem sum_frequency_mul_completeTwistedPhase
    (p : ℕ) [NeZero p] (phase : ZMod p → ZMod p) (x : ℤ) :
    ∑ h : ZMod p,
        ZMod.stdAddChar (-(h * (x : ZMod p))) *
          completeTwistedPhase p phase h =
      (p : ℂ) * ZMod.stdAddChar (phase (x : ZMod p)) := by
  simp_rw [completeTwistedPhase, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    ∑ y : ZMod p, ∑ h : ZMod p,
        ZMod.stdAddChar (-(h * (x : ZMod p))) *
          ZMod.stdAddChar (h * y + phase y) =
      ∑ y : ZMod p, ZMod.stdAddChar (phase y) *
        ∑ h : ZMod p,
          ZMod.stdAddChar (h * (y - (x : ZMod p))) := by
      apply Finset.sum_congr rfl
      intro y _hy
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _hh
      rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
      congr 1
      ring
    _ = ∑ y : ZMod p, ZMod.stdAddChar (phase y) *
        (if y - (x : ZMod p) = 0 then (p : ℂ) else 0) := by
      apply Finset.sum_congr rfl
      intro y _hy
      rw [AdditiveOrthogonality.sum_stdAddChar_mul]
    _ = (p : ℂ) * ZMod.stdAddChar (phase (x : ZMod p)) := by
      simp only [sub_eq_zero]
      simp
      ring

/-- Phase-generic finite Fourier completion. -/
theorem shortPhase_eq_complete
    (p : ℕ) [NeZero p] (phase : ZMod p → ZMod p)
    (M : ℤ) (m : ℕ) :
    shortPhase p phase M m =
      (p : ℂ)⁻¹ * ∑ h : ZMod p,
        Waring.Analytic.intervalFourierCoefficient M m h *
          completeTwistedPhase p phase h := by
  unfold shortPhase Waring.Analytic.intervalFourierCoefficient
  symm
  calc
    (p : ℂ)⁻¹ * ∑ h : ZMod p,
        (∑ x ∈ Finset.Ioc M (M + m),
          ZMod.stdAddChar (-(h * (x : ZMod p)))) *
          completeTwistedPhase p phase h =
      (p : ℂ)⁻¹ * ∑ h : ZMod p,
        ∑ x ∈ Finset.Ioc M (M + m),
          ZMod.stdAddChar (-(h * (x : ZMod p))) *
            completeTwistedPhase p phase h := by
      simp_rw [Finset.sum_mul]
    _ = (p : ℂ)⁻¹ * ∑ x ∈ Finset.Ioc M (M + m),
        ∑ h : ZMod p,
          ZMod.stdAddChar (-(h * (x : ZMod p))) *
            completeTwistedPhase p phase h := by
      congr 1
      rw [Finset.sum_comm]
    _ = (p : ℂ)⁻¹ * ∑ x ∈ Finset.Ioc M (M + m),
        (p : ℂ) * ZMod.stdAddChar (phase (x : ZMod p)) := by
      apply congrArg ((p : ℂ)⁻¹ * ·)
      apply Finset.sum_congr rfl
      intro x _hx
      exact sum_frequency_mul_completeTwistedPhase p phase x
    _ = ∑ x ∈ Finset.Ioc M (M + m),
        ZMod.stdAddChar (phase (x : ZMod p)) := by
      rw [← Finset.mul_sum]
      have hp : (p : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne p
      rw [← mul_assoc, inv_mul_cancel₀ hp, one_mul]

/-- The zero-based natural interval is the integer interval
`-1 < x ≤ -1+m` used by the Fourier coefficient API. -/
theorem sum_range_eq_shortPhase_neg_one
    (p : ℕ) [NeZero p] (phase : ZMod p → ZMod p) (m : ℕ) :
    (∑ x ∈ Finset.range m, ZMod.stdAddChar (phase (x : ZMod p))) =
      shortPhase p phase (-1) m := by
  unfold shortPhase
  apply Finset.sum_bij (fun (x : ℕ) _hx => (x : ℤ))
  · intro x hx
    rw [Finset.mem_Ioc]
    have hxm : x < m := Finset.mem_range.mp hx
    constructor <;> norm_num <;> omega
  · intro x₁ hx₁ x₂ hx₂ hcast
    exact_mod_cast hcast
  · intro x hx
    rw [Finset.mem_Ioc] at hx
    have hx0 : 0 ≤ x := by omega
    refine ⟨x.toNat, Finset.mem_range.mpr ?_, ?_⟩
    · have hxUpper : x < m := by omega
      rw [← Int.toNat_of_nonneg hx0] at hxUpper
      exact_mod_cast hxUpper
    · exact Int.toNat_of_nonneg hx0
  · intro x hx
    simp

/-- A uniform bound for all complete linear twists gives an incomplete
bound with only the standard logarithmic Fourier loss. -/
theorem norm_shortPhase_le_log_of_complete_bound
    (p : ℕ) [NeZero p] (phase : ZMod p → ZMod p)
    (M : ℤ) (m : ℕ) (B : ℝ) (hm : m ≤ p) (hB : 0 ≤ B)
    (hcomplete : ∀ h : ZMod p, ‖completeTwistedPhase p phase h‖ ≤ B) :
    ‖shortPhase p phase M m‖ ≤ (Real.log p + 1) * B := by
  rw [shortPhase_eq_complete]
  have hpReal : (p : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  calc
    ‖(p : ℂ)⁻¹ * ∑ h : ZMod p,
        Waring.Analytic.intervalFourierCoefficient M m h *
          completeTwistedPhase p phase h‖ =
      (p : ℝ)⁻¹ * ‖∑ h : ZMod p,
        Waring.Analytic.intervalFourierCoefficient M m h *
          completeTwistedPhase p phase h‖ := by
        rw [norm_mul, norm_inv, Complex.norm_natCast]
    _ ≤ (p : ℝ)⁻¹ * ∑ h : ZMod p,
        ‖Waring.Analytic.intervalFourierCoefficient M m h *
          completeTwistedPhase p phase h‖ := by
      exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ = (p : ℝ)⁻¹ * ∑ h : ZMod p,
        ‖Waring.Analytic.intervalFourierCoefficient M m h‖ *
          ‖completeTwistedPhase p phase h‖ := by simp only [norm_mul]
    _ ≤ (p : ℝ)⁻¹ * ∑ h : ZMod p,
        ‖Waring.Analytic.intervalFourierCoefficient M m h‖ * B := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum fun h _ =>
        mul_le_mul_of_nonneg_left (hcomplete h) (norm_nonneg _)
    _ = (p : ℝ)⁻¹ *
        (∑ h : ZMod p,
          ‖Waring.Analytic.intervalFourierCoefficient M m h‖) * B := by
      rw [← Finset.sum_mul]
      ring
    _ ≤ (p : ℝ)⁻¹ * ((p : ℝ) * (Real.log p + 1)) * B := by
      apply mul_le_mul_of_nonneg_right _ hB
      exact mul_le_mul_of_nonneg_left
        (Waring.Analytic.sum_norm_intervalFourierCoefficient_le p M m hm)
        (by positivity)
    _ = (Real.log p + 1) * B := by field_simp

/-- Reciprocal character sum over the integer interval `M < x ≤ M+m`. -/
noncomputable def shortInversePhase
    (p : ℕ) [NeZero p] (c a : ZMod p) (M : ℤ) (m : ℕ) : ℂ :=
  ∑ x ∈ Finset.Ioc M (M + m),
    ZMod.stdAddChar (c * (a + (x : ZMod p))⁻¹)

/-- The completed sum with linear Fourier frequency `h`. -/
noncomputable def completeTwistedInversePhase
    (p : ℕ) [NeZero p] (c a h : ZMod p) : ℂ :=
  ∑ y : ZMod p, CyclicWeyl.twistedInversePhase p c a h y

/-- Orthogonality at one integer point, in exactly the sign convention of
`Waring.Analytic.intervalFourierCoefficient`. -/
private theorem sum_frequency_mul_completeTwistedInversePhase
    (p : ℕ) [NeZero p] (c a : ZMod p) (x : ℤ) :
    ∑ h : ZMod p,
        ZMod.stdAddChar (-(h * (x : ZMod p))) *
          completeTwistedInversePhase p c a h =
      (p : ℂ) * ZMod.stdAddChar (c * (a + (x : ZMod p))⁻¹) := by
  simp_rw [completeTwistedInversePhase,
    CyclicWeyl.twistedInversePhase, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    ∑ y : ZMod p, ∑ h : ZMod p,
        ZMod.stdAddChar (-(h * (x : ZMod p))) *
          ZMod.stdAddChar (h * y + c * (a + y)⁻¹) =
      ∑ y : ZMod p,
        ZMod.stdAddChar (c * (a + y)⁻¹) *
          ∑ h : ZMod p,
            ZMod.stdAddChar (h * (y - (x : ZMod p))) := by
      apply Finset.sum_congr rfl
      intro y _hy
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _hh
      rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
      congr 1
      ring
    _ = ∑ y : ZMod p,
        ZMod.stdAddChar (c * (a + y)⁻¹) *
          (if y - (x : ZMod p) = 0 then (p : ℂ) else 0) := by
      apply Finset.sum_congr rfl
      intro y _hy
      rw [AdditiveOrthogonality.sum_stdAddChar_mul]
    _ = (p : ℂ) *
        ZMod.stdAddChar (c * (a + (x : ZMod p))⁻¹) := by
      simp only [sub_eq_zero]
      simp
      ring

/-- Exact Fourier completion of the short reciprocal sum. -/
theorem shortInversePhase_eq_complete
    (p : ℕ) [NeZero p] (c a : ZMod p) (M : ℤ) (m : ℕ) :
    shortInversePhase p c a M m =
      (p : ℂ)⁻¹ * ∑ h : ZMod p,
        Waring.Analytic.intervalFourierCoefficient M m h *
          completeTwistedInversePhase p c a h := by
  unfold shortInversePhase Waring.Analytic.intervalFourierCoefficient
  symm
  calc
    (p : ℂ)⁻¹ * ∑ h : ZMod p,
        (∑ x ∈ Finset.Ioc M (M + m),
          ZMod.stdAddChar (-(h * (x : ZMod p)))) *
          completeTwistedInversePhase p c a h =
      (p : ℂ)⁻¹ * ∑ h : ZMod p,
        ∑ x ∈ Finset.Ioc M (M + m),
          ZMod.stdAddChar (-(h * (x : ZMod p))) *
            completeTwistedInversePhase p c a h := by
      simp_rw [Finset.sum_mul]
    _ = (p : ℂ)⁻¹ * ∑ x ∈ Finset.Ioc M (M + m),
        ∑ h : ZMod p,
          ZMod.stdAddChar (-(h * (x : ZMod p))) *
            completeTwistedInversePhase p c a h := by
      congr 1
      rw [Finset.sum_comm]
    _ = (p : ℂ)⁻¹ * ∑ x ∈ Finset.Ioc M (M + m),
        (p : ℂ) *
          ZMod.stdAddChar (c * (a + (x : ZMod p))⁻¹) := by
      apply congrArg ((p : ℂ)⁻¹ * ·)
      apply Finset.sum_congr rfl
      intro x _hx
      exact sum_frequency_mul_completeTwistedInversePhase p c a x
    _ = ∑ x ∈ Finset.Ioc M (M + m),
        ZMod.stdAddChar (c * (a + (x : ZMod p))⁻¹) := by
      rw [← Finset.mul_sum]
      have hp : (p : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne p
      rw [← mul_assoc, inv_mul_cancel₀ hp, one_mul]

/-- Explicit bound furnished by one cyclic difference of the completed
linearly twisted reciprocal phase. -/
noncomputable def completeBound (p : ℕ) : ℝ :=
  Real.sqrt ((p : ℝ) + (p - 1 : ℕ) *
    ((3 : ℝ) * Real.sqrt (p : ℝ) + 2))

theorem completeBound_nonneg (p : ℕ) : 0 ≤ completeBound p := by
  exact Real.sqrt_nonneg _

/-- Uniform completed-sum bound, obtained from the checked cyclic square
estimate. -/
theorem norm_completeTwistedInversePhase_le
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (hp : 2 < p) {c : ZMod p} (hc : c ≠ 0) (a h : ZMod p) :
    ‖completeTwistedInversePhase p c a h‖ ≤ completeBound p := by
  have hsquare := CyclicWeyl.norm_sum_twistedInversePhase_sq_le
    hp hc a h
  have hradicand : 0 ≤
      (p : ℝ) + (p - 1 : ℕ) *
        ((3 : ℝ) * Real.sqrt (p : ℝ) + 2) := by positivity
  have hsqrt : (completeBound p) ^ 2 =
      (p : ℝ) + (p - 1 : ℕ) *
        ((3 : ℝ) * Real.sqrt (p : ℝ) + 2) := by
    rw [completeBound, Real.sq_sqrt hradicand]
  dsimp only [completeTwistedInversePhase]
  nlinarith [norm_nonneg
    (∑ x : ZMod p, CyclicWeyl.twistedInversePhase p c a h x),
    completeBound_nonneg p]

/-- The exact completion identity and the `L¹` norm of interval Fourier
coefficients give a logarithmic-loss incomplete reciprocal bound. -/
theorem norm_shortInversePhase_le
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (hp : 2 < p) {c : ZMod p} (hc : c ≠ 0)
    (a : ZMod p) (M : ℤ) (m : ℕ) (hm : m ≤ p) :
    ‖shortInversePhase p c a M m‖ ≤
      (Real.log p + 1) * completeBound p := by
  rw [shortInversePhase_eq_complete]
  have hcomplete : ∀ h : ZMod p,
      ‖completeTwistedInversePhase p c a h‖ ≤ completeBound p :=
    fun h => norm_completeTwistedInversePhase_le hp hc a h
  have hq : (p : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  have hB : 0 ≤ completeBound p := completeBound_nonneg p
  calc
    ‖(p : ℂ)⁻¹ * ∑ h : ZMod p,
        Waring.Analytic.intervalFourierCoefficient M m h *
          completeTwistedInversePhase p c a h‖ =
      (p : ℝ)⁻¹ * ‖∑ h : ZMod p,
        Waring.Analytic.intervalFourierCoefficient M m h *
          completeTwistedInversePhase p c a h‖ := by
        rw [norm_mul, norm_inv, Complex.norm_natCast]
    _ ≤ (p : ℝ)⁻¹ * ∑ h : ZMod p,
        ‖Waring.Analytic.intervalFourierCoefficient M m h *
          completeTwistedInversePhase p c a h‖ := by
      exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ = (p : ℝ)⁻¹ * ∑ h : ZMod p,
        ‖Waring.Analytic.intervalFourierCoefficient M m h‖ *
          ‖completeTwistedInversePhase p c a h‖ := by
      simp only [norm_mul]
    _ ≤ (p : ℝ)⁻¹ * ∑ h : ZMod p,
        ‖Waring.Analytic.intervalFourierCoefficient M m h‖ *
          completeBound p := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum fun h _ =>
        mul_le_mul_of_nonneg_left (hcomplete h) (norm_nonneg _)
    _ = (p : ℝ)⁻¹ *
        (∑ h : ZMod p,
          ‖Waring.Analytic.intervalFourierCoefficient M m h‖) *
          completeBound p := by
      rw [← Finset.sum_mul]
      ring
    _ ≤ (p : ℝ)⁻¹ * ((p : ℝ) * (Real.log p + 1)) *
        completeBound p := by
      apply mul_le_mul_of_nonneg_right _ hB
      exact mul_le_mul_of_nonneg_left
        (Waring.Analytic.sum_norm_intervalFourierCoefficient_le p M m hm)
        (by positivity)
    _ = (Real.log p + 1) * completeBound p := by
      field_simp

end ReciprocalIntervalCompletion

end Erdos387
