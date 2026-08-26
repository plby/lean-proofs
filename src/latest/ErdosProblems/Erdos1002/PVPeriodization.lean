import ErdosProblems.Erdos1002.PrincipalValueTransform
import ErdosProblems.Erdos1002.RamanujanSums
import ErdosProblems.Erdos1002.HStar
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Principal-value periodization and Fourier coefficients

This file makes the periodization step in Lemma 2.1 explicit.  The integer
`residueCutoffQ p a R r` runs through `q = a + pj`, `-R ≤ j ≤ R`.
Fourier coefficients are first computed for this finite sum.  Only after that
calculation do we pass to the principal-value limit.
-/

open Filter MeasureTheory Set
open scoped BigOperators ComplexConjugate ENNReal Real

namespace Erdos1002

noncomputable section

set_option linter.unnecessarySimpa false

/-- The manuscript's unit-period Fourier coefficient, written directly as
an interval integral against `e(-nα)`. -/
def unitFourierCoefficient (f : ℝ → ℂ) (n : ℕ) : ℂ :=
  ∫ α in (0 : ℝ)..1, f α * paperExp (-(n : ℝ) * α)

/-- The same coefficient with an integer frequency, used only to record the
negative-frequency conjugacy at the end. -/
def unitFourierCoefficientInt (f : ℝ → ℂ) (n : ℤ) : ℂ :=
  ∫ α in (0 : ℝ)..1, f α * paperExp (-(n : ℝ) * α)

/-- The integer `q = a + p(R-r)`.  As `r` runs through
`0, ..., 2R`, this is exactly `a + pj` with `-R ≤ j ≤ R`, in
decreasing order of `q` and hence increasing order after the substitution
`x = pα-q`. -/
def residueCutoffQ (p a R r : ℕ) : ℤ :=
  (a : ℤ) + (p : ℤ) * ((R : ℤ) - (r : ℤ))

/-- One summand `p⁻¹ h_N(pα-q)` of the finite periodization. -/
def periodizationCell (N p : ℕ) (q : ℤ) (α : ℝ) : ℂ :=
  ((1 / (p : ℝ) : ℝ) : ℂ) *
    (transformKernel N ((p : ℝ) * α - (q : ℝ)) : ℂ)

/-- The explicit symmetric cutoff in one reduced residue class. -/
def residuePeriodizationTruncation (N p a R : ℕ) (α : ℝ) : ℂ :=
  ∑ r ∈ Finset.range (2 * R + 1), periodizationCell N p (residueCutoffQ p a R r) α

/-- The finite `p ≤ P` periodization with an explicit symmetric cutoff in
every reduced residue class. -/
def pvPeriodizationTruncation (N P R : ℕ) (α : ℝ) : ℂ :=
  ∑ p ∈ Finset.Icc 1 P,
    ∑ a ∈ reducedResidues p, residuePeriodizationTruncation N p a R α

/-- The real-line integrand obtained after the affine change of variables in
the `n`-th coefficient of the `p`-th periodization. -/
def periodizedTransformIntegrand (N n p : ℕ) (x : ℝ) : ℂ :=
  (transformKernel N x : ℂ) * paperExp (-((n : ℝ) / (p : ℝ)) * x)

private theorem paperExp_add (u v : ℝ) :
    paperExp u * paperExp v = paperExp (u + v) := by
  unfold paperExp
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem continuous_paperExp_local : Continuous paperExp := by
  unfold paperExp
  fun_prop

private theorem norm_paperExp_local (t : ℝ) : ‖paperExp t‖ = 1 := by
  rw [paperExp, Complex.norm_exp]
  simp

private theorem transformKernel_measurable_local (N : ℕ) :
    Measurable (transformKernel N) := by
  unfold transformKernel
  exact Measurable.ite (by simpa only [Set.setOf_eq_eq_singleton] using!
      (measurableSet_singleton (0 : ℝ))) measurable_const
    ((bernoulliMark_measurable.comp (measurable_const.mul measurable_id)).div measurable_id)

private theorem norm_transformKernel_le_half_N (N : ℕ) (x : ℝ) :
    ‖transformKernel N x‖ ≤ (N : ℝ) / 2 := by
  by_cases hx : x = 0
  · simp [transformKernel, hx, div_nonneg]
  · rw [transformKernel, if_neg hx, Real.norm_eq_abs, abs_div,
      abs_of_nonneg (bernoulliMark_nonneg _)]
    have hxabs : 0 < |x| := abs_pos.mpr hx
    apply (div_le_iff₀ hxabs).2
    have hmark : bernoulliMark ((N : ℝ) * x) ≤ |(N : ℝ) * x| / 2 := by
      rcases le_total 0 ((N : ℝ) * x) with hy | hy
      · have hfloor : (0 : ℝ) ≤ (⌊(N : ℝ) * x⌋ : ℤ) := by
          exact_mod_cast Int.floor_nonneg.mpr hy
        have hfract_le : Int.fract ((N : ℝ) * x) ≤ (N : ℝ) * x := by
          rw [Int.fract]
          linarith
        rw [abs_of_nonneg hy]
        dsimp [bernoulliMark]
        nlinarith [Int.fract_nonneg ((N : ℝ) * x),
          (Int.fract_lt_one ((N : ℝ) * x)).le]
      · have hny : 0 ≤ -((N : ℝ) * x) := neg_nonneg.mpr hy
        rw [← bernoulliMark_neg ((N : ℝ) * x), ← abs_neg ((N : ℝ) * x),
          abs_of_nonneg hny]
        have hfloor : (0 : ℝ) ≤ (⌊-((N : ℝ) * x)⌋ : ℤ) := by
          exact_mod_cast Int.floor_nonneg.mpr hny
        have hfract_le : Int.fract (-((N : ℝ) * x)) ≤ -((N : ℝ) * x) := by
          rw [Int.fract]
          linarith
        dsimp [bernoulliMark]
        nlinarith [Int.fract_nonneg (-((N : ℝ) * x)),
          (Int.fract_lt_one (-((N : ℝ) * x))).le]
    calc
      bernoulliMark ((N : ℝ) * x) ≤ |(N : ℝ) * x| / 2 := hmark
      _ = ((N : ℝ) / 2) * |x| := by
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg N)]
        ring

private theorem periodizedTransformIntegrand_intervalIntegrable
    (N n p : ℕ) (a b : ℝ) :
    IntervalIntegrable (periodizedTransformIntegrand N n p) volume a b := by
  apply (intervalIntegrable_const (c := ((N : ℝ) / 2))).mono_fun
  · exact ((transformKernel_measurable_local N).complex_ofReal.mul
      (continuous_paperExp_local.comp
        (continuous_const.mul continuous_id)).measurable).aestronglyMeasurable
  · filter_upwards with x
    rw [periodizedTransformIntegrand, norm_mul, Complex.norm_real,
      norm_paperExp_local, mul_one]
    have hN : 0 ≤ (N : ℝ) / 2 := div_nonneg (Nat.cast_nonneg N) (by norm_num)
    change |transformKernel N x| ≤ |(N : ℝ) / 2|
    rw [abs_of_nonneg hN]
    simpa only [Real.norm_eq_abs] using! norm_transformKernel_le_half_N N x

private theorem periodization_phase_split (n p : ℕ) (q : ℤ) (α : ℝ)
    (hp : 0 < p) :
    paperExp (-(n : ℝ) * α) =
      paperExp (-(n : ℝ) * (q : ℝ) / (p : ℝ)) *
        paperExp (-((n : ℝ) / (p : ℝ)) * ((p : ℝ) * α - (q : ℝ))) := by
  rw [paperExp_add]
  congr 1
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  field_simp [hpR]
  ring

/-- Fourier coefficient of one finite `q`-cell, computed before any
principal-value limit. -/
theorem unitFourierCoefficient_periodizationCell
    (N n p : ℕ) (q : ℤ) (hp : 0 < p) :
    unitFourierCoefficient (periodizationCell N p q) n =
      ((1 / (p : ℝ) ^ 2 : ℝ) : ℂ) *
        paperExp (-(n : ℝ) * (q : ℝ) / (p : ℝ)) *
          (∫ x in -(q : ℝ)..(p : ℝ) - (q : ℝ),
            periodizedTransformIntegrand N n p x) := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  unfold unitFourierCoefficient periodizationCell
  calc
    (∫ α in (0 : ℝ)..1,
        ((1 / (p : ℝ) : ℝ) : ℂ) *
          (transformKernel N ((p : ℝ) * α - (q : ℝ)) : ℂ) *
            paperExp (-(n : ℝ) * α)) =
      ∫ α in (0 : ℝ)..1,
        (((1 / (p : ℝ) : ℝ) : ℂ) *
          paperExp (-(n : ℝ) * (q : ℝ) / (p : ℝ))) *
            periodizedTransformIntegrand N n p ((p : ℝ) * α - (q : ℝ)) := by
      apply intervalIntegral.integral_congr
      intro α hα
      simp only [periodizedTransformIntegrand]
      rw [periodization_phase_split n p q α hp]
      ring
    _ = (((1 / (p : ℝ) : ℝ) : ℂ) *
          paperExp (-(n : ℝ) * (q : ℝ) / (p : ℝ))) *
        (∫ α in (0 : ℝ)..1,
          periodizedTransformIntegrand N n p ((p : ℝ) * α - (q : ℝ))) := by
      rw [intervalIntegral.integral_const_mul]
    _ = (((1 / (p : ℝ) : ℝ) : ℂ) *
          paperExp (-(n : ℝ) * (q : ℝ) / (p : ℝ))) *
        ((p : ℝ)⁻¹ •
          (∫ x in -(q : ℝ)..(p : ℝ) - (q : ℝ),
            periodizedTransformIntegrand N n p x)) := by
      rw [intervalIntegral.integral_comp_mul_sub
        (periodizedTransformIntegrand N n p) hpR (q : ℝ)]
      norm_num
    _ = ((1 / (p : ℝ) ^ 2 : ℝ) : ℂ) *
        paperExp (-(n : ℝ) * (q : ℝ) / (p : ℝ)) *
          (∫ x in -(q : ℝ)..(p : ℝ) - (q : ℝ),
            periodizedTransformIntegrand N n p x) := by
      rw [Complex.real_smul]
      push_cast
      field_simp [hpR]

private theorem paperExp_int_local (z : ℤ) : paperExp (z : ℝ) = 1 := by
  unfold paperExp
  convert! Complex.exp_int_mul_two_pi_mul_I z using 2
  push_cast
  ring

private theorem residueCutoffQ_phase (n p a R r : ℕ) (hp : 0 < p) :
    paperExp (-(n : ℝ) * (residueCutoffQ p a R r : ℝ) / (p : ℝ)) =
      paperExp (-(n : ℝ) * (a : ℝ) / (p : ℝ)) := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  let z : ℤ := -(n : ℤ) * ((R : ℤ) - (r : ℤ))
  have harg :
      -(n : ℝ) * (residueCutoffQ p a R r : ℝ) / (p : ℝ) =
        -(n : ℝ) * (a : ℝ) / (p : ℝ) + (z : ℝ) := by
    dsimp [residueCutoffQ, z]
    push_cast
    field_simp [hpR]
    ring
  rw [harg, ← paperExp_add, paperExp_int_local, mul_one]

private theorem periodizationCellFourier_intervalIntegrable
    (N n p : ℕ) (q : ℤ) :
    IntervalIntegrable
      (fun α => periodizationCell N p q α * paperExp (-(n : ℝ) * α)) volume 0 1 := by
  let C : ℝ := |1 / (p : ℝ)| * ((N : ℝ) / 2)
  have hC : 0 ≤ C := mul_nonneg (abs_nonneg _) (div_nonneg (Nat.cast_nonneg N) (by norm_num))
  apply (intervalIntegrable_const (c := C)).mono_fun
  · exact (((transformKernel_measurable_local N).comp
        (measurable_const.mul measurable_id |>.sub measurable_const)).complex_ofReal.const_mul
          ((1 / (p : ℝ) : ℝ) : ℂ) |>.mul
        (continuous_paperExp_local.comp
          (continuous_const.mul continuous_id)).measurable).aestronglyMeasurable
  · filter_upwards with α
    rw [periodizationCell, norm_mul, norm_mul, Complex.norm_real,
      Complex.norm_real, norm_paperExp_local, mul_one]
    calc
      |1 / (p : ℝ)| * |transformKernel N ((p : ℝ) * α - (q : ℝ))| ≤
          |1 / (p : ℝ)| * ((N : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left
          (by simpa only [Real.norm_eq_abs] using!
            norm_transformKernel_le_half_N N ((p : ℝ) * α - (q : ℝ)))
          (abs_nonneg _)
      _ = C := rfl
      _ = |C| := (abs_of_nonneg hC).symm

private theorem intervalIntegrable_finsetSum
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℝ → ℂ) (u v : ℝ)
    (hf : ∀ i ∈ s, IntervalIntegrable (f i) volume u v) :
    IntervalIntegrable (fun x => ∑ i ∈ s, f i x) volume u v := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp only [Finset.mem_insert] at hf
      simp only [Finset.sum_insert hi]
      exact (hf i (Or.inl rfl)).add (ih fun j hj => hf j (Or.inr hj))

private theorem residuePeriodizationFourier_intervalIntegrable
    (N n p a R : ℕ) :
    IntervalIntegrable
      (fun α => residuePeriodizationTruncation N p a R α *
        paperExp (-(n : ℝ) * α)) volume 0 1 := by
  unfold residuePeriodizationTruncation
  simp_rw [Finset.sum_mul]
  exact intervalIntegrable_finsetSum (Finset.range (2 * R + 1))
    (fun r α => periodizationCell N p (residueCutoffQ p a R r) α *
      paperExp (-(n : ℝ) * α)) 0 1
    (fun r _hr => periodizationCellFourier_intervalIntegrable N n p
      (residueCutoffQ p a R r))

private theorem unitFourierCoefficient_residuePeriodizationTruncation_sum
    (N n p a R : ℕ) :
    unitFourierCoefficient (residuePeriodizationTruncation N p a R) n =
      ∑ r ∈ Finset.range (2 * R + 1),
        unitFourierCoefficient (periodizationCell N p (residueCutoffQ p a R r)) n := by
  unfold unitFourierCoefficient residuePeriodizationTruncation
  simp_rw [Finset.sum_mul]
  exact intervalIntegral.integral_finset_sum fun r hr =>
    periodizationCellFourier_intervalIntegrable N n p (residueCutoffQ p a R r)

private theorem sum_range_adjacent_intervalIntegrals
    (f : ℝ → ℂ) (c d : ℝ) (m : ℕ)
    (hlocal : ∀ u v : ℝ, IntervalIntegrable f volume u v) :
    (∑ r ∈ Finset.range m,
      ∫ x in c + d * (r : ℝ)..c + d * (r + 1 : ℕ), f x) =
      ∫ x in c..c + d * m, f x := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      have hadd := intervalIntegral.integral_add_adjacent_intervals
        (hlocal c (c + d * m)) (hlocal (c + d * m) (c + d * (m + 1)))
      convert! hadd using 1 <;> push_cast <;> ring

private theorem residueCutoffQ_cell_left (p a R r : ℕ) :
    -(residueCutoffQ p a R r : ℝ) =
      -(a : ℝ) - (p : ℝ) * R + (p : ℝ) * r := by
  simp only [residueCutoffQ]
  push_cast
  ring

private theorem residueCutoffQ_cell_right (p a R r : ℕ) :
    (p : ℝ) - (residueCutoffQ p a R r : ℝ) =
      -(a : ℝ) - (p : ℝ) * R + (p : ℝ) * ((r + 1 : ℕ) : ℝ) := by
  have hleft := residueCutoffQ_cell_left p a R r
  push_cast at hleft ⊢
  linarith

/-- The transformed cells for `q = a + pj`, `|j| ≤ R`, tile one
explicit interval. -/
theorem sum_residueCutoffQ_transformIntegrals (N n p a R : ℕ) :
    (∑ r ∈ Finset.range (2 * R + 1),
      ∫ x in -(residueCutoffQ p a R r : ℝ)..
          (p : ℝ) - (residueCutoffQ p a R r : ℝ),
        periodizedTransformIntegrand N n p x) =
      ∫ x in -(a : ℝ) - (p : ℝ) * R..
          (p : ℝ) - (a : ℝ) + (p : ℝ) * R,
        periodizedTransformIntegrand N n p x := by
  have htile := sum_range_adjacent_intervalIntegrals
    (periodizedTransformIntegrand N n p)
    (-(a : ℝ) - (p : ℝ) * R) (p : ℝ) (2 * R + 1)
    (periodizedTransformIntegrand_intervalIntegrable N n p)
  calc
    (∑ r ∈ Finset.range (2 * R + 1),
      ∫ x in -(residueCutoffQ p a R r : ℝ)..
          (p : ℝ) - (residueCutoffQ p a R r : ℝ),
        periodizedTransformIntegrand N n p x) =
      ∑ r ∈ Finset.range (2 * R + 1),
        ∫ x in -(a : ℝ) - (p : ℝ) * R + (p : ℝ) * r..
            -(a : ℝ) - (p : ℝ) * R + (p : ℝ) * ((r + 1 : ℕ) : ℝ),
          periodizedTransformIntegrand N n p x := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [residueCutoffQ_cell_left, residueCutoffQ_cell_right]
    _ = ∫ x in -(a : ℝ) - (p : ℝ) * R..
          -(a : ℝ) - (p : ℝ) * R + (p : ℝ) * ((2 * R + 1 : ℕ) : ℝ),
        periodizedTransformIntegrand N n p x := htile
    _ = ∫ x in -(a : ℝ) - (p : ℝ) * R..
          (p : ℝ) - (a : ℝ) + (p : ℝ) * R,
        periodizedTransformIntegrand N n p x := by
      congr 1
      push_cast
      ring

/-- Exact coefficient of one reduced residue cutoff. -/
theorem unitFourierCoefficient_residuePeriodizationTruncation
    (N n p a R : ℕ) (hp : 0 < p) :
    unitFourierCoefficient (residuePeriodizationTruncation N p a R) n =
      ((1 / (p : ℝ) ^ 2 : ℝ) : ℂ) *
        paperExp (-(n : ℝ) * (a : ℝ) / (p : ℝ)) *
          (∫ x in -(a : ℝ) - (p : ℝ) * R..
              (p : ℝ) - (a : ℝ) + (p : ℝ) * R,
            periodizedTransformIntegrand N n p x) := by
  rw [unitFourierCoefficient_residuePeriodizationTruncation_sum N n p a R]
  simp_rw [unitFourierCoefficient_periodizationCell N n p _ hp,
    residueCutoffQ_phase n p a R _ hp]
  rw [← Finset.mul_sum]
  rw [sum_residueCutoffQ_transformIntegrals]

/-! ## Removing the shifted endpoints -/

private theorem norm_transformKernel_le_inverse (N : ℕ) (x : ℝ) :
    ‖transformKernel N x‖ ≤ (1 / 8 : ℝ) * |x|⁻¹ := by
  by_cases hx : x = 0
  · simp [transformKernel, hx]
  · rw [transformKernel, if_neg hx, Real.norm_eq_abs, abs_div,
      abs_of_nonneg (bernoulliMark_nonneg _)]
    calc
      bernoulliMark ((N : ℝ) * x) / |x| ≤ (1 / 8 : ℝ) / |x| :=
        div_le_div_of_nonneg_right (bernoulliMark_le_one_eighth _) (abs_nonneg x)
      _ = (1 / 8 : ℝ) * |x|⁻¹ := by rw [div_eq_mul_inv]

private theorem transformKernel_tendsto_atTop_zero (N : ℕ) :
    Tendsto (transformKernel N) atTop (nhds 0) := by
  apply squeeze_zero_norm'
  · exact Eventually.of_forall (norm_transformKernel_le_inverse N)
  · have hi : Tendsto (fun x : ℝ => |x|⁻¹) atTop (nhds 0) :=
      (tendsto_inv_atTop_zero :
        Tendsto (fun x : ℝ => x⁻¹) atTop (nhds 0)).comp tendsto_abs_atTop_atTop
    have hc : Tendsto (fun _x : ℝ => (1 / 8 : ℝ)) atTop (nhds (1 / 8 : ℝ)) :=
      tendsto_const_nhds
    simpa using! hc.mul hi

private theorem transformKernel_tendsto_atBot_zero (N : ℕ) :
    Tendsto (transformKernel N) atBot (nhds 0) := by
  apply squeeze_zero_norm'
  · exact Eventually.of_forall (norm_transformKernel_le_inverse N)
  · have hi : Tendsto (fun x : ℝ => |x|⁻¹) atBot (nhds 0) :=
      (tendsto_inv_atTop_zero :
        Tendsto (fun x : ℝ => x⁻¹) atTop (nhds 0)).comp tendsto_abs_atBot_atTop
    have hc : Tendsto (fun _x : ℝ => (1 / 8 : ℝ)) atBot (nhds (1 / 8 : ℝ)) :=
      tendsto_const_nhds
    simpa using! hc.mul hi

private theorem periodizedTransformIntegrand_measurable (N n p : ℕ) :
    Measurable (periodizedTransformIntegrand N n p) := by
  exact (transformKernel_measurable_local N).complex_ofReal.mul
    (continuous_paperExp_local.comp
      (continuous_const.mul continuous_id)).measurable

private theorem norm_periodizedTransformIntegrand_le (N n p : ℕ) (x : ℝ) :
    ‖periodizedTransformIntegrand N n p x‖ ≤ (N : ℝ) / 2 := by
  rw [periodizedTransformIntegrand, norm_mul, Complex.norm_real,
    norm_paperExp_local, mul_one]
  exact norm_transformKernel_le_half_N N x

private theorem periodizedTransformIntegrand_tendsto_atTop_zero (N n p : ℕ) :
    Tendsto (periodizedTransformIntegrand N n p) atTop (nhds 0) := by
  have hk : Tendsto (fun x : ℝ => (transformKernel N x : ℂ)) atTop (nhds 0) :=
    (Complex.continuous_ofReal.tendsto 0).comp (transformKernel_tendsto_atTop_zero N)
  have hb : IsBoundedUnder (· ≤ ·) atTop
      ((‖·‖) ∘ fun x : ℝ => paperExp (-((n : ℝ) / (p : ℝ)) * x)) := by
    apply isBoundedUnder_of_eventually_le (a := 1)
    filter_upwards with x
    simp only [Function.comp_apply, norm_paperExp_local, le_refl]
  simpa only [periodizedTransformIntegrand] using! hk.zero_mul_isBoundedUnder_le hb

private theorem periodizedTransformIntegrand_tendsto_atBot_zero (N n p : ℕ) :
    Tendsto (periodizedTransformIntegrand N n p) atBot (nhds 0) := by
  have hk : Tendsto (fun x : ℝ => (transformKernel N x : ℂ)) atBot (nhds 0) :=
    (Complex.continuous_ofReal.tendsto 0).comp (transformKernel_tendsto_atBot_zero N)
  have hb : IsBoundedUnder (· ≤ ·) atBot
      ((‖·‖) ∘ fun x : ℝ => paperExp (-((n : ℝ) / (p : ℝ)) * x)) := by
    apply isBoundedUnder_of_eventually_le (a := 1)
    filter_upwards with x
    simp only [Function.comp_apply, norm_paperExp_local, le_refl]
  simpa only [periodizedTransformIntegrand] using! hk.zero_mul_isBoundedUnder_le hb

private theorem tendsto_left_endpoint_integral_zero
    (N n p a : ℕ) (hp : 0 < p) :
    Tendsto
      (fun R : ℕ =>
        ∫ x in -(a : ℝ) - (p : ℝ) * R..-(p : ℝ) * R,
          periodizedTransformIntegrand N n p x)
      atTop (nhds 0) := by
  let F : ℕ → ℝ → ℂ := fun R y =>
    periodizedTransformIntegrand N n p
      (y + (-(p : ℝ) * R - (a : ℝ)))
  have hscale : Tendsto (fun R : ℕ => (p : ℝ) * R) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (Nat.cast_pos.mpr hp)
  have hshift (y : ℝ) :
      Tendsto (fun R : ℕ => y + (-(p : ℝ) * R - (a : ℝ))) atTop atBot := by
    have hneg : Tendsto (fun R : ℕ => -((p : ℝ) * R)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp hscale
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using!
      tendsto_atBot_add_const_left atTop (y - (a : ℝ)) hneg
  have hDCT : Tendsto (fun R : ℕ => ∫ y in (0 : ℝ)..a, F R y) atTop (nhds 0) := by
    have h := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (a := (0 : ℝ)) (b := (a : ℝ)) (f := fun _y => (0 : ℂ))
      (F := F) (l := atTop) (μ := volume)
      (fun _y => (N : ℝ) / 2)
      (by
        filter_upwards with R
        simpa only [F] using!
          ((periodizedTransformIntegrand_measurable N n p).comp
            (measurable_id.add measurable_const)).aestronglyMeasurable)
      (by
        filter_upwards with R
        filter_upwards with y
        intro _hy
        exact norm_periodizedTransformIntegrand_le N n p _)
      intervalIntegrable_const
      (by
        filter_upwards with y
        intro _hy
        exact (periodizedTransformIntegrand_tendsto_atBot_zero N n p).comp (hshift y))
    simpa only [intervalIntegral.integral_zero] using! h
  apply hDCT.congr'
  filter_upwards with R
  dsimp [F]
  simpa [add_assoc, add_left_comm, add_comm, sub_eq_add_neg] using!
    (intervalIntegral.integral_comp_add_right
      (a := (0 : ℝ)) (b := (a : ℝ))
      (periodizedTransformIntegrand N n p)
      (-(p : ℝ) * R - (a : ℝ))).symm

private theorem tendsto_right_endpoint_integral_zero
    (N n p a : ℕ) (hp : 0 < p) :
    Tendsto
      (fun R : ℕ =>
        ∫ x in (p : ℝ) * R..(p : ℝ) - (a : ℝ) + (p : ℝ) * R,
          periodizedTransformIntegrand N n p x)
      atTop (nhds 0) := by
  let F : ℕ → ℝ → ℂ := fun R y =>
    periodizedTransformIntegrand N n p (y + (p : ℝ) * R)
  have hscale : Tendsto (fun R : ℕ => (p : ℝ) * R) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (Nat.cast_pos.mpr hp)
  have hshift (y : ℝ) :
      Tendsto (fun R : ℕ => y + (p : ℝ) * R) atTop atTop :=
    tendsto_atTop_add_const_left atTop y hscale
  have hDCT : Tendsto
      (fun R : ℕ => ∫ y in (0 : ℝ)..(p : ℝ) - (a : ℝ), F R y)
      atTop (nhds 0) := by
    have h := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (a := (0 : ℝ)) (b := (p : ℝ) - (a : ℝ)) (f := fun _y => (0 : ℂ))
      (F := F) (l := atTop) (μ := volume)
      (fun _y => (N : ℝ) / 2)
      (by
        filter_upwards with (R : ℕ)
        simpa only [F] using!
          ((periodizedTransformIntegrand_measurable N n p).comp
            (measurable_id.add measurable_const)).aestronglyMeasurable)
      (by
        filter_upwards with R
        filter_upwards with y
        intro _hy
        exact norm_periodizedTransformIntegrand_le N n p _)
      intervalIntegrable_const
      (by
        filter_upwards with y
        intro _hy
        exact (periodizedTransformIntegrand_tendsto_atTop_zero N n p).comp (hshift y))
    simpa only [intervalIntegral.integral_zero] using! h
  apply hDCT.congr'
  filter_upwards with R
  dsimp [F]
  simpa [add_assoc, add_left_comm, add_comm] using!
    (intervalIntegral.integral_comp_add_right
      (a := (0 : ℝ)) (b := (p : ℝ) - (a : ℝ))
      (periodizedTransformIntegrand N n p) ((p : ℝ) * R)).symm

/-- Shifting each endpoint of the expanding symmetric interval by a fixed
amount does not alter the principal value.  The two error integrals are the
fixed-length windows handled above. -/
theorem tendsto_residue_transformIntegral_of_principalValue
    (N n p a : ℕ) (hp : 0 < p) (z : ℂ)
    (hpv : HasSymmetricPrincipalValue N ((n : ℝ) / (p : ℝ)) z) :
    Tendsto
      (fun R : ℕ =>
        ∫ x in -(a : ℝ) - (p : ℝ) * R..
            (p : ℝ) - (a : ℝ) + (p : ℝ) * R,
          periodizedTransformIntegrand N n p x)
      atTop (nhds z) := by
  have hscale : Tendsto (fun R : ℕ => (p : ℝ) * R) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (Nat.cast_pos.mpr hp)
  have hcenter : Tendsto
      (fun R : ℕ =>
        ∫ x in -(p : ℝ) * R..(p : ℝ) * R,
          periodizedTransformIntegrand N n p x)
      atTop (nhds z) := by
    unfold HasSymmetricPrincipalValue at hpv
    have h := hpv.comp hscale
    change Tendsto
      (fun R : ℕ => principalValueTruncation N ((n : ℝ) / (p : ℝ))
        ((p : ℝ) * R)) atTop (nhds z) at h
    simpa only [principalValueTruncation, periodizedTransformIntegrand, neg_mul] using! h
  have hleft := tendsto_left_endpoint_integral_zero N n p a hp
  have hright := tendsto_right_endpoint_integral_zero N n p a hp
  have hsum : Tendsto
      (fun R : ℕ =>
        (∫ x in -(a : ℝ) - (p : ℝ) * R..-(p : ℝ) * R,
            periodizedTransformIntegrand N n p x) +
          ((∫ x in -(p : ℝ) * R..(p : ℝ) * R,
              periodizedTransformIntegrand N n p x) +
            ∫ x in (p : ℝ) * R..(p : ℝ) - (a : ℝ) + (p : ℝ) * R,
              periodizedTransformIntegrand N n p x))
      atTop (nhds z) := by
    simpa using! hleft.add (hcenter.add hright)
  apply hsum.congr'
  filter_upwards with R
  have h₁ := intervalIntegral.integral_add_adjacent_intervals
    (periodizedTransformIntegrand_intervalIntegrable N n p
      (-(a : ℝ) - (p : ℝ) * R) (-(p : ℝ) * R))
    (periodizedTransformIntegrand_intervalIntegrable N n p
      (-(p : ℝ) * R) ((p : ℝ) * R))
  have h₂ := intervalIntegral.integral_add_adjacent_intervals
    (periodizedTransformIntegrand_intervalIntegrable N n p
      (-(a : ℝ) - (p : ℝ) * R) ((p : ℝ) * R))
    (periodizedTransformIntegrand_intervalIntegrable N n p
      ((p : ℝ) * R) ((p : ℝ) - (a : ℝ) + (p : ℝ) * R))
  calc
    (∫ x in -(a : ℝ) - (p : ℝ) * R..-(p : ℝ) * R,
        periodizedTransformIntegrand N n p x) +
        ((∫ x in -(p : ℝ) * R..(p : ℝ) * R,
            periodizedTransformIntegrand N n p x) +
          ∫ x in (p : ℝ) * R..(p : ℝ) - (a : ℝ) + (p : ℝ) * R,
            periodizedTransformIntegrand N n p x) =
      ((∫ x in -(a : ℝ) - (p : ℝ) * R..-(p : ℝ) * R,
          periodizedTransformIntegrand N n p x) +
        ∫ x in -(p : ℝ) * R..(p : ℝ) * R,
          periodizedTransformIntegrand N n p x) +
        ∫ x in (p : ℝ) * R..(p : ℝ) - (a : ℝ) + (p : ℝ) * R,
          periodizedTransformIntegrand N n p x := by abel
    _ = ∫ x in -(a : ℝ) - (p : ℝ) * R..
          (p : ℝ) - (a : ℝ) + (p : ℝ) * R,
          periodizedTransformIntegrand N n p x := by rw [h₁, h₂]

/-! ## Identification of the sampled half-weighted tail -/

/-- At the rational frequency `s = n/p`, the analytic half-weighted tail is
exactly the arithmetic `H_*` value used in the manuscript.  Both the strict
inequality and the equality (half-weight) case are transported explicitly. -/
theorem halfWeightedTail_div_eq_hStarRatio (N n p : ℕ) (hp : 0 < p) :
    halfWeightedTail N ((n : ℝ) / (p : ℝ)) = hStarRatio n (p * N) := by
  unfold halfWeightedTail hStarRatio
  apply tsum_congr
  intro k
  have hpR : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp
  have hcast : (k : ℝ) * (N : ℝ) * (p : ℝ) =
      ((k * (p * N) : ℕ) : ℝ) := by
    push_cast
    ring
  have hlt : ((n : ℝ) / (p : ℝ) < (k : ℝ) * (N : ℝ)) ↔
      n < k * (p * N) := by
    rw [div_lt_iff₀ hpR, hcast]
    exact_mod_cast Iff.rfl
  have heq : ((n : ℝ) / (p : ℝ) = (k : ℝ) * (N : ℝ)) ↔
      n = k * (p * N) := by
    rw [div_eq_iff (ne_of_gt hpR), hcast]
    exact_mod_cast Iff.rfl
  unfold halfWeightedTailTerm hStarRatioWeight
  rw [inverseSquare_eq]
  simp only [hlt, heq]
  split_ifs <;> ring

/-! ## One-residue coefficient limits -/

/-- For a positive frequency, the exact finite-cutoff coefficient in one
reduced residue class converges to the manuscript's half-weighted tail. -/
theorem tendsto_residuePeriodizationCoefficient_pos
    (N n p a : ℕ) (hN : 0 < N) (hn : 0 < n) (hp : 0 < p) :
    Tendsto
      (fun R : ℕ =>
        unitFourierCoefficient (residuePeriodizationTruncation N p a R) n)
      atTop
      (nhds
        (((1 / (p : ℝ) ^ 2 : ℝ) : ℂ) *
          paperExp (-(n : ℝ) * (a : ℝ) / (p : ℝ)) *
            ((-(Complex.I / (2 * Real.pi))) *
              (hStarRatio n (p * N) : ℂ)))) := by
  have hs : (0 : ℝ) < (n : ℝ) / (p : ℝ) :=
    div_pos (Nat.cast_pos.mpr hn) (Nat.cast_pos.mpr hp)
  have hpv : HasSymmetricPrincipalValue N ((n : ℝ) / (p : ℝ))
      ((-(Complex.I / (2 * Real.pi))) * (hStarRatio n (p * N) : ℂ)) := by
    simpa only [halfWeightedTail_div_eq_hStarRatio N n p hp] using!
      principalValueTransform_eq_halfWeightedTail N ((n : ℝ) / (p : ℝ)) hN hs
  have hint := tendsto_residue_transformIntegral_of_principalValue
    N n p a hp _ hpv
  have hc₁ : Tendsto
      (fun _R : ℕ => ((1 / (p : ℝ) ^ 2 : ℝ) : ℂ)) atTop
      (nhds ((1 / (p : ℝ) ^ 2 : ℝ) : ℂ)) := tendsto_const_nhds
  have hc₂ : Tendsto
      (fun _R : ℕ => paperExp (-(n : ℝ) * (a : ℝ) / (p : ℝ))) atTop
      (nhds (paperExp (-(n : ℝ) * (a : ℝ) / (p : ℝ)))) := tendsto_const_nhds
  have hmul := hc₁.mul (hc₂.mul hint)
  have hcoef := hmul.congr' (by
    filter_upwards with R
    simpa only [mul_assoc] using!
      (unitFourierCoefficient_residuePeriodizationTruncation N n p a R hp).symm)
  simpa only [mul_assoc] using! hcoef

/-- At frequency zero the coefficient limit is zero.  This uses the oddness
of the real-line kernel through `principalValueTransform_zero_frequency`,
not the positive-frequency tail formula. -/
theorem tendsto_residuePeriodizationCoefficient_zero
    (N p a : ℕ) (hp : 0 < p) :
    Tendsto
      (fun R : ℕ =>
        unitFourierCoefficient (residuePeriodizationTruncation N p a R) 0)
      atTop (nhds 0) := by
  have hpv : HasSymmetricPrincipalValue N (((0 : ℕ) : ℝ) / (p : ℝ)) 0 := by
    simpa using! principalValueTransform_zero_frequency N
  have hint := tendsto_residue_transformIntegral_of_principalValue
    N 0 p a hp 0 hpv
  have hc₁ : Tendsto
      (fun _R : ℕ => ((1 / (p : ℝ) ^ 2 : ℝ) : ℂ)) atTop
      (nhds ((1 / (p : ℝ) ^ 2 : ℝ) : ℂ)) := tendsto_const_nhds
  have hc₂ : Tendsto
      (fun _R : ℕ => paperExp (-(0 : ℝ) * (a : ℝ) / (p : ℝ))) atTop
      (nhds (paperExp (-(0 : ℝ) * (a : ℝ) / (p : ℝ)))) := tendsto_const_nhds
  have hmul := hc₁.mul (hc₂.mul hint)
  have hcoef := hmul.congr' (by
    filter_upwards with R
    simpa only [Nat.cast_zero, neg_zero, zero_mul, zero_div, mul_assoc] using!
      (unitFourierCoefficient_residuePeriodizationTruncation N 0 p a R hp).symm)
  simpa only [mul_zero] using! hcoef

/-! ## The finite `p`-sum and the Ramanujan phase sum -/

/-- Linearity is applied only to the finite `p`, residue, and cutoff sums.
Every summand is interval-integrable by the uniform local bound proved above. -/
theorem unitFourierCoefficient_pvPeriodizationTruncation
    (N P R n : ℕ) :
    unitFourierCoefficient (pvPeriodizationTruncation N P R) n =
      ∑ p ∈ Finset.Icc 1 P,
        ∑ a ∈ reducedResidues p,
          unitFourierCoefficient (residuePeriodizationTruncation N p a R) n := by
  unfold unitFourierCoefficient pvPeriodizationTruncation
  simp_rw [Finset.sum_mul]
  rw [intervalIntegral.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro p hpMem
    exact intervalIntegral.integral_finset_sum fun a haMem =>
      residuePeriodizationFourier_intervalIntegrable N n p a R
  · intro p hpMem
    exact intervalIntegrable_finsetSum (reducedResidues p)
      (fun a α => residuePeriodizationTruncation N p a R α *
        paperExp (-(n : ℝ) * α)) 0 1
      (fun a haMem => residuePeriodizationFourier_intervalIntegrable N n p a R)

private theorem paperExp_eq_fourierChar (t : ℝ) :
    paperExp t = (Real.fourierChar t : ℂ) := by
  rw [Real.fourierChar_apply]
  unfold paperExp
  congr 1
  push_cast
  ring

private theorem paperExp_residuePhase_neg (n p a : ℕ) :
    paperExp (-(n : ℝ) * (a : ℝ) / (p : ℝ)) =
      ramanujanPhase p a (-(n : ℤ)) := by
  rw [paperExp_eq_fourierChar]
  unfold ramanujanPhase
  congr 2
  push_cast
  ring

/-- The residue phases in the finite Fourier calculation are exactly a
Ramanujan sum.  The sign is removed by the independently proved evenness of
Ramanujan sums, rather than by silently identifying a phase with its
conjugate. -/
theorem sum_reducedResidues_paperExp_neg (n p : ℕ) :
    (∑ a ∈ reducedResidues p,
      paperExp (-(n : ℝ) * (a : ℝ) / (p : ℝ))) =
      ramanujanSum p (n : ℤ) := by
  simp_rw [paperExp_residuePhase_neg]
  exact ramanujanSum_even p (n : ℤ)

/-- The exact positive-frequency coefficient displayed in Lemma 2.1, before
factoring out the common Fourier-transform constant. -/
def pvPeriodizationPositiveCoefficient (N P n : ℕ) : ℂ :=
  ∑ p ∈ Finset.Icc 1 P,
    ((1 / (p : ℝ) ^ 2 : ℝ) : ℂ) * ramanujanSum p (n : ℤ) *
      ((-(Complex.I / (2 * Real.pi))) * (hStarRatio n (p * N) : ℂ))

private theorem residueCoefficientLimit_sum_eq
    (N n p : ℕ) :
    (∑ a ∈ reducedResidues p,
      ((1 / (p : ℝ) ^ 2 : ℝ) : ℂ) *
        paperExp (-(n : ℝ) * (a : ℝ) / (p : ℝ)) *
          ((-(Complex.I / (2 * Real.pi))) *
            (hStarRatio n (p * N) : ℂ))) =
      ((1 / (p : ℝ) ^ 2 : ℝ) : ℂ) * ramanujanSum p (n : ℤ) *
        ((-(Complex.I / (2 * Real.pi))) *
          (hStarRatio n (p * N) : ℂ)) := by
  rw [← Finset.sum_mul, ← Finset.mul_sum, sum_reducedResidues_paperExp_neg]

/-- Main legality statement for the nonzero Fourier coefficients: the
coefficient of every finite symmetric `q`-cutoff is computed first, and
those coefficients converge to the exact Ramanujan formula.  Thus no
principal-value series is interchanged directly with the unit-interval
integral. -/
theorem tendsto_pvPeriodizationCoefficient_pos
    (N P n : ℕ) (hN : 0 < N) (hn : 0 < n) :
    Tendsto
      (fun R : ℕ => unitFourierCoefficient (pvPeriodizationTruncation N P R) n)
      atTop (nhds (pvPeriodizationPositiveCoefficient N P n)) := by
  have hsum : Tendsto
      (fun R : ℕ =>
        ∑ p ∈ Finset.Icc 1 P,
          ∑ a ∈ reducedResidues p,
            unitFourierCoefficient (residuePeriodizationTruncation N p a R) n)
      atTop
      (nhds
        (∑ p ∈ Finset.Icc 1 P,
          ∑ a ∈ reducedResidues p,
            ((1 / (p : ℝ) ^ 2 : ℝ) : ℂ) *
              paperExp (-(n : ℝ) * (a : ℝ) / (p : ℝ)) *
                ((-(Complex.I / (2 * Real.pi))) *
                  (hStarRatio n (p * N) : ℂ)))) := by
    apply tendsto_finset_sum
    intro p hpMem
    apply tendsto_finset_sum
    intro a haMem
    exact tendsto_residuePeriodizationCoefficient_pos N n p a hN hn
      (by exact (Finset.mem_Icc.mp hpMem).1)
  have hcoef := hsum.congr' (by
    filter_upwards with R
    exact (unitFourierCoefficient_pvPeriodizationTruncation N P R n).symm)
  simpa only [pvPeriodizationPositiveCoefficient, residueCoefficientLimit_sum_eq]
    using! hcoef

/-- The zero-frequency coefficient is treated separately and converges to
zero. -/
theorem tendsto_pvPeriodizationCoefficient_zero (N P : ℕ) :
    Tendsto
      (fun R : ℕ => unitFourierCoefficient (pvPeriodizationTruncation N P R) 0)
      atTop (nhds 0) := by
  have hsum : Tendsto
      (fun R : ℕ =>
        ∑ p ∈ Finset.Icc 1 P,
          ∑ a ∈ reducedResidues p,
            unitFourierCoefficient (residuePeriodizationTruncation N p a R) 0)
      atTop
      (nhds (∑ p ∈ Finset.Icc 1 P, ∑ a ∈ reducedResidues p, (0 : ℂ))) := by
    apply tendsto_finset_sum
    intro p hpMem
    apply tendsto_finset_sum
    intro a haMem
    exact tendsto_residuePeriodizationCoefficient_zero N p a
      (by exact (Finset.mem_Icc.mp hpMem).1)
  have hcoef := hsum.congr' (by
    filter_upwards with R
    exact (unitFourierCoefficient_pvPeriodizationTruncation N P R 0).symm)
  simpa using! hcoef

/-- Factoring the common transform constant gives exactly the manuscript's
displayed coefficient
`-i/(2π) ∑_{p≤P} c_p(n) p⁻² H_*(n/(pN))`. -/
theorem pvPeriodizationPositiveCoefficient_eq_paperFormula
    (N P n : ℕ) :
    pvPeriodizationPositiveCoefficient N P n =
      (-(Complex.I / (2 * Real.pi))) *
        ∑ p ∈ Finset.Icc 1 P,
          ramanujanSum p (n : ℤ) *
            (((hStarRatio n (p * N) / (p : ℝ) ^ 2 : ℝ) : ℂ)) := by
  unfold pvPeriodizationPositiveCoefficient
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hpMem
  push_cast
  ring

/-- Positive-frequency coefficient convergence in the paper's final
factored notation. -/
theorem tendsto_pvPeriodizationCoefficient_pos_paperFormula
    (N P n : ℕ) (hN : 0 < N) (hn : 0 < n) :
    Tendsto
      (fun R : ℕ => unitFourierCoefficient (pvPeriodizationTruncation N P R) n)
      atTop
      (nhds
        ((-(Complex.I / (2 * Real.pi))) *
          ∑ p ∈ Finset.Icc 1 P,
            ramanujanSum p (n : ℤ) *
              (((hStarRatio n (p * N) / (p : ℝ) ^ 2 : ℝ) : ℂ)))) := by
  rw [← pvPeriodizationPositiveCoefficient_eq_paperFormula N P n]
  exact tendsto_pvPeriodizationCoefficient_pos N P n hN hn

/-! ## Negative frequencies -/

private theorem conj_paperExp (t : ℝ) :
    conj (paperExp t) = paperExp (-t) := by
  unfold paperExp
  rw [← Complex.exp_conj]
  apply congrArg Complex.exp
  push_cast
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  ring

private theorem conj_periodizationCell (N p : ℕ) (q : ℤ) (α : ℝ) :
    conj (periodizationCell N p q α) = periodizationCell N p q α := by
  simp [periodizationCell]

/-- Every finite cutoff is real-valued. -/
theorem conj_pvPeriodizationTruncation (N P R : ℕ) (α : ℝ) :
    conj (pvPeriodizationTruncation N P R α) =
      pvPeriodizationTruncation N P R α := by
  simp only [pvPeriodizationTruncation, residuePeriodizationTruncation,
    map_sum, conj_periodizationCell]

/-- Fourier coefficients of a real-valued function at opposite frequencies
are complex conjugates. -/
theorem unitFourierCoefficientInt_neg_of_real
    (f : ℝ → ℂ) (n : ℤ) (hreal : ∀ α, conj (f α) = f α) :
    unitFourierCoefficientInt f (-n) = conj (unitFourierCoefficientInt f n) := by
  unfold unitFourierCoefficientInt
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), ← integral_conj]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with α
  rw [map_mul, hreal, conj_paperExp]
  congr 2
  push_cast
  ring

/-- The natural- and integer-frequency coefficient conventions agree at a
nonnegative integer. -/
theorem unitFourierCoefficientInt_natCast (f : ℝ → ℂ) (n : ℕ) :
    unitFourierCoefficientInt f (n : ℤ) = unitFourierCoefficient f n := by
  unfold unitFourierCoefficientInt unitFourierCoefficient
  norm_num

/-- This formalizes the final conjugacy sentence of Lemma 2.1 for every
finite cutoff. -/
theorem unitFourierCoefficientInt_pvPeriodization_neg
    (N P R n : ℕ) :
    unitFourierCoefficientInt (pvPeriodizationTruncation N P R) (-(n : ℤ)) =
      conj (unitFourierCoefficient (pvPeriodizationTruncation N P R) n) := by
  rw [unitFourierCoefficientInt_neg_of_real _ (n : ℤ)
    (conj_pvPeriodizationTruncation N P R)]
  rw [unitFourierCoefficientInt_natCast]

/-- Consequently, negative finite-cutoff coefficients converge to the
complex conjugate of the positive-frequency Ramanujan formula. -/
theorem tendsto_pvPeriodizationCoefficient_neg
    (N P n : ℕ) (hN : 0 < N) (hn : 0 < n) :
    Tendsto
      (fun R : ℕ =>
        unitFourierCoefficientInt (pvPeriodizationTruncation N P R) (-(n : ℤ)))
      atTop (nhds (conj (pvPeriodizationPositiveCoefficient N P n))) := by
  have hpos := tendsto_pvPeriodizationCoefficient_pos N P n hN hn
  have hconj := (Complex.continuous_conj.tendsto
    (pvPeriodizationPositiveCoefficient N P n)).comp hpos
  apply hconj.congr'
  filter_upwards with R
  exact (unitFourierCoefficientInt_pvPeriodization_neg N P R n).symm

end

end Erdos1002
