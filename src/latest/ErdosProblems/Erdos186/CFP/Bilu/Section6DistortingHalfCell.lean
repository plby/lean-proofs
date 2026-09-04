/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section8Synthesis
import ErdosProblems.Erdos186.CFP.Bilu.Section7FreimanMap
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Bilu Lemma 6.1: a distorting frequency biases a half residue class

The offset in Freiman's map is not zero.  Lemma 6.1 chooses it from the
large exponential sum: one translated half of the circle contains more
than `(1 + delta) / 2` of the source points.  This is the first ingredient
which absorbs the apparent `2^r` residue-cell loss in Section 7.
-/

namespace Erdos186.CFP.Bilu.Section6DistortingHalfCell

open scoped BigOperators RealInnerProductSpace
open Set MeasureTheory
open DistortingMeasure Section8Synthesis Section7FreimanMap SubspaceLattice

noncomputable section

set_option autoImplicit false

/-! ## Fractional half intervals -/

/-- Indices whose translated phase lies in the lower half of the unit
circle. -/
def lowerHalfIndices {ι : Type*} [Fintype ι] [DecidableEq ι]
    (y : ι → ℝ) (b : ℝ) : Finset ι :=
  Finset.univ.filter fun i ↦ Int.fract (y i - b) < 1 / 2

@[simp] theorem mem_lowerHalfIndices {ι : Type*} [Fintype ι]
    [DecidableEq ι] (y : ι → ℝ) (b : ℝ) (i : ι) :
    i ∈ lowerHalfIndices y b ↔ Int.fract (y i - b) < 1 / 2 := by
  simp [lowerHalfIndices]

theorem fract_add_intCast (x : ℝ) (z : ℤ) :
    Int.fract (x + z) = Int.fract x := by
  simp only [Int.fract, Int.floor_add_intCast]
  push_cast
  ring

/-- Translation by one half exchanges the two half-open residue classes.
The half-open convention makes this statement exact even on the boundary.
-/
theorem fract_sub_half_lt_half_iff (x : ℝ) :
    Int.fract (x - 1 / 2) < 1 / 2 ↔
      ¬ Int.fract x < 1 / 2 := by
  let u := Int.fract x
  have hu0 : 0 ≤ u := Int.fract_nonneg x
  have hu1 : u < 1 := Int.fract_lt_one x
  have hx : x - 1 / 2 = (⌊x⌋ : ℝ) + (u - 1 / 2) := by
    dsimp only [u]
    calc
      x - 1 / 2 = ((⌊x⌋ : ℝ) + Int.fract x) - 1 / 2 := by
        rw [Int.floor_add_fract]
      _ = (⌊x⌋ : ℝ) + (Int.fract x - 1 / 2) := by ring
  rw [hx, add_comm, fract_add_intCast]
  by_cases hu : u < 1 / 2
  · have hfloor : ⌊u - 1 / 2⌋ = (-1 : ℤ) := by
      rw [Int.floor_eq_iff]
      constructor <;> norm_num <;> linarith
    simp only [Int.fract, hfloor]
    push_cast
    constructor
    · intro h
      exfalso
      linarith
    · intro h
      exact (h hu).elim
  · have hfloor : ⌊u - 1 / 2⌋ = (0 : ℤ) := by
      rw [Int.floor_eq_iff]
      constructor <;> norm_num <;> linarith
    simp only [Int.fract, hfloor]
    push_cast
    constructor
    · intro _
      exact hu
    · intro _
      linarith

theorem lowerHalfIndices_add_half {ι : Type*} [Fintype ι]
    [DecidableEq ι] (y : ι → ℝ) (b : ℝ) :
    lowerHalfIndices y (b + 1 / 2) =
      Finset.univ \ lowerHalfIndices y b := by
  ext i
  simp only [mem_lowerHalfIndices, Finset.mem_sdiff, Finset.mem_univ, true_and]
  convert fract_sub_half_lt_half_iff (y i - b) using 1 <;> ring_nf

theorem card_lowerHalfIndices_add_half {ι : Type*} [Fintype ι]
    [DecidableEq ι] (y : ι → ℝ) (b : ℝ) :
    (lowerHalfIndices y (b + 1 / 2)).card =
      Fintype.card ι - (lowerHalfIndices y b).card := by
  rw [lowerHalfIndices_add_half,
    Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ _),
    Finset.card_univ]

/-- On the first half-period, the modular lower half is the ordinary
half-open interval `[b,b+1/2)`. -/
theorem fract_sub_lt_half_iff_of_mem_firstHalf
    (y b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 2) :
    Int.fract (y - b) < 1 / 2 ↔
      b ≤ Int.fract y ∧ Int.fract y < b + 1 / 2 := by
  let u := Int.fract y
  have hu0 : 0 ≤ u := Int.fract_nonneg y
  have hu1 : u < 1 := Int.fract_lt_one y
  have hy : y - b = (⌊y⌋ : ℝ) + (u - b) := by
    dsimp only [u]
    calc
      y - b = ((⌊y⌋ : ℝ) + Int.fract y) - b := by
        rw [Int.floor_add_fract]
      _ = (⌊y⌋ : ℝ) + (Int.fract y - b) := by ring
  rw [hy, add_comm, fract_add_intCast]
  by_cases hlo : b ≤ u
  · by_cases hhi : u < b + 1 / 2
    · have hfract : Int.fract (u - b) = u - b :=
        Int.fract_eq_self.mpr ⟨sub_nonneg.mpr hlo, by linarith⟩
      rw [hfract]
      exact ⟨fun _ ↦ ⟨hlo, hhi⟩, fun _ ↦ by linarith⟩
    · have hfract : Int.fract (u - b) = u - b :=
        Int.fract_eq_self.mpr ⟨sub_nonneg.mpr hlo, by linarith⟩
      rw [hfract]
      constructor
      · intro h
        exfalso
        linarith
      · intro h
        exact (hhi h.2).elim
  · have hub : u < b := lt_of_not_ge hlo
    have hfloor : ⌊u - b⌋ = (-1 : ℤ) := by
      rw [Int.floor_eq_iff]
      constructor <;> norm_num <;> linarith
    simp only [Int.fract, hfloor]
    push_cast
    constructor
    · intro h
      exfalso
      linarith
    · intro h
      exact (not_le_of_gt hub h.1).elim

/-! ## The integral estimate in Lemma 6.1 -/

/-- Distribution function of the fractional phases. -/
def phaseDistribution {ι : Type*} [Fintype ι]
    (y : ι → ℝ) (x : ℝ) : ℝ :=
  ∑ i, if Int.fract (y i) < x then 1 else 0

theorem phaseDistribution_eq_card {ι : Type*} [Fintype ι]
    [DecidableEq ι] (y : ι → ℝ) (x : ℝ) :
    phaseDistribution y x =
      ((Finset.univ.filter fun i ↦ Int.fract (y i) < x).card : ℝ) := by
  classical
  simpa only [phaseDistribution] using
    (Finset.sum_boole (fun i : ι ↦ Int.fract (y i) < x)
      Finset.univ :
        (∑ i ∈ Finset.univ,
          if Int.fract (y i) < x then (1 : ℝ) else 0) = _)

/-- Difference of the distribution function over a half interval is the
cardinality of the corresponding modular residue class. -/
theorem phaseDistribution_add_half_sub {ι : Type*} [Fintype ι]
    [DecidableEq ι] (y : ι → ℝ) (b : ℝ)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 2) :
    phaseDistribution y (b + 1 / 2) - phaseDistribution y b =
      (lowerHalfIndices y b).card := by
  classical
  let lower : Finset ι :=
    Finset.univ.filter fun i ↦ Int.fract (y i) < b
  let upper : Finset ι :=
    Finset.univ.filter fun i ↦ Int.fract (y i) < b + 1 / 2
  have hsub : lower ⊆ upper := by
    intro i hi
    simp only [lower, upper, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    linarith
  have hdiff : upper \ lower = lowerHalfIndices y b := by
    ext i
    simp only [upper, lower, Finset.mem_sdiff, Finset.mem_filter,
      Finset.mem_univ, true_and, mem_lowerHalfIndices]
    rw [fract_sub_lt_half_iff_of_mem_firstHalf (y i) b hb0 hb1]
    constructor
    · rintro ⟨hupper, hlower⟩
      exact ⟨le_of_not_gt hlower, hupper⟩
    · rintro ⟨hlower, hupper⟩
      exact ⟨hupper, not_lt_of_ge hlower⟩
  rw [phaseDistribution_eq_card, phaseDistribution_eq_card]
  change (upper.card : ℝ) - (lower.card : ℝ) = _
  rw [← Nat.cast_sub (Finset.card_le_card hsub)]
  have hcard : (upper \ lower).card = upper.card - lower.card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub]
  rw [← hcard, hdiff]

theorem intervalIntegral_sin_two_pi (a b : ℝ) :
    (∫ x in a..b, Real.sin (2 * Real.pi * x)) =
      (Real.cos (2 * Real.pi * a) -
        Real.cos (2 * Real.pi * b)) / (2 * Real.pi) := by
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hchange := intervalIntegral.integral_comp_mul_deriv
    (a := a) (b := b)
    (f := fun x : ℝ ↦ 2 * Real.pi * x)
    (f' := fun _ : ℝ ↦ 2 * Real.pi)
    (g := Real.sin)
    (by
      intro x hx
      exact hasDerivAt_const_mul (2 * Real.pi))
    continuous_const.continuousOn Real.continuous_sin
  have hchange' :
      (∫ x in a..b, Real.sin (2 * Real.pi * x)) *
          (2 * Real.pi) =
        ∫ x in 2 * Real.pi * a..2 * Real.pi * b, Real.sin x := by
    rw [intervalIntegral.integral_mul_const] at hchange
    simpa only [Function.comp_apply] using hchange
  rw [integral_sin] at hchange'
  exact (eq_div_iff hpi).2 hchange'

/-- Integral of the one-sided step attached to one fractional phase. -/
theorem intervalIntegral_phaseStep_sin
    (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (∫ x in (0 : ℝ)..1,
      (if u < x then 1 else 0) * Real.sin (2 * Real.pi * x)) =
      (Real.cos (2 * Real.pi * u) - 1) / (2 * Real.pi) := by
  let f : ℝ → ℝ := fun x ↦ Real.sin (2 * Real.pi * x)
  have hf : IntervalIntegrable f volume 0 1 :=
    (Real.continuous_sin.comp
      (continuous_const.mul continuous_id)).intervalIntegrable 0 1
  have hleft :
      (∫ x in (0 : ℝ)..1, {x | x ≤ u}.indicator f x) =
        ∫ x in (0 : ℝ)..u, f x :=
    intervalIntegral.integral_indicator ⟨hu0, hu1⟩
  have hpoint : (fun x : ℝ ↦
      (if u < x then 1 else 0) * f x) =
      fun x ↦ f x - {x | x ≤ u}.indicator f x := by
    funext x
    by_cases hx : x ≤ u
    · simp [f, hx, not_lt_of_ge hx]
    · simp [f, hx, lt_of_not_ge hx]
  have hindicator : IntervalIntegrable
      ({x | x ≤ u}.indicator f) volume 0 1 := by
    constructor
    · exact hf.1.indicator (measurableSet_le measurable_id measurable_const)
    · exact hf.2.indicator (measurableSet_le measurable_id measurable_const)
  rw [hpoint, intervalIntegral.integral_sub hf
    hindicator, hleft]
  rw [intervalIntegral_sin_two_pi, intervalIntegral_sin_two_pi]
  norm_num [Real.cos_two_pi]
  field_simp
  ring

/-- Finite integration-by-parts identity used in Bilu's proof. -/
theorem cosSum_eq_distributionIntegral {ι : Type*} [Fintype ι]
    (y : ι → ℝ) :
    (∑ i, Real.cos (2 * Real.pi * Int.fract (y i))) =
      Fintype.card ι + 2 * Real.pi *
        (∫ x in (0 : ℝ)..1,
          phaseDistribution y x * Real.sin (2 * Real.pi * x)) := by
  classical
  have hstep (i : ι) : IntervalIntegrable
      (fun x : ℝ ↦
        (if Int.fract (y i) < x then 1 else 0) *
          Real.sin (2 * Real.pi * x)) volume 0 1 := by
    have hf : IntervalIntegrable
        (fun x : ℝ ↦ Real.sin (2 * Real.pi * x)) volume 0 1 :=
      (Real.continuous_sin.comp
        (continuous_const.mul continuous_id)).intervalIntegrable 0 1
    have hindicator : IntervalIntegrable
        ({x : ℝ | Int.fract (y i) < x}.indicator
          fun x ↦ Real.sin (2 * Real.pi * x)) volume 0 1 := by
      constructor
      · exact hf.1.indicator (measurableSet_lt measurable_const measurable_id)
      · exact hf.2.indicator (measurableSet_lt measurable_const measurable_id)
    have heq : (fun x : ℝ ↦
        (if Int.fract (y i) < x then 1 else 0) *
          Real.sin (2 * Real.pi * x)) =
        {x : ℝ | Int.fract (y i) < x}.indicator
          (fun x ↦ Real.sin (2 * Real.pi * x)) := by
      funext x
      by_cases hx : Int.fract (y i) < x <;>
        simp [Set.indicator, hx]
    rw [heq]
    exact hindicator
  have hsum := intervalIntegral.integral_finset_sum
    (s := Finset.univ)
    (f := fun i x ↦
      (if Int.fract (y i) < x then 1 else 0) *
        Real.sin (2 * Real.pi * x))
    (fun i hi ↦ hstep i)
  have hfun : (fun x : ℝ ↦
      phaseDistribution y x * Real.sin (2 * Real.pi * x)) =
      fun x ↦ ∑ i,
        (if Int.fract (y i) < x then 1 else 0) *
          Real.sin (2 * Real.pi * x) := by
    funext x
    simp only [phaseDistribution, Finset.sum_mul]
  rw [hfun, hsum]
  simp_rw [intervalIntegral_phaseStep_sin _
    (Int.fract_nonneg _) (Int.fract_lt_one _).le]
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  rw [Finset.mul_sum]
  simp_rw [mul_div_cancel₀ _ hpi]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- The distribution integrand is interval-integrable on every compact
interval. -/
theorem phaseDistribution_mul_sin_intervalIntegrable
    {ι : Type*} [Fintype ι] (y : ι → ℝ) (a b : ℝ) :
    IntervalIntegrable
      (fun x ↦ phaseDistribution y x * Real.sin (2 * Real.pi * x))
      volume a b := by
  classical
  have hstep (i : ι) : IntervalIntegrable
      (fun x : ℝ ↦
        (if Int.fract (y i) < x then 1 else 0) *
          Real.sin (2 * Real.pi * x)) volume a b := by
    have hf : IntervalIntegrable
        (fun x : ℝ ↦ Real.sin (2 * Real.pi * x)) volume a b :=
      (Real.continuous_sin.comp
        (continuous_const.mul continuous_id)).intervalIntegrable a b
    have hindicator : IntervalIntegrable
        ({x : ℝ | Int.fract (y i) < x}.indicator
          fun x ↦ Real.sin (2 * Real.pi * x)) volume a b := by
      constructor
      · exact hf.1.indicator (measurableSet_lt measurable_const measurable_id)
      · exact hf.2.indicator (measurableSet_lt measurable_const measurable_id)
    have heq : (fun x : ℝ ↦
        (if Int.fract (y i) < x then 1 else 0) *
          Real.sin (2 * Real.pi * x)) =
        {x : ℝ | Int.fract (y i) < x}.indicator
          (fun x ↦ Real.sin (2 * Real.pi * x)) := by
      funext x
      by_cases hx : Int.fract (y i) < x <;>
        simp [Set.indicator, hx]
    rw [heq]
    exact hindicator
  have hsum : IntervalIntegrable
      (fun x : ℝ ↦ ∑ i,
        (if Int.fract (y i) < x then 1 else 0) *
          Real.sin (2 * Real.pi * x)) volume a b :=
    by
      let g : ι → ℝ → ℝ := fun i x ↦
        (if Int.fract (y i) < x then 1 else 0) *
          Real.sin (2 * Real.pi * x)
      have hg := IntervalIntegrable.sum Finset.univ
        (f := g) fun i hi ↦ hstep i
      have heq : (∑ i, g i) = fun x ↦ ∑ i, g i x := by
        funext x
        exact Fintype.sum_apply x g
      rw [← heq]
      exact hg
  have hfun : (fun x : ℝ ↦
      phaseDistribution y x * Real.sin (2 * Real.pi * x)) =
      fun x ↦ ∑ i,
        (if Int.fract (y i) < x then 1 else 0) *
          Real.sin (2 * Real.pi * x) := by
    funext x
    simp only [phaseDistribution, Finset.sum_mul]
  rw [hfun]
  exact hsum

/-- The distribution integral over a full period is the negative weighted
integral of the half-cell cardinality on the first half-period. -/
theorem distributionIntegral_eq_neg_lowerHalfIntegral
    {ι : Type*} [Fintype ι] [DecidableEq ι] (y : ι → ℝ) :
    (∫ x in (0 : ℝ)..1,
      phaseDistribution y x * Real.sin (2 * Real.pi * x)) =
      -(∫ x in (0 : ℝ)..(1 / 2),
        ((lowerHalfIndices y x).card : ℝ) *
          Real.sin (2 * Real.pi * x)) := by
  let f : ℝ → ℝ := fun x ↦
    phaseDistribution y x * Real.sin (2 * Real.pi * x)
  have hf0 : IntervalIntegrable f volume 0 (1 / 2) :=
    phaseDistribution_mul_sin_intervalIntegrable y 0 (1 / 2)
  have hf1 : IntervalIntegrable f volume (1 / 2) 1 :=
    phaseDistribution_mul_sin_intervalIntegrable y (1 / 2) 1
  have hfshift : IntervalIntegrable (fun x ↦ f (x + 1 / 2))
      volume 0 (1 / 2) := by
    have hstep (i : ι) : IntervalIntegrable
        (fun x : ℝ ↦
          (if Int.fract (y i) < x + 1 / 2 then 1 else 0) *
            Real.sin (2 * Real.pi * (x + 1 / 2))) volume 0 (1 / 2) := by
      have hg : IntervalIntegrable
          (fun x : ℝ ↦ Real.sin (2 * Real.pi * (x + 1 / 2)))
          volume 0 (1 / 2) :=
        (Real.continuous_sin.comp
          (continuous_const.mul
            (continuous_id.add continuous_const))).intervalIntegrable 0 (1 / 2)
      have hindicator : IntervalIntegrable
          ({x : ℝ | Int.fract (y i) < x + 1 / 2}.indicator
            fun x ↦ Real.sin (2 * Real.pi * (x + 1 / 2)))
          volume 0 (1 / 2) := by
        constructor
        · exact hg.1.indicator
            (measurableSet_lt measurable_const
              (measurable_id.add measurable_const))
        · exact hg.2.indicator
            (measurableSet_lt measurable_const
              (measurable_id.add measurable_const))
      have heq : (fun x : ℝ ↦
          (if Int.fract (y i) < x + 1 / 2 then 1 else 0) *
            Real.sin (2 * Real.pi * (x + 1 / 2))) =
          {x : ℝ | Int.fract (y i) < x + 1 / 2}.indicator
            (fun x ↦ Real.sin (2 * Real.pi * (x + 1 / 2))) := by
        funext x
        by_cases hx : Int.fract (y i) < x + 1 / 2 <;>
          simp [Set.indicator, hx]
      rw [heq]
      exact hindicator
    have hsum : IntervalIntegrable
        (fun x : ℝ ↦ ∑ i,
          (if Int.fract (y i) < x + 1 / 2 then 1 else 0) *
            Real.sin (2 * Real.pi * (x + 1 / 2))) volume 0 (1 / 2) :=
      by
        let g : ι → ℝ → ℝ := fun i x ↦
          (if Int.fract (y i) < x + 1 / 2 then 1 else 0) *
            Real.sin (2 * Real.pi * (x + 1 / 2))
        have hg := IntervalIntegrable.sum Finset.univ
          (f := g) fun i hi ↦ hstep i
        have heq : (∑ i, g i) = fun x ↦ ∑ i, g i x := by
          funext x
          exact Fintype.sum_apply x g
        rw [← heq]
        exact hg
    have heq : (fun x ↦ f (x + 1 / 2)) = fun x : ℝ ↦ ∑ i,
        (if Int.fract (y i) < x + 1 / 2 then 1 else 0) *
          Real.sin (2 * Real.pi * (x + 1 / 2)) := by
      funext x
      simp only [f, phaseDistribution, Finset.sum_mul]
    rw [heq]
    exact hsum
  have hshift :
      (∫ x in (0 : ℝ)..(1 / 2), f (x + 1 / 2)) =
        ∫ x in (1 / 2)..1, f x := by
    simpa only [zero_add, add_halves] using
      (intervalIntegral.integral_comp_add_right f (1 / 2)
        (a := 0) (b := 1 / 2))
  have hpoint : Set.EqOn
      (fun x ↦ f x + f (x + 1 / 2))
      (fun x ↦ -(((lowerHalfIndices y x).card : ℝ) *
        Real.sin (2 * Real.pi * x))) (Set.uIcc 0 (1 / 2)) := by
    intro x hx
    have hx' : x ∈ Set.Icc (0 : ℝ) (1 / 2) := by simpa using hx
    have hsin : Real.sin (2 * Real.pi * (x + 1 / 2)) =
        -Real.sin (2 * Real.pi * x) := by
      convert Real.sin_add_pi (2 * Real.pi * x) using 1 <;> ring_nf
    have hcount := phaseDistribution_add_half_sub y x hx'.1 hx'.2
    dsimp only [f]
    rw [hsin]
    rw [← hcount]
    ring
  calc
    (∫ x in (0 : ℝ)..1, f x) =
        (∫ x in (0 : ℝ)..(1 / 2), f x) +
          ∫ x in (1 / 2)..1, f x :=
      (intervalIntegral.integral_add_adjacent_intervals hf0 hf1).symm
    _ = (∫ x in (0 : ℝ)..(1 / 2), f x) +
          ∫ x in (0 : ℝ)..(1 / 2), f (x + 1 / 2) := by rw [hshift]
    _ = ∫ x in (0 : ℝ)..(1 / 2),
          (f x + f (x + 1 / 2)) :=
      (intervalIntegral.integral_add hf0 hfshift).symm
    _ = ∫ x in (0 : ℝ)..(1 / 2),
          -(((lowerHalfIndices y x).card : ℝ) *
            Real.sin (2 * Real.pi * x)) :=
      intervalIntegral.integral_congr hpoint
    _ = -(∫ x in (0 : ℝ)..(1 / 2),
          ((lowerHalfIndices y x).card : ℝ) *
            Real.sin (2 * Real.pi * x)) :=
      intervalIntegral.integral_neg

/-- The half-cell cardinality times the sine weight is integrable on the
first half-period. -/
theorem lowerHalfCard_mul_sin_intervalIntegrable
    {ι : Type*} [Fintype ι] [DecidableEq ι] (y : ι → ℝ) :
    IntervalIntegrable
      (fun x ↦ ((lowerHalfIndices y x).card : ℝ) *
        Real.sin (2 * Real.pi * x)) volume 0 (1 / 2) := by
  classical
  have hstep (i : ι) : IntervalIntegrable
      (fun x : ℝ ↦
        (if Int.fract (y i - x) < 1 / 2 then 1 else 0) *
          Real.sin (2 * Real.pi * x)) volume 0 (1 / 2) := by
    let S : Set ℝ :=
      {x | x ≤ Int.fract (y i)} ∩
        {x | Int.fract (y i) < x + 1 / 2}
    have hS : MeasurableSet S :=
      (measurableSet_le measurable_id measurable_const).inter
        (measurableSet_lt measurable_const
          (measurable_id.add measurable_const))
    have hsin : IntervalIntegrable
        (fun x : ℝ ↦ Real.sin (2 * Real.pi * x)) volume 0 (1 / 2) :=
      (Real.continuous_sin.comp
        (continuous_const.mul continuous_id)).intervalIntegrable 0 (1 / 2)
    have hindicator : IntervalIntegrable
        (S.indicator fun x ↦ Real.sin (2 * Real.pi * x))
        volume 0 (1 / 2) := by
      constructor
      · exact hsin.1.indicator hS
      · exact hsin.2.indicator hS
    apply hindicator.congr
    intro x hx
    have hx' : x ∈ Set.Icc (0 : ℝ) (1 / 2) := by
      rw [Set.uIoc_of_le (by norm_num)] at hx
      exact ⟨hx.1.le, hx.2⟩
    change S.indicator (fun x ↦ Real.sin (2 * Real.pi * x)) x =
      (if Int.fract (y i - x) < 1 / 2 then 1 else 0) *
        Real.sin (2 * Real.pi * x)
    simp only [fract_sub_lt_half_iff_of_mem_firstHalf (y i) x hx'.1 hx'.2]
    simp only [S, Set.indicator, Set.mem_inter_iff, Set.mem_setOf_eq]
    by_cases hmem : x ≤ Int.fract (y i) ∧
        Int.fract (y i) < x + 1 / 2 <;> simp [hmem]
  have hsum : IntervalIntegrable
      (fun x : ℝ ↦ ∑ i,
        (if Int.fract (y i - x) < 1 / 2 then 1 else 0) *
          Real.sin (2 * Real.pi * x)) volume 0 (1 / 2) := by
    let g : ι → ℝ → ℝ := fun i x ↦
      (if Int.fract (y i - x) < 1 / 2 then 1 else 0) *
        Real.sin (2 * Real.pi * x)
    have hg := IntervalIntegrable.sum Finset.univ
      (f := g) fun i hi ↦ hstep i
    have heq : (∑ i, g i) = fun x ↦ ∑ i, g i x := by
      funext x
      exact Fintype.sum_apply x g
    rw [← heq]
    exact hg
  apply hsum.congr
  intro x hx
  change (∑ i,
      (if Int.fract (y i - x) < 1 / 2 then 1 else 0) *
        Real.sin (2 * Real.pi * x)) =
    ((lowerHalfIndices y x).card : ℝ) * Real.sin (2 * Real.pi * x)
  rw [← Finset.sum_mul]
  congr 1
  change (∑ i, if Int.fract (y i - x) < 1 / 2 then 1 else 0) =
    ((lowerHalfIndices y x).card : ℝ)
  simpa only [lowerHalfIndices] using
    (Finset.sum_boole
      (fun i : ι ↦ Int.fract (y i - x) < 1 / 2) Finset.univ :
      (∑ i ∈ Finset.univ,
        if Int.fract (y i - x) < 1 / 2 then (1 : ℝ) else 0) = _)

/-- If every translated half contains at most `(1+delta)/2` of the
indices, then the weighted half-count integral has the complementary
lower bound. -/
theorem lowerHalfIntegral_ge_of_card_upper
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (y : ι → ℝ) (delta : ℝ)
    (hupper : ∀ b : ℝ,
      ((lowerHalfIndices y b).card : ℝ) ≤
        (1 + delta) / 2 * Fintype.card ι) :
    ((1 - delta) / 2 * Fintype.card ι) / Real.pi ≤
      ∫ x in (0 : ℝ)..(1 / 2),
        ((lowerHalfIndices y x).card : ℝ) *
          Real.sin (2 * Real.pi * x) := by
  let lower : ℝ := (1 - delta) / 2 * Fintype.card ι
  have hlower (x : ℝ) : lower ≤ ((lowerHalfIndices y x).card : ℝ) := by
    have hshift := hupper (x + 1 / 2)
    have hcard := card_lowerHalfIndices_add_half y x
    have hle : (lowerHalfIndices y x).card ≤ Fintype.card ι := by
      exact Finset.card_le_univ _
    have hsumNat :
        (lowerHalfIndices y (x + 1 / 2)).card +
          (lowerHalfIndices y x).card = Fintype.card ι := by omega
    have hsumReal :
        ((lowerHalfIndices y (x + 1 / 2)).card : ℝ) +
          (lowerHalfIndices y x).card = Fintype.card ι := by
      exact_mod_cast hsumNat
    dsimp only [lower]
    linarith
  have hsinInt : IntervalIntegrable
      (fun x : ℝ ↦ Real.sin (2 * Real.pi * x)) volume 0 (1 / 2) :=
    (Real.continuous_sin.comp
      (continuous_const.mul continuous_id)).intervalIntegrable 0 (1 / 2)
  have hlowerInt : IntervalIntegrable
      (fun x ↦ lower * Real.sin (2 * Real.pi * x))
      volume 0 (1 / 2) := hsinInt.const_mul lower
  have hcardInt := lowerHalfCard_mul_sin_intervalIntegrable y
  have hmono :
      (∫ x in (0 : ℝ)..(1 / 2),
        lower * Real.sin (2 * Real.pi * x)) ≤
      ∫ x in (0 : ℝ)..(1 / 2),
        ((lowerHalfIndices y x).card : ℝ) *
          Real.sin (2 * Real.pi * x) := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      hlowerInt hcardInt
    intro x hx
    apply mul_le_mul_of_nonneg_right (hlower x)
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · exact mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hx.1
    · have hx1 : x ≤ (1 : ℝ) / 2 := hx.2
      nlinarith [Real.pi_pos]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral_sin_two_pi] at hmono
  have hangle : 2 * Real.pi * (1 / 2 : ℝ) = Real.pi := by ring
  rw [hangle, Real.cos_pi] at hmono
  norm_num at hmono
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hquot : (2 : ℝ) / (2 * Real.pi) = 1 / Real.pi := by
    field_simp
  rw [hquot] at hmono
  dsimp only [lower] at hmono
  simpa [div_eq_mul_inv] using hmono

/-- Real-oriented form of Bilu's Lemma 6.1. -/
theorem exists_lowerHalf_of_cosSum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (y : ι → ℝ) (delta : ℝ)
    (hdistort : delta * Fintype.card ι <
      ∑ i, Real.cos (2 * Real.pi * Int.fract (y i))) :
    ∃ b : ℝ,
      (1 + delta) / 2 * Fintype.card ι <
        (lowerHalfIndices y b).card := by
  by_contra hnone
  push_neg at hnone
  have hintegral := lowerHalfIntegral_ge_of_card_upper y delta hnone
  have hdistIntegral := distributionIntegral_eq_neg_lowerHalfIntegral y
  have hcos := cosSum_eq_distributionIntegral y
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  rw [hdistIntegral] at hcos
  have hbound :
      (∑ i, Real.cos (2 * Real.pi * Int.fract (y i))) ≤
        delta * Fintype.card ι := by
    rw [hcos]
    calc
      (Fintype.card ι : ℝ) + 2 * Real.pi *
          (-(∫ x in (0 : ℝ)..(1 / 2),
            ((lowerHalfIndices y x).card : ℝ) *
              Real.sin (2 * Real.pi * x))) ≤
          (Fintype.card ι : ℝ) + 2 * Real.pi *
            (-(((1 - delta) / 2 * Fintype.card ι) / Real.pi)) := by
        gcongr
      _ = delta * Fintype.card ι := by
        field_simp
        ring
  exact (not_lt_of_ge hbound) hdistort

/-! ## Rotation of the complex exponential sum -/

/-- Taking fractional parts does not change a cosine with period one. -/
theorem cos_two_pi_fract (x : ℝ) :
    Real.cos (2 * Real.pi * Int.fract x) =
      Real.cos (2 * Real.pi * x) := by
  calc
    Real.cos (2 * Real.pi * Int.fract x) =
        Real.cos (2 * Real.pi * Int.fract x + (⌊x⌋ : ℝ) *
          (2 * Real.pi)) :=
      (Real.cos_add_int_mul_two_pi
        (2 * Real.pi * Int.fract x) ⌊x⌋).symm
    _ = Real.cos (2 * Real.pi * x) := by
      congr 1
      calc
        2 * Real.pi * Int.fract x + (⌊x⌋ : ℝ) * (2 * Real.pi) =
            2 * Real.pi * ((⌊x⌋ : ℝ) + Int.fract x) := by ring
        _ = 2 * Real.pi * x := by rw [Int.floor_add_fract]

/-- The exponential sum associated to a finite family of real phases. -/
def phaseExponentialSum {ι : Type*} [Fintype ι]
    (y : ι → ℝ) : ℂ :=
  ∑ i, Complex.exp ((2 * Real.pi * y i : ℝ) * Complex.I)

theorem phaseExponentialSum_re {ι : Type*} [Fintype ι]
    (y : ι → ℝ) :
    (phaseExponentialSum y).re = ∑ i, Real.cos (2 * Real.pi * y i) := by
  simp [phaseExponentialSum, Complex.exp_re]

theorem phaseExponentialSum_im {ι : Type*} [Fintype ι]
    (y : ι → ℝ) :
    (phaseExponentialSum y).im = ∑ i, Real.sin (2 * Real.pi * y i) := by
  simp [phaseExponentialSum, Complex.exp_im]

/-- Rotate the phases by the argument of their exponential sum.  The
resulting cosine sum is its norm. -/
theorem cosineSum_rotated_eq_norm {ι : Type*} [Fintype ι]
    (y : ι → ℝ) :
    (∑ i, Real.cos (2 * Real.pi * Int.fract
      (y i - (phaseExponentialSum y).arg / (2 * Real.pi)))) =
        ‖phaseExponentialSum y‖ := by
  simp_rw [cos_two_pi_fract]
  have hangle (i : ι) :
      2 * Real.pi * (y i - (phaseExponentialSum y).arg / (2 * Real.pi)) =
        2 * Real.pi * y i - (phaseExponentialSum y).arg := by
    field_simp
  simp_rw [hangle, Real.cos_sub]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
  rw [← phaseExponentialSum_re, ← phaseExponentialSum_im]
  rw [← Complex.norm_mul_cos_arg (phaseExponentialSum y),
    ← Complex.norm_mul_sin_arg (phaseExponentialSum y)]
  ring_nf
  rw [← mul_add, Real.cos_sq_add_sin_sq]
  ring

/-- Complex form of Lemma 6.1.  Rotating by the argument loses no
constant. -/
theorem exists_lowerHalf_of_exponentialSum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (y : ι → ℝ) (delta : ℝ) (hdelta : 0 ≤ delta)
    (hdistort : delta * Fintype.card ι < ‖phaseExponentialSum y‖) :
    ∃ b : ℝ, (1 + delta) / 2 * Fintype.card ι <
      (lowerHalfIndices y b).card := by
  have hz : phaseExponentialSum y ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hdistort
    exact (not_lt_of_ge (mul_nonneg hdelta (Nat.cast_nonneg _))) hdistort
  let theta : ℝ := (phaseExponentialSum y).arg / (2 * Real.pi)
  let y' : ι → ℝ := fun i ↦ y i - theta
  have hsum : (∑ i, Real.cos (2 * Real.pi * Int.fract (y' i))) =
      ‖phaseExponentialSum y‖ := by
    simpa only [y', theta] using cosineSum_rotated_eq_norm y
  obtain ⟨b, hb⟩ := exists_lowerHalf_of_cosSum y' delta (by rwa [hsum])
  refine ⟨b + theta, ?_⟩
  have hsets : lowerHalfIndices y' b = lowerHalfIndices y (b + theta) := by
    ext i
    simp only [mem_lowerHalfIndices, y']
    congr 2
    ring_nf
  rwa [← hsets]

/-! ## Distorting frequencies -/

/-- A torus character evaluated on a real representative is the
exponential of the Euclidean pairing. -/
theorem character_realToTorus_eq_phase_exp {m : ℕ}
    (a : EuclideanSpace ℝ (Fin m)) (x : Mahler.IntegralPoint m) :
    character x (realToTorus (WithLp.ofLp a)) =
      Complex.exp ((2 * Real.pi * ⟪integralReal x, a⟫ : ℝ) * Complex.I) := by
  rw [character]
  simp_rw [realToTorus, fourier_coe_apply]
  rw [← Complex.exp_sum]
  congr 1
  simp only [PiLp.inner_apply, integralReal_apply,
    RCLike.inner_apply, conj_trivial]
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The abstract phase exponential sum is exactly Bilu's trigonometric
polynomial on the real torus representative. -/
theorem phaseExponentialSum_subtype_eq_trigPolynomial {m : ℕ}
    (K : Finset (Mahler.IntegralPoint m))
    (a : EuclideanSpace ℝ (Fin m)) :
    phaseExponentialSum (fun x : ↑K ↦ ⟪integralReal x.1, a⟫) =
      trigPolynomial K (realToTorus (WithLp.ofLp a)) := by
  rw [phaseExponentialSum]
  calc
    (∑ x : ↑K, Complex.exp
        ((2 * Real.pi * ⟪integralReal x.1, a⟫ : ℝ) * Complex.I)) =
        ∑ x : ↑K, character x.1 (realToTorus (WithLp.ofLp a)) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact (character_realToTorus_eq_phase_exp a x).symm
    _ = trigPolynomial K (realToTorus (WithLp.ofLp a)) := by
      rw [trigPolynomial]
      exact (Finset.sum_subtype K (fun _ ↦ Iff.rfl)
        (fun x ↦ character x (realToTorus (WithLp.ofLp a)))).symm

/-- **Bilu, Lemma 6.1.** Every distorting frequency has a translated
lower half-cell containing more than `(1+delta)/2` of the source set. -/
theorem exists_biased_halfCell_of_mem_cubeDistortingSet {m : ℕ}
    (K : Finset (Mahler.IntegralPoint m)) (delta : ℝ)
    (hdelta : 0 ≤ delta) (a : EuclideanSpace ℝ (Fin m))
    (ha : WithLp.ofLp a ∈ cubeDistortingSet delta K) :
    ∃ b : ℝ,
      (1 + delta) / 2 * K.card <
        (K.filter fun x ↦
          0 ≤ Int.fract (⟪integralReal x, a⟫ - b) ∧
          Int.fract (⟪integralReal x, a⟫ - b) < 1 / 2).card := by
  have hdistort : delta * K.card <
      ‖trigPolynomial K (realToTorus (WithLp.ofLp a))‖ := ha.2
  let y : ↑K → ℝ := fun x ↦ ⟪integralReal x.1, a⟫
  have hdistort' : delta * Fintype.card ↑K < ‖phaseExponentialSum y‖ := by
    rw [phaseExponentialSum_subtype_eq_trigPolynomial]
    simpa using hdistort
  obtain ⟨b, hb⟩ :=
    exists_lowerHalf_of_exponentialSum y delta hdelta hdistort'
  refine ⟨b, ?_⟩
  let p : Mahler.IntegralPoint m → Prop := fun x ↦
    0 ≤ Int.fract (⟪integralReal x, a⟫ - b) ∧
      Int.fract (⟪integralReal x, a⟫ - b) < 1 / 2
  have hcard :
      (K.attach.filter fun x : ↑K ↦ p x.1).card =
        (K.filter p).card := by
    have h := congrArg Finset.card (Finset.filter_attach p K)
    simpa only [Finset.card_map, Finset.card_attach] using h
  rw [← hcard]
  simpa only [lowerHalfIndices, y, p, Fintype.card_coe,
    Finset.univ_eq_attach, Int.fract_nonneg, true_and] using hb

/-- Simultaneously choose the offsets in Lemma 6.1 for a finite family
of distorting frequencies. -/
theorem exists_offsets_biased_halfCells_of_mem_cubeDistortingSet
    {m r : ℕ} (K : Finset (Mahler.IntegralPoint m)) (delta : ℝ)
    (hdelta : 0 ≤ delta)
    (a : Fin r → EuclideanSpace ℝ (Fin m))
    (ha : ∀ i, WithLp.ofLp (a i) ∈ cubeDistortingSet delta K) :
    ∃ b : Fin r → ℝ, ∀ i,
      ((K.filter fun x ↦
        0 ≤ Int.fract (phase a b x i) ∧
          Int.fract (phase a b x i) < 1 / 2).card : ℝ) >
        (1 + delta) / 2 * K.card := by
  choose b hb using fun i ↦
    exists_biased_halfCell_of_mem_cubeDistortingSet
      K delta hdelta (a i) (ha i)
  refine ⟨b, ?_⟩
  intro i
  change (1 + delta) / 2 * (K.card : ℝ) <
    ((K.filter fun x ↦
      0 ≤ Int.fract (phase a b x i) ∧
        Int.fract (phase a b x i) < 1 / 2).card : ℝ)
  convert hb i using 1 <;> rfl

end

end Erdos186.CFP.Bilu.Section6DistortingHalfCell

#print axioms
  Erdos186.CFP.Bilu.Section6DistortingHalfCell.fract_sub_half_lt_half_iff
#print axioms
  Erdos186.CFP.Bilu.Section6DistortingHalfCell.cosSum_eq_distributionIntegral
