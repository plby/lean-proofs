import Wikipedia.SzemeredisTheorem.Finite.CauchySchwarz

/-!
# Finite analytic lemmas for densification

This file isolates the elementary projected-majorant estimates used in one
step of Conlon--Fox--Zhao densification.  It does not state a relative
counting theorem.

If a nonnegative finite majorant `ν` has first and second normalized moments
within `η` of one, then

```
mean (fun x => |ν x - 1|) ≤ √(3 * η).
```

For `0 ≤ g ≤ ν`, truncating `g` pointwise at one produces a `[0,1]`-valued
function.  Its `L¹` loss, and its loss in any pairing against a unit-bounded
factor, are bounded first by the mean excess `max (ν - 1) 0`, and hence by
the same square-root moment bound.  The final section records pointwise and
averaged product-perturbation inequalities used to package the remaining
bounded factors in a densification step.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Projected-majorant moments -/

/-- The finite moment hypotheses used after projecting all majorant factors
other than the edge currently being densified.

The common error parameter is recorded as nonnegative so downstream
square-root statements do not have to recover this fact from an absolute
value inequality. -/
structure HasProjectedMajorantMoments
    {Ω : Type*} [Fintype Ω]
    (ν : Ω → ℝ) (η : ℝ) : Prop where
  error_nonneg : 0 ≤ η
  nonneg : ∀ x, 0 ≤ ν x
  firstMoment_close : |mean ν - 1| ≤ η
  secondMoment_close :
    |mean (fun x => ν x ^ 2) - 1| ≤ η

/-- Exact expansion of a centered second moment.  Nonemptiness is the
precise hypothesis needed for the normalized mean of the constant function
one to equal one. -/
theorem mean_sub_one_sq_eq
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f : Ω → ℝ) :
    mean (fun x => (f x - 1) ^ 2) =
      mean (fun x => f x ^ 2) - 2 * mean f + 1 := by
  calc
    mean (fun x => (f x - 1) ^ 2) =
        mean (fun x =>
          f x ^ 2 + ((-2 : ℝ) * f x + 1)) := by
      apply congrArg mean
      funext x
      ring
    _ = mean (fun x => f x ^ 2) +
        mean (fun x => (-2 : ℝ) * f x + 1) :=
      mean_add _ _
    _ = mean (fun x => f x ^ 2) +
        (mean (fun x => (-2 : ℝ) * f x) +
          mean (fun _ : Ω => (1 : ℝ))) := by
      rw [mean_add]
    _ = mean (fun x => f x ^ 2) - 2 * mean f + 1 := by
      rw [mean_smul, mean_const]
      ring

namespace HasProjectedMajorantMoments

/-- First and second moment errors at most `η` give centered second moment at
most `3 * η`. -/
theorem centeredSecondMoment_le
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {ν : Ω → ℝ} {η : ℝ}
    (h : HasProjectedMajorantMoments ν η) :
    mean (fun x => (ν x - 1) ^ 2) ≤ 3 * η := by
  have hfirstLower : 1 - η ≤ mean ν := by
    have hneg := (abs_le.mp h.firstMoment_close).1
    linarith
  have hsecondUpper :
      mean (fun x => ν x ^ 2) ≤ 1 + η := by
    have hpos := (abs_le.mp h.secondMoment_close).2
    linarith
  rw [mean_sub_one_sq_eq]
  linarith

/-- Cauchy--Schwarz converts the centered second-moment estimate into a
squared `L¹` estimate. -/
theorem centeredAbsMean_sq_le
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {ν : Ω → ℝ} {η : ℝ}
    (h : HasProjectedMajorantMoments ν η) :
    (mean (fun x => |ν x - 1|)) ^ 2 ≤ 3 * η := by
  calc
    (mean (fun x => |ν x - 1|)) ^ 2 ≤
        mean (fun x => |ν x - 1| ^ 2) :=
      mean_square_le_mean_square _
    _ = mean (fun x => (ν x - 1) ^ 2) := by
      apply congrArg mean
      funext x
      exact sq_abs _
    _ ≤ 3 * η :=
      h.centeredSecondMoment_le

/-- Explicit square-root form of the projected-majorant `L¹` bound. -/
theorem centeredAbsMean_le_sqrt
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {ν : Ω → ℝ} {η : ℝ}
    (h : HasProjectedMajorantMoments ν η) :
    mean (fun x => |ν x - 1|) ≤ Real.sqrt (3 * η) := by
  apply
    (Real.le_sqrt
      (mean_nonneg fun x => abs_nonneg (ν x - 1))
      (mul_nonneg (by norm_num) h.error_nonneg)).2
  exact h.centeredAbsMean_sq_le

end HasProjectedMajorantMoments

/-! ## Truncation at one -/

/-- Pointwise truncation used to turn a nonnegative function into a dense
`[0,1]` model. -/
def truncateAtOne {Ω : Type*} (g : Ω → ℝ) : Ω → ℝ :=
  fun x => min (g x) 1

/-- Pointwise mass above one. -/
def excessAboveOne {Ω : Type*} (f : Ω → ℝ) : Ω → ℝ :=
  fun x => max (f x - 1) 0

@[simp]
theorem truncateAtOne_apply
    {Ω : Type*} (g : Ω → ℝ) (x : Ω) :
    truncateAtOne g x = min (g x) 1 :=
  rfl

@[simp]
theorem excessAboveOne_apply
    {Ω : Type*} (f : Ω → ℝ) (x : Ω) :
    excessAboveOne f x = max (f x - 1) 0 :=
  rfl

theorem truncateAtOne_nonneg
    {Ω : Type*} {g : Ω → ℝ}
    (hg : ∀ x, 0 ≤ g x) (x : Ω) :
    0 ≤ truncateAtOne g x :=
  le_min (hg x) zero_le_one

theorem truncateAtOne_le_one
    {Ω : Type*} (g : Ω → ℝ) (x : Ω) :
    truncateAtOne g x ≤ 1 :=
  min_le_right _ _

theorem truncateAtOne_le
    {Ω : Type*} (g : Ω → ℝ) (x : Ω) :
    truncateAtOne g x ≤ g x :=
  min_le_left _ _

/-- A nonnegative function becomes `[0,1]`-valued after truncation. -/
theorem truncateAtOne_mem_unitInterval
    {Ω : Type*} {g : Ω → ℝ}
    (hg : ∀ x, 0 ≤ g x) (x : Ω) :
    0 ≤ truncateAtOne g x ∧ truncateAtOne g x ≤ 1 :=
  ⟨truncateAtOne_nonneg hg x, truncateAtOne_le_one g x⟩

theorem excessAboveOne_nonneg
    {Ω : Type*} (f : Ω → ℝ) (x : Ω) :
    0 ≤ excessAboveOne f x :=
  le_max_right _ _

/-- Excess above one is monotone in the underlying function. -/
theorem excessAboveOne_mono
    {Ω : Type*} {f g : Ω → ℝ}
    (hfg : ∀ x, f x ≤ g x) (x : Ω) :
    excessAboveOne f x ≤ excessAboveOne g x := by
  exact max_le_max (sub_le_sub_right (hfg x) 1) le_rfl

/-- Excess above one is bounded by centered absolute value. -/
theorem excessAboveOne_le_abs_sub_one
    {Ω : Type*} (f : Ω → ℝ) (x : Ω) :
    excessAboveOne f x ≤ |f x - 1| := by
  exact max_le (le_abs_self _) (abs_nonneg _)

/-- Truncation removes exactly the positive excess above one. -/
theorem sub_truncateAtOne_eq_excessAboveOne
    {Ω : Type*} (g : Ω → ℝ) (x : Ω) :
    g x - truncateAtOne g x = excessAboveOne g x := by
  by_cases hx : g x ≤ 1
  · simp [truncateAtOne, excessAboveOne, min_eq_left hx,
      max_eq_right (sub_nonpos.mpr hx)]
  · have hx' : 1 ≤ g x := le_of_not_ge hx
    simp [truncateAtOne, excessAboveOne, min_eq_right hx',
      max_eq_left (sub_nonneg.mpr hx')]

/-- Absolute truncation loss is the same positive excess. -/
theorem abs_sub_truncateAtOne_eq_excessAboveOne
    {Ω : Type*} (g : Ω → ℝ) (x : Ω) :
    |g x - truncateAtOne g x| = excessAboveOne g x := by
  rw [abs_of_nonneg
    (sub_nonneg.mpr (truncateAtOne_le g x))]
  exact sub_truncateAtOne_eq_excessAboveOne g x

/-- If `g ≤ ν`, pointwise truncation loss is charged to the excess of the
majorant `ν` above one. -/
theorem abs_sub_truncateAtOne_le_excessAboveOne
    {Ω : Type*} {g ν : Ω → ℝ}
    (hgν : ∀ x, g x ≤ ν x) (x : Ω) :
    |g x - truncateAtOne g x| ≤ excessAboveOne ν x := by
  rw [abs_sub_truncateAtOne_eq_excessAboveOne]
  exact excessAboveOne_mono hgν x

/-- `L¹` truncation loss is at most the mean excess of the majorant. -/
theorem mean_abs_sub_truncateAtOne_le_mean_excessAboveOne
    {Ω : Type*} [Fintype Ω]
    {g ν : Ω → ℝ}
    (hgν : ∀ x, g x ≤ ν x) :
    mean (fun x => |g x - truncateAtOne g x|) ≤
      mean (excessAboveOne ν) :=
  mean_mono fun x =>
    abs_sub_truncateAtOne_le_excessAboveOne hgν x

/-- The majorant's mean excess is bounded by its centered `L¹` norm. -/
theorem mean_excessAboveOne_le_mean_abs_sub_one
    {Ω : Type*} [Fintype Ω]
    (ν : Ω → ℝ) :
    mean (excessAboveOne ν) ≤
      mean (fun x => |ν x - 1|) :=
  mean_mono fun x => excessAboveOne_le_abs_sub_one ν x

namespace HasProjectedMajorantMoments

/-- Moment control gives an explicit bound for mean excess above one. -/
theorem mean_excessAboveOne_le_sqrt
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {ν : Ω → ℝ} {η : ℝ}
    (h : HasProjectedMajorantMoments ν η) :
    mean (excessAboveOne ν) ≤ Real.sqrt (3 * η) :=
  (mean_excessAboveOne_le_mean_abs_sub_one ν).trans
    h.centeredAbsMean_le_sqrt

/-- A function dominated by a projected majorant loses at most
`√(3 * η)` in `L¹` when truncated at one. -/
theorem mean_abs_sub_truncateAtOne_le_sqrt
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {ν g : Ω → ℝ} {η : ℝ}
    (h : HasProjectedMajorantMoments ν η)
    (hgν : ∀ x, g x ≤ ν x) :
    mean (fun x => |g x - truncateAtOne g x|) ≤
      Real.sqrt (3 * η) :=
  (mean_abs_sub_truncateAtOne_le_mean_excessAboveOne hgν).trans
    h.mean_excessAboveOne_le_sqrt

/-- Packaged dense truncation: for `0 ≤ g ≤ ν`, `min g 1` lies in
`[0,1]` and has explicit `L¹` error. -/
theorem truncateAtOne_spec
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {ν g : Ω → ℝ} {η : ℝ}
    (h : HasProjectedMajorantMoments ν η)
    (hg0 : ∀ x, 0 ≤ g x)
    (hgν : ∀ x, g x ≤ ν x) :
    (∀ x, 0 ≤ truncateAtOne g x ∧ truncateAtOne g x ≤ 1) ∧
      mean (fun x => |g x - truncateAtOne g x|) ≤
        Real.sqrt (3 * η) :=
  ⟨truncateAtOne_mem_unitInterval hg0,
    h.mean_abs_sub_truncateAtOne_le_sqrt hgν⟩

end HasProjectedMajorantMoments

/-! ## Pairing and product perturbations -/

/-- Replacing one factor in a normalized pairing costs at most its `L¹`
distance when the other factor is bounded in absolute value by one. -/
theorem abs_mean_mul_sub_mul_le_mean_abs
    {Ω : Type*} [Fintype Ω]
    (f g u : Ω → ℝ)
    (hu : ∀ x, |u x| ≤ 1) :
    |mean (fun x => f x * u x) -
        mean (fun x => g x * u x)| ≤
      mean (fun x => |f x - g x|) := by
  rw [← mean_sub]
  calc
    |mean (fun x => f x * u x - g x * u x)| ≤
        mean (fun x => |f x * u x - g x * u x|) := by
      exact Finset.abs_expect_le Finset.univ _
    _ ≤ mean (fun x => |f x - g x|) := by
      apply mean_mono
      intro x
      rw [← sub_mul, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg (f x - g x)) (hu x)

/-- Pairing loss from truncation is bounded by the mean excess of the
majorant. -/
theorem abs_mean_mul_sub_truncateAtOne_mul_le_mean_excessAboveOne
    {Ω : Type*} [Fintype Ω]
    {g ν u : Ω → ℝ}
    (hgν : ∀ x, g x ≤ ν x)
    (hu : ∀ x, |u x| ≤ 1) :
    |mean (fun x => g x * u x) -
        mean (fun x => truncateAtOne g x * u x)| ≤
      mean (excessAboveOne ν) := by
  calc
    |mean (fun x => g x * u x) -
        mean (fun x => truncateAtOne g x * u x)| ≤
        mean (fun x => |g x - truncateAtOne g x|) :=
      abs_mean_mul_sub_mul_le_mean_abs
        g (truncateAtOne g) u hu
    _ ≤ mean (excessAboveOne ν) :=
      mean_abs_sub_truncateAtOne_le_mean_excessAboveOne hgν

namespace HasProjectedMajorantMoments

/-- Projected-majorant moments bound the loss of one densified pairing by
`√(3 * η)`. -/
theorem abs_mean_mul_sub_truncateAtOne_mul_le_sqrt
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {ν g u : Ω → ℝ} {η : ℝ}
    (h : HasProjectedMajorantMoments ν η)
    (hgν : ∀ x, g x ≤ ν x)
    (hu : ∀ x, |u x| ≤ 1) :
    |mean (fun x => g x * u x) -
        mean (fun x => truncateAtOne g x * u x)| ≤
      Real.sqrt (3 * η) :=
  (abs_mean_mul_sub_truncateAtOne_mul_le_mean_excessAboveOne
    hgν hu).trans h.mean_excessAboveOne_le_sqrt

end HasProjectedMajorantMoments

/-- Pointwise perturbation of a finite product of unit-bounded factors.
Unlike a uniform-error estimate, this retains the individual pointwise
errors in a sum. -/
theorem abs_prod_sub_prod_le_sum_abs
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f g : ι → ℝ)
    (hf : ∀ i ∈ s, |f i| ≤ 1)
    (hg : ∀ i ∈ s, |g i| ≤ 1) :
    |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| ≤
      ∑ i ∈ s, |f i - g i| := by
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      have hfa : |f a| ≤ 1 :=
        hf a (Finset.mem_insert_self a s)
      have hga : |g a| ≤ 1 :=
        hg a (Finset.mem_insert_self a s)
      have hfs : |∏ i ∈ s, f i| ≤ 1 := by
        rw [Finset.abs_prod]
        exact Finset.prod_le_one
          (fun i _ => abs_nonneg (f i))
          (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      have ih' :
          |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| ≤
            ∑ i ∈ s, |f i - g i| :=
        ih
          (fun i hi => hf i (Finset.mem_insert_of_mem hi))
          (fun i hi => hg i (Finset.mem_insert_of_mem hi))
      rw [Finset.prod_insert ha, Finset.prod_insert ha,
        Finset.sum_insert ha]
      calc
        |f a * (∏ i ∈ s, f i) -
            g a * ∏ i ∈ s, g i| =
            |(f a - g a) * (∏ i ∈ s, f i) +
              g a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i)| := by
          congr 1
          ring
        _ ≤
            |f a - g a| * |∏ i ∈ s, f i| +
              |g a| *
                |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| := by
          simpa [abs_mul] using
            abs_add_le
              ((f a - g a) * (∏ i ∈ s, f i))
              (g a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i))
        _ ≤
            |f a - g a| +
              ∑ i ∈ s, |f i - g i| := by
          exact add_le_add
            (by
              simpa using
                mul_le_of_le_one_right
                  (abs_nonneg (f a - g a)) hfs)
            (by
              calc
                |g a| *
                    |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| ≤
                    1 *
                      |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| :=
                  mul_le_mul_of_nonneg_right hga (abs_nonneg _)
                _ ≤ 1 * (∑ i ∈ s, |f i - g i|) :=
                  mul_le_mul_of_nonneg_left ih' zero_le_one
                _ = ∑ i ∈ s, |f i - g i| := one_mul _)

/-- Mean absolute perturbation of a finite product is bounded by the sum of
the factorwise mean absolute perturbations. -/
theorem mean_abs_prod_sub_prod_le_sum_mean_abs
    {Ω ι : Type*} [Fintype Ω] [DecidableEq ι]
    (s : Finset ι) (f g : ι → Ω → ℝ)
    (hf : ∀ i ∈ s, ∀ x, |f i x| ≤ 1)
    (hg : ∀ i ∈ s, ∀ x, |g i x| ≤ 1) :
    mean (fun x =>
        |(∏ i ∈ s, f i x) - ∏ i ∈ s, g i x|) ≤
      ∑ i ∈ s, mean (fun x => |f i x - g i x|) := by
  calc
    mean (fun x =>
        |(∏ i ∈ s, f i x) - ∏ i ∈ s, g i x|) ≤
        mean (fun x =>
          ∑ i ∈ s, |f i x - g i x|) :=
      mean_mono fun x =>
        abs_prod_sub_prod_le_sum_abs s
          (fun i => f i x) (fun i => g i x)
          (fun i hi => hf i hi x)
          (fun i hi => hg i hi x)
    _ = ∑ i ∈ s, mean (fun x => |f i x - g i x|) := by
      simpa [mean] using
        (Finset.expect_sum_comm
          (Finset.univ : Finset Ω) s
          (fun x i => |f i x - g i x|))

/-- Absolute difference of the corresponding product means is controlled by
the same sum of factorwise `L¹` errors. -/
theorem abs_mean_prod_sub_mean_prod_le_sum_mean_abs
    {Ω ι : Type*} [Fintype Ω] [DecidableEq ι]
    (s : Finset ι) (f g : ι → Ω → ℝ)
    (hf : ∀ i ∈ s, ∀ x, |f i x| ≤ 1)
    (hg : ∀ i ∈ s, ∀ x, |g i x| ≤ 1) :
    |mean (fun x => ∏ i ∈ s, f i x) -
        mean (fun x => ∏ i ∈ s, g i x)| ≤
      ∑ i ∈ s, mean (fun x => |f i x - g i x|) := by
  rw [← mean_sub]
  calc
    |mean (fun x =>
        (∏ i ∈ s, f i x) - ∏ i ∈ s, g i x)| ≤
        mean (fun x =>
          |(∏ i ∈ s, f i x) - ∏ i ∈ s, g i x|) := by
      exact Finset.abs_expect_le Finset.univ _
    _ ≤ ∑ i ∈ s, mean (fun x => |f i x - g i x|) :=
      mean_abs_prod_sub_prod_le_sum_mean_abs s f g hf hg

/-- A finite product of unit-bounded factors is itself unit-bounded. -/
theorem abs_prod_le_one
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (u : ι → ℝ)
    (hu : ∀ i ∈ s, |u i| ≤ 1) :
    |∏ i ∈ s, u i| ≤ 1 := by
  rw [Finset.abs_prod]
  exact Finset.prod_le_one
    (fun i _ => abs_nonneg (u i)) hu

/-- One densification step with the remaining bounded factors already
packaged as a finite product. -/
theorem abs_mean_mul_prod_sub_truncateAtOne_mul_prod_le_mean_excessAboveOne
    {Ω ι : Type*} [Fintype Ω] [DecidableEq ι]
    (s : Finset ι)
    {g ν : Ω → ℝ} (u : ι → Ω → ℝ)
    (hgν : ∀ x, g x ≤ ν x)
    (hu : ∀ i ∈ s, ∀ x, |u i x| ≤ 1) :
    |mean (fun x => g x * ∏ i ∈ s, u i x) -
        mean (fun x =>
          truncateAtOne g x * ∏ i ∈ s, u i x)| ≤
      mean (excessAboveOne ν) := by
  exact
    abs_mean_mul_sub_truncateAtOne_mul_le_mean_excessAboveOne
      hgν
      (fun x =>
        abs_prod_le_one s (fun i => u i x)
          (fun i hi => hu i hi x))

namespace HasProjectedMajorantMoments

/-- Square-root loss bound for one densification step with all other factors
in a finite unit-bounded product. -/
theorem abs_mean_mul_prod_sub_truncateAtOne_mul_prod_le_sqrt
    {Ω ι : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq ι]
    (s : Finset ι)
    {ν g : Ω → ℝ} {η : ℝ}
    (h : HasProjectedMajorantMoments ν η)
    (u : ι → Ω → ℝ)
    (hgν : ∀ x, g x ≤ ν x)
    (hu : ∀ i ∈ s, ∀ x, |u i x| ≤ 1) :
    |mean (fun x => g x * ∏ i ∈ s, u i x) -
        mean (fun x =>
          truncateAtOne g x * ∏ i ∈ s, u i x)| ≤
      Real.sqrt (3 * η) :=
  (abs_mean_mul_prod_sub_truncateAtOne_mul_prod_le_mean_excessAboveOne
    s u hgν hu).trans h.mean_excessAboveOne_le_sqrt

end HasProjectedMajorantMoments

end Wikipedia.SzemeredisTheorem
