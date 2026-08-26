import ErdosProblems.Erdos1038.RecoveryPositivePotentialLp
import ErdosProblems.Erdos1038.ExteriorRoots

/-!
# Pointwise analysis of positive-buffer recovery potentials

This file develops the global atom-plus-continuous formula for the
positive-buffer potential.  It is the pointwise input needed for zero-set
nullity and for the exterior-volume limit.
-/

open scoped ENNReal Real
open MeasureTheory Set

namespace Erdos1038

noncomputable section

/-- The continuous logarithmic kernel is integrable at every observation
point, not only on the continuous support. -/
theorem integrable_positiveBufferContinuousRootMeasure_log_kernel_global
    {s alpha x : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (halpha : 0 ≤ alpha) (halphas : alpha ≤ s) :
    Integrable (fun y : ℝ ↦ Real.log |x - y|)
      (positiveBufferContinuousRootMeasure s alpha) := by
  let G : ℝ → ℝ := fun y ↦ Real.log |x - y|
  have hG : Measurable G := by
    dsimp only [G]
    fun_prop
  have hshift : Measurable positiveBufferRootCoordinate := by
    unfold positiveBufferRootCoordinate
    fun_prop
  rw [positiveBufferContinuousRootMeasure]
  rw [integrable_map_measure hG.aestronglyMeasurable hshift.aemeasurable]
  have hbase := integrable_platformConstantReferenceMeasure_log_kernel
    (positiveBufferRatio_nonneg halpha (halphas.trans_lt hs1))
    (positiveBufferDistanceLeft_pos hs)
    (positiveBufferDistanceLeft_lt_two hs hs1)
    (positiveBuffer_threshold_le hs.le hs1 halpha halphas)
    (d := x + 1)
  apply hbase.congr
  filter_upwards with e
  simp only [Function.comp_apply, G, positiveBufferRootCoordinate]
  congr 2
  ring

/-- Global splitting of the positive-buffer potential into its endpoint
atom and its continuous distance-coordinate contribution. -/
theorem positiveBufferPotential_eq_atom_add_continuous
    {s alpha x : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (halpha : 0 ≤ alpha) (halphas : alpha ≤ s) :
    positiveBufferPotential s alpha x =
      alpha * Real.log |x + 1| +
        (1 - alpha) *
          (∫ e : ℝ, Real.log |(x + 1) - e|
            ∂(positiveBufferContinuousDistanceMeasure s alpha)) := by
  let kernel : ℝ → ℝ := fun y ↦ Real.log |x - y|
  have halpha1 : alpha < 1 := halphas.trans_lt hs1
  have hcontinuous : Integrable kernel
      (positiveBufferContinuousRootMeasure s alpha) :=
    integrable_positiveBufferContinuousRootMeasure_log_kernel_global
      hs hs1 halpha halphas
  have hatomScaled : Integrable kernel
      (ENNReal.ofReal alpha • Measure.dirac (-1 : ℝ)) :=
    (integrable_dirac (by finiteness)).smul_measure (by simp)
  have hcontinuousScaled : Integrable kernel
      (ENNReal.ofReal (1 - alpha) •
        positiveBufferContinuousRootMeasure s alpha) :=
    hcontinuous.smul_measure (by simp)
  rw [positiveBufferPotential, positiveBufferMeasure,
    integral_add_measure hatomScaled hcontinuousScaled,
    integral_smul_measure, integral_dirac, integral_smul_measure,
    ENNReal.toReal_ofReal halpha,
    ENNReal.toReal_ofReal (sub_nonneg.mpr halpha1.le)]
  simp only [kernel, smul_eq_mul]
  rw [show x - (-1 : ℝ) = x + 1 by ring,
    integral_positiveBufferContinuousRootMeasure_log_kernel]

/-- The same global splitting, retained in root coordinates. -/
theorem positiveBufferPotential_eq_atom_add_root
    {s alpha x : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (halpha : 0 ≤ alpha) (halphas : alpha ≤ s) :
    positiveBufferPotential s alpha x =
      alpha * Real.log |x + 1| +
        (1 - alpha) *
          (∫ y : ℝ, Real.log |x - y|
            ∂(positiveBufferContinuousRootMeasure s alpha)) := by
  let kernel : ℝ → ℝ := fun y ↦ Real.log |x - y|
  have halpha1 : alpha < 1 := halphas.trans_lt hs1
  have hcontinuous : Integrable kernel
      (positiveBufferContinuousRootMeasure s alpha) :=
    integrable_positiveBufferContinuousRootMeasure_log_kernel_global
      hs hs1 halpha halphas
  have hatomScaled : Integrable kernel
      (ENNReal.ofReal alpha • Measure.dirac (-1 : ℝ)) :=
    (integrable_dirac (by finiteness)).smul_measure (by simp)
  have hcontinuousScaled : Integrable kernel
      (ENNReal.ofReal (1 - alpha) •
        positiveBufferContinuousRootMeasure s alpha) :=
    hcontinuous.smul_measure (by simp)
  rw [positiveBufferPotential, positiveBufferMeasure,
    integral_add_measure hatomScaled hcontinuousScaled,
    integral_smul_measure, integral_dirac, integral_smul_measure,
    ENNReal.toReal_ofReal halpha,
    ENNReal.toReal_ofReal (sub_nonneg.mpr halpha1.le)]
  simp only [kernel, smul_eq_mul]
  rw [show x - (-1 : ℝ) = x + 1 by ring]

/-- To the left of an almost-everywhere lower support bound, a logarithmic
potential is concave. -/
theorem concaveOn_integral_log_abs_sub_of_ae_ge
    (mu : Measure ℝ) {c : ℝ}
    (hsupport : ∀ᵐ y ∂mu, c ≤ y)
    (hintegrable : ∀ x : ℝ,
      Integrable (fun y : ℝ ↦ Real.log |x - y|) mu) :
    ConcaveOn ℝ (Iio c)
      (fun x : ℝ ↦ ∫ y : ℝ, Real.log |x - y| ∂mu) := by
  refine ⟨convex_Iio c, ?_⟩
  intro x hx z hz a b ha hb hab
  have hcombo : Integrable
      (fun y : ℝ ↦ Real.log |(a • x + b • z) - y|) mu :=
    hintegrable _
  have hxint := hintegrable x
  have hzint := hintegrable z
  simp only [smul_eq_mul]
  calc
    a * (∫ y : ℝ, Real.log |x - y| ∂mu) +
          b * (∫ y : ℝ, Real.log |z - y| ∂mu) =
        ∫ y : ℝ,
          (a * Real.log |x - y| + b * Real.log |z - y|) ∂mu := by
      rw [integral_add (hxint.const_mul a) (hzint.const_mul b),
        integral_const_mul, integral_const_mul]
    _ ≤ ∫ y : ℝ, Real.log |(a * x + b * z) - y| ∂mu := by
      apply integral_mono_ae ((hxint.const_mul a).add (hzint.const_mul b))
        hcombo
      filter_upwards [hsupport] with y hy
      have hxy : 0 < y - x := sub_pos.mpr (hx.trans_le hy)
      have hzy : 0 < y - z := sub_pos.mpr (hz.trans_le hy)
      have hleft := strictConcaveOn_log_Ioi.concaveOn.2
        hxy hzy ha hb hab
      have hdist :
          y - (a * x + b * z) = a * (y - x) + b * (y - z) := by
        calc
          y - (a * x + b * z) = (a + b) * y - (a * x + b * z) := by
            rw [hab]
            ring
          _ = a * (y - x) + b * (y - z) := by ring
      have hcomboMem : a * x + b * z ∈ Iio c := by
        simpa only [smul_eq_mul] using! (convex_Iio c) hx hz ha hb hab
      have hcomboLt : a * x + b * z < y := hcomboMem.trans_le hy
      change a * Real.log |x - y| + b * Real.log |z - y| ≤
        Real.log |(a * x + b * z) - y|
      rw [abs_of_neg (sub_neg.mpr (hx.trans_le hy)),
        abs_of_neg (sub_neg.mpr (hz.trans_le hy)),
        abs_of_neg (sub_neg.mpr hcomboLt)]
      simp only [neg_sub]
      simpa only [smul_eq_mul, hdist] using! hleft

/-- To the right of an almost-everywhere upper support bound, a logarithmic
potential is concave. -/
theorem concaveOn_integral_log_abs_sub_of_ae_le
    (mu : Measure ℝ) {c : ℝ}
    (hsupport : ∀ᵐ y ∂mu, y ≤ c)
    (hintegrable : ∀ x : ℝ,
      Integrable (fun y : ℝ ↦ Real.log |x - y|) mu) :
    ConcaveOn ℝ (Ioi c)
      (fun x : ℝ ↦ ∫ y : ℝ, Real.log |x - y| ∂mu) := by
  refine ⟨convex_Ioi c, ?_⟩
  intro x hx z hz a b ha hb hab
  have hcombo : Integrable
      (fun y : ℝ ↦ Real.log |(a • x + b • z) - y|) mu :=
    hintegrable _
  have hxint := hintegrable x
  have hzint := hintegrable z
  simp only [smul_eq_mul]
  calc
    a * (∫ y : ℝ, Real.log |x - y| ∂mu) +
          b * (∫ y : ℝ, Real.log |z - y| ∂mu) =
        ∫ y : ℝ,
          (a * Real.log |x - y| + b * Real.log |z - y|) ∂mu := by
      rw [integral_add (hxint.const_mul a) (hzint.const_mul b),
        integral_const_mul, integral_const_mul]
    _ ≤ ∫ y : ℝ, Real.log |(a * x + b * z) - y| ∂mu := by
      apply integral_mono_ae ((hxint.const_mul a).add (hzint.const_mul b))
        hcombo
      filter_upwards [hsupport] with y hy
      have hxy : 0 < x - y := sub_pos.mpr (hy.trans_lt hx)
      have hzy : 0 < z - y := sub_pos.mpr (hy.trans_lt hz)
      have hleft := strictConcaveOn_log_Ioi.concaveOn.2
        hxy hzy ha hb hab
      have hdist :
          (a * x + b * z) - y = a * (x - y) + b * (z - y) := by
        calc
          (a * x + b * z) - y =
              (a * x + b * z) - (a + b) * y := by
            rw [hab]
            ring
          _ = a * (x - y) + b * (z - y) := by ring
      have hcomboMem : a * x + b * z ∈ Ioi c := by
        simpa only [smul_eq_mul] using! (convex_Ioi c) hx hz ha hb hab
      have hcomboGt : y < a * x + b * z := hy.trans_lt hcomboMem
      change a * Real.log |x - y| + b * Real.log |z - y| ≤
        Real.log |(a * x + b * z) - y|
      rw [abs_of_pos hxy, abs_of_pos hzy, abs_of_pos (sub_pos.mpr hcomboGt)]
      simpa only [smul_eq_mul, hdist] using! hleft

/-- The logarithmic distance to a point is strictly concave on the open
half-line to its left. -/
theorem strictConcaveOn_log_abs_sub_left (c : ℝ) :
    StrictConcaveOn ℝ (Iio c) (fun x : ℝ ↦ Real.log |x - c|) := by
  refine ⟨convex_Iio c, ?_⟩
  intro x hx z hz hxz a b ha hb hab
  have hxc : 0 < c - x := sub_pos.mpr hx
  have hzc : 0 < c - z := sub_pos.mpr hz
  have hdistNe : c - x ≠ c - z := by
    intro h
    apply hxz
    linarith
  have hlog := strictConcaveOn_log_Ioi.2
    hxc hzc hdistNe ha hb hab
  have hcombo : a * x + b * z < c := by
    simpa only [smul_eq_mul] using! (convex_Iio c) hx hz ha.le hb.le hab
  have hdist :
      c - (a * x + b * z) = a * (c - x) + b * (c - z) := by
    calc
      c - (a * x + b * z) = (a + b) * c - (a * x + b * z) := by
        rw [hab]
        ring
      _ = a * (c - x) + b * (c - z) := by ring
  simp only [smul_eq_mul]
  rw [abs_of_neg (sub_neg.mpr hx), abs_of_neg (sub_neg.mpr hz),
    abs_of_neg (sub_neg.mpr hcombo)]
  simp only [neg_sub]
  simpa only [smul_eq_mul, hdist] using! hlog

/-- The logarithmic distance to a point is strictly concave on the open
half-line to its right. -/
theorem strictConcaveOn_log_abs_sub_right (c : ℝ) :
    StrictConcaveOn ℝ (Ioi c) (fun x : ℝ ↦ Real.log |x - c|) := by
  refine ⟨convex_Ioi c, ?_⟩
  intro x hx z hz hxz a b ha hb hab
  have hxc : 0 < x - c := sub_pos.mpr hx
  have hzc : 0 < z - c := sub_pos.mpr hz
  have hdistNe : x - c ≠ z - c := by
    intro h
    apply hxz
    linarith
  have hlog := strictConcaveOn_log_Ioi.2
    hxc hzc hdistNe ha hb hab
  have hcombo : c < a * x + b * z := by
    simpa only [smul_eq_mul] using! (convex_Ioi c) hx hz ha.le hb.le hab
  have hdist :
      (a * x + b * z) - c = a * (x - c) + b * (z - c) := by
    calc
      (a * x + b * z) - c =
          (a * x + b * z) - (a + b) * c := by
        rw [hab]
        ring
      _ = a * (x - c) + b * (z - c) := by ring
  simp only [smul_eq_mul]
  rw [abs_of_pos hxc, abs_of_pos hzc, abs_of_pos (sub_pos.mpr hcombo)]
  simpa only [smul_eq_mul, hdist] using! hlog

/-- Multiplication by a positive scalar preserves strict concavity. -/
theorem strictConcaveOn_const_mul_of_pos
    {D : Set ℝ} {f : ℝ → ℝ} {r : ℝ}
    (hf : StrictConcaveOn ℝ D f) (hr : 0 < r) :
    StrictConcaveOn ℝ D (fun x ↦ r * f x) := by
  refine ⟨hf.1, ?_⟩
  intro x hx z hz hxz a b ha hb hab
  have h := hf.2 hx hz hxz ha hb hab
  have hmul := mul_lt_mul_of_pos_left h hr
  simp only [smul_eq_mul] at hmul ⊢
  calc
    a * (r * f x) + b * (r * f z) =
        r * (a * f x + b * f z) := by ring
    _ < r * f (a * x + b * z) := hmul

/-- The continuous part of a positive buffer is concave everywhere to the
left of its support. -/
theorem positiveBufferContinuousPotential_concaveOn_left
    {s alpha : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (halpha : 0 ≤ alpha) (halphas : alpha ≤ s) :
    ConcaveOn ℝ (Iio (positiveBufferDistanceLeft s - 1))
      (fun x : ℝ ↦ ∫ y : ℝ, Real.log |x - y|
        ∂(positiveBufferContinuousRootMeasure s alpha)) := by
  have hsuppMem : ∀ᵐ y ∂(positiveBufferContinuousRootMeasure s alpha),
      y ∈ Icc (positiveBufferDistanceLeft s - 1) 1 :=
    mem_ae_iff.mpr
      (positiveBufferContinuousRootMeasure_compl_support hs hs1)
  apply concaveOn_integral_log_abs_sub_of_ae_ge
  · filter_upwards [hsuppMem] with y hy
    exact hy.1
  · intro x
    exact integrable_positiveBufferContinuousRootMeasure_log_kernel_global
      hs hs1 halpha halphas

/-- The continuous part of a positive buffer is concave everywhere to the
right of its support. -/
theorem positiveBufferContinuousPotential_concaveOn_right
    {s alpha : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (halpha : 0 ≤ alpha) (halphas : alpha ≤ s) :
    ConcaveOn ℝ (Ioi 1)
      (fun x : ℝ ↦ ∫ y : ℝ, Real.log |x - y|
        ∂(positiveBufferContinuousRootMeasure s alpha)) := by
  have hsuppMem : ∀ᵐ y ∂(positiveBufferContinuousRootMeasure s alpha),
      y ∈ Icc (positiveBufferDistanceLeft s - 1) 1 :=
    mem_ae_iff.mpr
      (positiveBufferContinuousRootMeasure_compl_support hs hs1)
  apply concaveOn_integral_log_abs_sub_of_ae_le
  · filter_upwards [hsuppMem] with y hy
    exact hy.2
  · intro x
    exact integrable_positiveBufferContinuousRootMeasure_log_kernel_global
      hs hs1 halpha halphas

/-- A positive endpoint atom makes the full potential strictly concave on
the component to the left of that atom. -/
theorem positiveBufferPotential_strictConcaveOn_left
    {s alpha : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (halpha : 0 < alpha) (halphas : alpha ≤ s) :
    StrictConcaveOn ℝ (Iio (-1 : ℝ))
      (positiveBufferPotential s alpha) := by
  let C : ℝ → ℝ := fun x ↦
    ∫ y : ℝ, Real.log |x - y|
      ∂(positiveBufferContinuousRootMeasure s alpha)
  have hleft : (-1 : ℝ) ≤ positiveBufferDistanceLeft s - 1 := by
    linarith [positiveBufferDistanceLeft_pos hs]
  have hCwide : ConcaveOn ℝ (Iio (positiveBufferDistanceLeft s - 1)) C := by
    simpa only [C] using! positiveBufferContinuousPotential_concaveOn_left
      hs hs1 halpha.le halphas
  have hC : ConcaveOn ℝ (Iio (-1 : ℝ)) C :=
    hCwide.subset (Iio_subset_Iio hleft) (convex_Iio (-1 : ℝ))
  have hatom : StrictConcaveOn ℝ (Iio (-1 : ℝ))
      (fun x : ℝ ↦ alpha * Real.log |x + 1|) := by
    have hbase := strictConcaveOn_log_abs_sub_left (-1 : ℝ)
    have hrewrite : (fun x : ℝ ↦ Real.log |x + 1|) =
        fun x : ℝ ↦ Real.log |x - (-1 : ℝ)| := by
      funext x
      congr 2
      ring
    have hbase' : StrictConcaveOn ℝ (Iio (-1 : ℝ))
        (fun x : ℝ ↦ Real.log |x + 1|) := by
      rw [hrewrite]
      exact hbase
    exact strictConcaveOn_const_mul_of_pos hbase' halpha
  have hCscaled : ConcaveOn ℝ (Iio (-1 : ℝ))
      (fun x ↦ (1 - alpha) * C x) := by
    simpa only [smul_eq_mul] using!
      hC.smul (sub_nonneg.mpr (halphas.trans_lt hs1).le)
  have hsum := hatom.add_concaveOn hCscaled
  apply hsum.congr
  intro x hx
  simp only [Pi.add_apply]
  rw [positiveBufferPotential_eq_atom_add_root
    hs hs1 halpha.le halphas]

/-- Between the endpoint atom and the continuous support, the positive
buffer potential is strictly concave. -/
theorem positiveBufferPotential_strictConcaveOn_gap
    {s alpha : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (halpha : 0 < alpha) (halphas : alpha ≤ s) :
    StrictConcaveOn ℝ
      (Ioo (-1 : ℝ) (positiveBufferDistanceLeft s - 1))
      (positiveBufferPotential s alpha) := by
  let C : ℝ → ℝ := fun x ↦
    ∫ y : ℝ, Real.log |x - y|
      ∂(positiveBufferContinuousRootMeasure s alpha)
  let D : Set ℝ :=
    Ioo (-1 : ℝ) (positiveBufferDistanceLeft s - 1)
  have hCwide : ConcaveOn ℝ (Iio (positiveBufferDistanceLeft s - 1)) C := by
    simpa only [C] using! positiveBufferContinuousPotential_concaveOn_left
      hs hs1 halpha.le halphas
  have hC : ConcaveOn ℝ D C :=
    hCwide.subset Ioo_subset_Iio_self
      (convex_Ioo (-1 : ℝ) (positiveBufferDistanceLeft s - 1))
  have hatomBase : StrictConcaveOn ℝ D
      (fun x : ℝ ↦ Real.log |x + 1|) := by
    have hwide := strictConcaveOn_log_abs_sub_right (-1 : ℝ)
    have hrewrite : (fun x : ℝ ↦ Real.log |x + 1|) =
        fun x : ℝ ↦ Real.log |x - (-1 : ℝ)| := by
      funext x
      congr 2
      ring
    rw [hrewrite]
    exact hwide.subset Ioo_subset_Ioi_self
      (convex_Ioo (-1 : ℝ) (positiveBufferDistanceLeft s - 1))
  have hatom : StrictConcaveOn ℝ D
      (fun x : ℝ ↦ alpha * Real.log |x + 1|) :=
    strictConcaveOn_const_mul_of_pos hatomBase halpha
  have hCscaled : ConcaveOn ℝ D
      (fun x ↦ (1 - alpha) * C x) := by
    simpa only [smul_eq_mul] using!
      hC.smul (sub_nonneg.mpr (halphas.trans_lt hs1).le)
  have hsum := hatom.add_concaveOn hCscaled
  apply hsum.congr
  intro x hx
  simp only [Pi.add_apply]
  rw [positiveBufferPotential_eq_atom_add_root
    hs hs1 halpha.le halphas]

/-- To the right of the continuous support, the positive endpoint atom
again makes the full potential strictly concave. -/
theorem positiveBufferPotential_strictConcaveOn_right
    {s alpha : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (halpha : 0 < alpha) (halphas : alpha ≤ s) :
    StrictConcaveOn ℝ (Ioi (1 : ℝ))
      (positiveBufferPotential s alpha) := by
  let C : ℝ → ℝ := fun x ↦
    ∫ y : ℝ, Real.log |x - y|
      ∂(positiveBufferContinuousRootMeasure s alpha)
  have hC : ConcaveOn ℝ (Ioi (1 : ℝ)) C := by
    simpa only [C] using! positiveBufferContinuousPotential_concaveOn_right
      hs hs1 halpha.le halphas
  have hatomBase : StrictConcaveOn ℝ (Ioi (1 : ℝ))
      (fun x : ℝ ↦ Real.log |x + 1|) := by
    have hwide := strictConcaveOn_log_abs_sub_right (-1 : ℝ)
    have hrewrite : (fun x : ℝ ↦ Real.log |x + 1|) =
        fun x : ℝ ↦ Real.log |x - (-1 : ℝ)| := by
      funext x
      congr 2
      ring
    rw [hrewrite]
    exact hwide.subset (Ioi_subset_Ioi (by norm_num : (-1 : ℝ) ≤ 1))
      (convex_Ioi (1 : ℝ))
  have hatom : StrictConcaveOn ℝ (Ioi (1 : ℝ))
      (fun x : ℝ ↦ alpha * Real.log |x + 1|) :=
    strictConcaveOn_const_mul_of_pos hatomBase halpha
  have hCscaled : ConcaveOn ℝ (Ioi (1 : ℝ))
      (fun x ↦ (1 - alpha) * C x) := by
    simpa only [smul_eq_mul] using!
      hC.smul (sub_nonneg.mpr (halphas.trans_lt hs1).le)
  have hsum := hatom.add_concaveOn hCscaled
  apply hsum.congr
  intro x hx
  simp only [Pi.add_apply]
  rw [positiveBufferPotential_eq_atom_add_root
    hs hs1 halpha.le halphas]

/-- A strictly concave real function has at most two zeros on its convexity
domain; in particular that zero set is finite. -/
theorem finite_zeroSet_of_strictConcaveOn
    {D : Set ℝ} {f : ℝ → ℝ}
    (hf : StrictConcaveOn ℝ D f) :
    {x : ℝ | x ∈ D ∧ f x = 0}.Finite := by
  let Z : Set ℝ := {x : ℝ | x ∈ D ∧ f x = 0}
  by_contra hfinite
  have hZinf : Z.Infinite := hfinite
  obtain ⟨x, hxZ, _hxempty⟩ := hZinf.exists_notMem_finset ∅
  obtain ⟨y, hyZ, hyx⟩ := hZinf.exists_notMem_finset {x}
  obtain ⟨z, hzZ, hzxy⟩ := hZinf.exists_notMem_finset {x, y}
  have hxy : x ≠ y := by
    have hyx' : y ≠ x := by
      simpa only [Finset.mem_singleton] using! hyx
    exact hyx'.symm
  have hzpair : z ≠ x ∧ z ≠ y := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using! hzxy
  have hzx : z ≠ x := by
    exact hzpair.1
  have hzy : z ≠ y := by
    exact hzpair.2
  have hnoThree : ∀ {a b c : ℝ}, a ∈ Z → b ∈ Z → c ∈ Z →
      a < b → b < c → False := by
    intro a b c haZ hbZ hcZ hab hbc
    have hac : a < c := hab.trans hbc
    let w : ℝ := (c - b) / (c - a)
    let v : ℝ := (b - a) / (c - a)
    have hden : 0 < c - a := sub_pos.mpr hac
    have hw : 0 < w := div_pos (sub_pos.mpr hbc) hden
    have hv : 0 < v := div_pos (sub_pos.mpr hab) hden
    have hwv : w + v = 1 := by
      dsimp only [w, v]
      field_simp [hden.ne']
      ring
    have hcombo : w * a + v * c = b := by
      dsimp only [w, v]
      field_simp [hden.ne']
      ring
    have hstrict := hf.2 haZ.1 hcZ.1 (ne_of_lt hac) hw hv hwv
    simp only [smul_eq_mul, haZ.2, hcZ.2, mul_zero, add_zero,
      hcombo, hbZ.2] at hstrict
    exact (lt_irrefl (0 : ℝ)) hstrict
  rcases lt_or_gt_of_ne hxy with hxylt | hyxlt
  · rcases lt_trichotomy z x with hzxlt | hzxeq | hxzlt
    · exact hnoThree hzZ hxZ hyZ hzxlt hxylt
    · exact hzx hzxeq
    · rcases lt_trichotomy z y with hzylt | hzyeq | hyzlt
      · exact hnoThree hxZ hzZ hyZ hxzlt hzylt
      · exact hzy hzyeq
      · exact hnoThree hxZ hyZ hzZ hxylt hyzlt
  · rcases lt_trichotomy z y with hzylt | hzyeq | hyzlt
    · exact hnoThree hzZ hyZ hxZ hzylt hyxlt
    · exact hzy hzyeq
    · rcases lt_trichotomy z x with hzxlt | hzxeq | hxzlt
      · exact hnoThree hyZ hzZ hxZ hyzlt hzxlt
      · exact hzx hzxeq
      · exact hnoThree hyZ hxZ hzZ hyxlt hxzlt

/-- For a one-cut positive buffer strictly above the zero-platform mass,
the zero set on `[-2,2]` is finite. -/
theorem finite_positiveBufferPotential_zeroSet_s_of_A_lt
    {q alpha : ℝ} (hq : q ∈ Ioo (0 : ℝ) qCeiling)
    (halpha : 0 ≤ alpha) (hAalpha : A q < alpha)
    (halphas : alpha ≤ s q) :
    {x : ℝ | x ∈ Icc (-2 : ℝ) 2 ∧
      positiveBufferPotential (s q) alpha x = 0}.Finite := by
  let U : ℝ → ℝ := positiveBufferPotential (s q) alpha
  let ell : ℝ := positiveBufferDistanceLeft (s q) - 1
  let Zleft : Set ℝ := {x : ℝ | x ∈ Iio (-1 : ℝ) ∧ U x = 0}
  let Zgap : Set ℝ := {x : ℝ | x ∈ Ioo (-1 : ℝ) ell ∧ U x = 0}
  let Zright : Set ℝ := {x : ℝ | x ∈ Ioi (1 : ℝ) ∧ U x = 0}
  let Cover : Set ℝ :=
    Zleft ∪ ({-1} ∪ (Zgap ∪ Zright))
  have hs := s_mem_Ioo_of_mem_Ioo hq
  have halphaPos : 0 < alpha :=
    (A_pos_of_mem_Ioo hq).trans hAalpha
  have hleftConcave : StrictConcaveOn ℝ (Iio (-1 : ℝ)) U := by
    simpa only [U] using! positiveBufferPotential_strictConcaveOn_left
      hs.1 hs.2 halphaPos halphas
  have hgapConcave : StrictConcaveOn ℝ (Ioo (-1 : ℝ) ell) U := by
    simpa only [U, ell] using! positiveBufferPotential_strictConcaveOn_gap
      hs.1 hs.2 halphaPos halphas
  have hrightConcave : StrictConcaveOn ℝ (Ioi (1 : ℝ)) U := by
    simpa only [U] using! positiveBufferPotential_strictConcaveOn_right
      hs.1 hs.2 halphaPos halphas
  have hZleft : Zleft.Finite := by
    simpa only [Zleft] using!
      finite_zeroSet_of_strictConcaveOn hleftConcave
  have hZgap : Zgap.Finite := by
    simpa only [Zgap] using!
      finite_zeroSet_of_strictConcaveOn hgapConcave
  have hZright : Zright.Finite := by
    simpa only [Zright] using!
      finite_zeroSet_of_strictConcaveOn hrightConcave
  have hCover : Cover.Finite := by
    dsimp only [Cover]
    exact hZleft.union ((Set.finite_singleton (-1 : ℝ)).union
      (hZgap.union hZright))
  apply hCover.subset
  intro x hx
  have hxzero : U x = 0 := by
    simpa only [U] using! hx.2
  by_cases hxleft : x < -1
  · exact Or.inl ⟨hxleft, hxzero⟩
  by_cases hxatom : x = -1
  · exact Or.inr (Or.inl hxatom)
  have hxatomRight : -1 < x :=
    lt_of_le_of_ne (le_of_not_gt hxleft) (Ne.symm hxatom)
  by_cases hxgap : x < ell
  · exact Or.inr (Or.inr (Or.inl ⟨⟨hxatomRight, hxgap⟩, hxzero⟩))
  have hellx : ell ≤ x := le_of_not_gt hxgap
  by_cases hxsupportRight : x ≤ 1
  · have hpos : 0 < U x := by
      simpa only [U, ell] using! positiveBufferPotential_s_pos_of_A_lt
        hq halpha hAalpha halphas ⟨hellx, hxsupportRight⟩
    rw [hxzero] at hpos
    exact False.elim ((lt_irrefl (0 : ℝ)) hpos)
  · exact Or.inr (Or.inr (Or.inr
      ⟨lt_of_not_ge hxsupportRight, hxzero⟩))

/-- Consequently every strict positive buffer has a null zero level on the
observation interval. -/
theorem volume_positiveBufferPotential_zeroSet_s_of_A_lt
    {q alpha : ℝ} (hq : q ∈ Ioo (0 : ℝ) qCeiling)
    (halpha : 0 ≤ alpha) (hAalpha : A q < alpha)
    (halphas : alpha ≤ s q) :
    volume {x : ℝ | x ∈ Icc (-2 : ℝ) 2 ∧
      positiveBufferPotential (s q) alpha x = 0} = 0 := by
  exact (finite_positiveBufferPotential_zeroSet_s_of_A_lt
    hq halpha hAalpha halphas).measure_zero volume

end

end Erdos1038
