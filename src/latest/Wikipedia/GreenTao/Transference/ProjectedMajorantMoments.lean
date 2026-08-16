import Wikipedia.GreenTao.Transference.Densification
import Wikipedia.GreenTao.Transference.StrongLinearForms

/-!
# Moment packages for projected majorants

The positive-arity fiber convolution preserves the first moment exactly and
contracts the second moment.  Consequently, a nonnegative input weight whose
first moment is within `η₁` of one and whose second moment is at most
`1 + η₂` produces a projected majorant with common first/second moment error

```
max η₂ (2 * η₁).
```

The factor `2` in the lower second-moment estimate comes from Jensen:
if `m ≥ 1 - η₁`, then `m ^ 2 ≥ 1 - 2 * η₁`.

This file deliberately exposes the input estimates as a named conditional
interface.  `FaceMoments` proves centered face and box-moment estimates, but
the current transference API does not yet define the densification projection
or identify its first and doubled second moments with CFZ subproducts.
Accordingly, there is no honest theorem here claiming that an arbitrary
`HasLinearFormsCondition` directly supplies this interface.  Such a theorem
will require those geometry-specific definitions and exact reindexing
identities.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## The exact conditional interface -/

/-- The one-sided input moments sufficient for positive-arity fiber
convolution to produce a projected-majorant moment package.

Only an upper bound is required for the input second moment: its projected
lower bound follows from the first moment and Jensen's inequality. -/
structure HasFiberConvolutionInputMoments
    {G : Type*} [Fintype G] [AddCommGroup G]
    (n : ℕ) (w : (Fin (n + 1) → G) → ℝ)
    (η₁ η₂ : ℝ) : Prop where
  firstError_nonneg : 0 ≤ η₁
  secondError_nonneg : 0 ≤ η₂
  nonneg : ∀ x, 0 ≤ w x
  firstMoment_close : |mean w - 1| ≤ η₁
  secondMoment_upper :
    mean (fun x => w x ^ 2) ≤ 1 + η₂

namespace HasFiberConvolutionInputMoments

/-- Exact first-moment preservation gives the projected first-moment
estimate with no loss. -/
theorem projected_firstMoment_close
    {G : Type*} [Fintype G] [AddCommGroup G]
    {n : ℕ} {w : (Fin (n + 1) → G) → ℝ}
    {η₁ η₂ : ℝ}
    (h : HasFiberConvolutionInputMoments n w η₁ η₂) :
    |mean (fiberConvolution (n + 1) w) - 1| ≤ η₁ := by
  rw [mean_fiberConvolution]
  exact h.firstMoment_close

/-- Jensen supplies the lower projected second-moment estimate. -/
theorem projected_secondMoment_lower
    {G : Type*} [Fintype G] [AddCommGroup G]
    {n : ℕ} {w : (Fin (n + 1) → G) → ℝ}
    {η₁ η₂ : ℝ}
    (h : HasFiberConvolutionInputMoments n w η₁ η₂) :
    1 - 2 * η₁ ≤
      mean (fun z => fiberConvolution (n + 1) w z ^ 2) := by
  have hmean_lower : 1 - η₁ ≤ mean w := by
    have hneg := (abs_le.mp h.firstMoment_close).1
    linarith
  have hjensen :=
    sq_mean_le_mean_sq (fiberConvolution (n + 1) w)
  rw [mean_fiberConvolution] at hjensen
  nlinarith [sq_nonneg (mean w - 1)]

/-- Second-moment contraction supplies the upper projected estimate. -/
theorem projected_secondMoment_upper
    {G : Type*} [Fintype G] [AddCommGroup G]
    {n : ℕ} {w : (Fin (n + 1) → G) → ℝ}
    {η₁ η₂ : ℝ}
    (h : HasFiberConvolutionInputMoments n w η₁ η₂) :
    mean (fun z => fiberConvolution (n + 1) w z ^ 2) ≤
      1 + η₂ :=
  (fiberConvolution_secondMoment_le n w).trans h.secondMoment_upper

/-- The two one-sided estimates combine into the sharp common absolute
second-moment error available from this interface. -/
theorem projected_secondMoment_close
    {G : Type*} [Fintype G] [AddCommGroup G]
    {n : ℕ} {w : (Fin (n + 1) → G) → ℝ}
    {η₁ η₂ : ℝ}
    (h : HasFiberConvolutionInputMoments n w η₁ η₂) :
    |mean (fun z => fiberConvolution (n + 1) w z ^ 2) - 1| ≤
      max η₂ (2 * η₁) := by
  apply abs_le.mpr
  constructor
  · have hlower := h.projected_secondMoment_lower
    have hmax : 2 * η₁ ≤ max η₂ (2 * η₁) :=
      le_max_right _ _
    linarith
  · have hupper := h.projected_secondMoment_upper
    have hmax : η₂ ≤ max η₂ (2 * η₁) :=
      le_max_left _ _
    linarith

/-- Package a positive-arity fiber convolution as a projected majorant.
The common error is `max η₂ (2 * η₁)`: the first moment costs `η₁`,
the upper second moment costs `η₂`, and Jensen costs `2 * η₁` on the lower
side. -/
theorem hasProjectedMajorantMoments
    {G : Type*} [Fintype G] [AddCommGroup G]
    {n : ℕ} {w : (Fin (n + 1) → G) → ℝ}
    {η₁ η₂ : ℝ}
    (h : HasFiberConvolutionInputMoments n w η₁ η₂) :
    HasProjectedMajorantMoments
      (fiberConvolution (n + 1) w)
      (max η₂ (2 * η₁)) := by
  refine
    { error_nonneg := ?_
      nonneg := fun z => fiberConvolution_nonneg_succ h.nonneg z
      firstMoment_close := ?_
      secondMoment_close := h.projected_secondMoment_close }
  · exact h.secondError_nonneg.trans (le_max_left _ _)
  · exact h.projected_firstMoment_close.trans <|
      (show η₁ ≤ max η₂ (2 * η₁) by
        have hdouble : η₁ ≤ 2 * η₁ := by
          linarith [h.firstError_nonneg]
        exact hdouble.trans (le_max_right _ _))

/-- The centered `L²` estimate retains the sharper additive error before
the two moment bounds are folded into one common parameter. -/
theorem projected_centeredSecondMoment_le
    {G : Type*} [Fintype G] [AddCommGroup G]
    {n : ℕ} {w : (Fin (n + 1) → G) → ℝ}
    {η₁ η₂ : ℝ}
    (h : HasFiberConvolutionInputMoments n w η₁ η₂) :
    mean (fun z =>
      (fiberConvolution (n + 1) w z - 1) ^ 2) ≤
        η₂ + 2 * η₁ := by
  have hmean_lower : 1 - η₁ ≤ mean w := by
    have hneg := (abs_le.mp h.firstMoment_close).1
    linarith
  rw [mean_sub_one_sq_eq, mean_fiberConvolution]
  have hsecond := h.projected_secondMoment_upper
  linarith

/-- Squared `L¹` consequence of the sharp centered `L²` estimate. -/
theorem projected_centeredAbsMean_sq_le
    {G : Type*} [Fintype G] [AddCommGroup G]
    {n : ℕ} {w : (Fin (n + 1) → G) → ℝ}
    {η₁ η₂ : ℝ}
    (h : HasFiberConvolutionInputMoments n w η₁ η₂) :
    (mean (fun z =>
      |fiberConvolution (n + 1) w z - 1|)) ^ 2 ≤
        η₂ + 2 * η₁ := by
  calc
    (mean (fun z =>
        |fiberConvolution (n + 1) w z - 1|)) ^ 2 ≤
        mean (fun z =>
          |fiberConvolution (n + 1) w z - 1| ^ 2) :=
      sq_mean_le_mean_sq _
    _ = mean (fun z =>
        (fiberConvolution (n + 1) w z - 1) ^ 2) := by
      apply congrArg mean
      funext z
      exact sq_abs _
    _ ≤ η₂ + 2 * η₁ :=
      h.projected_centeredSecondMoment_le

/-- Square-root form of the sharp projected `L¹` estimate. -/
theorem projected_centeredAbsMean_le_sqrt
    {G : Type*} [Fintype G] [AddCommGroup G]
    {n : ℕ} {w : (Fin (n + 1) → G) → ℝ}
    {η₁ η₂ : ℝ}
    (h : HasFiberConvolutionInputMoments n w η₁ η₂) :
    mean (fun z =>
      |fiberConvolution (n + 1) w z - 1|) ≤
        Real.sqrt (η₂ + 2 * η₁) := by
  apply
    (Real.le_sqrt
      (mean_nonneg fun z =>
        abs_nonneg (fiberConvolution (n + 1) w z - 1))
      (add_nonneg h.secondError_nonneg
        (mul_nonneg (by norm_num) h.firstError_nonneg))).2
  exact h.projected_centeredAbsMean_sq_le

end HasFiberConvolutionInputMoments

/-! ## Generalized-convolution specialization -/

/-- The conditional input-moment interface specialized to the product of a
family of deleted-coordinate tests. -/
abbrev HasGeneralizedConvolutionInputMoments
    {G : Type*} [Fintype G] [AddCommGroup G]
    (n : ℕ) (u : CutTestFamily G (n + 1))
    (η₁ η₂ : ℝ) : Prop :=
  HasFiberConvolutionInputMoments n (cutTestProduct u) η₁ η₂

namespace HasGeneralizedConvolutionInputMoments

/-- Componentwise nonnegativity and the two explicit product-moment
estimates instantiate the generalized-convolution interface. -/
theorem of_componentwise_nonneg
    {G : Type*} [Fintype G] [AddCommGroup G]
    {n : ℕ} {u : CutTestFamily G (n + 1)}
    {η₁ η₂ : ℝ}
    (hη₁ : 0 ≤ η₁) (hη₂ : 0 ≤ η₂)
    (hu : ∀ i y, 0 ≤ u i y)
    (hmean : |mean (cutTestProduct u) - 1| ≤ η₁)
    (hsecond :
      mean (fun x => cutTestProduct u x ^ 2) ≤ 1 + η₂) :
    HasGeneralizedConvolutionInputMoments n u η₁ η₂ := by
  refine
    { firstError_nonneg := hη₁
      secondError_nonneg := hη₂
      nonneg := ?_
      firstMoment_close := hmean
      secondMoment_upper := hsecond }
  intro x
  exact Finset.prod_nonneg fun i _ =>
    hu i (eraseCoordinate i x)

/-- A generalized convolution satisfying the explicit input-moment
interface is a projected majorant with common error
`max η₂ (2 * η₁)`. -/
theorem hasProjectedMajorantMoments
    {G : Type*} [Fintype G] [AddCommGroup G]
    {n : ℕ} {u : CutTestFamily G (n + 1)}
    {η₁ η₂ : ℝ}
    (h : HasGeneralizedConvolutionInputMoments n u η₁ η₂) :
    HasProjectedMajorantMoments
      (generalizedConvolution (n + 1) u)
      (max η₂ (2 * η₁)) := by
  change HasProjectedMajorantMoments
    (fiberConvolution (n + 1) (cutTestProduct u))
    (max η₂ (2 * η₁))
  exact HasFiberConvolutionInputMoments.hasProjectedMajorantMoments h

/-- Direct hypothesis-driven bridge, phrased without first constructing
the named interface. -/
theorem hasProjectedMajorantMoments_of_componentwise_nonneg
    {G : Type*} [Fintype G] [AddCommGroup G]
    {n : ℕ} {u : CutTestFamily G (n + 1)}
    {η₁ η₂ : ℝ}
    (hη₁ : 0 ≤ η₁) (hη₂ : 0 ≤ η₂)
    (hu : ∀ i y, 0 ≤ u i y)
    (hmean : |mean (cutTestProduct u) - 1| ≤ η₁)
    (hsecond :
      mean (fun x => cutTestProduct u x ^ 2) ≤ 1 + η₂) :
    HasProjectedMajorantMoments
      (generalizedConvolution (n + 1) u)
      (max η₂ (2 * η₁)) :=
  hasProjectedMajorantMoments
    (of_componentwise_nonneg hη₁ hη₂ hu hmean hsecond)

end HasGeneralizedConvolutionInputMoments

/-! ## Reusing a full two-sided moment package -/

namespace HasProjectedMajorantMoments

/-- A full moment package on the input weight descends through positive
fiber convolution.  Equal first/second input errors give the explicit
common projected error `2 * η`. -/
theorem fiberConvolution
    {G : Type*} [Fintype G] [AddCommGroup G]
    {n : ℕ} {w : (Fin (n + 1) → G) → ℝ}
    {η : ℝ}
    (h : HasProjectedMajorantMoments w η) :
    HasProjectedMajorantMoments
      (Wikipedia.SzemeredisTheorem.fiberConvolution (n + 1) w)
      (2 * η) := by
  have hinput :
      HasFiberConvolutionInputMoments n w η η := by
    refine
      { firstError_nonneg := h.error_nonneg
        secondError_nonneg := h.error_nonneg
        nonneg := h.nonneg
        firstMoment_close := h.firstMoment_close
        secondMoment_upper := ?_ }
    have hupper := (abs_le.mp h.secondMoment_close).2
    rw [sub_le_iff_le_add] at hupper
    simpa [add_comm] using hupper
  have hprojected :=
    hinput.hasProjectedMajorantMoments
  have hmax : max η (2 * η) = 2 * η :=
    max_eq_right (by linarith [h.error_nonneg])
  rw [hmax] at hprojected
  exact hprojected

/-- Generalized-convolution specialization of
`HasProjectedMajorantMoments.fiberConvolution`. -/
theorem generalizedConvolution
    {G : Type*} [Fintype G] [AddCommGroup G]
    {n : ℕ} {u : CutTestFamily G (n + 1)}
    {η : ℝ}
    (h : HasProjectedMajorantMoments (cutTestProduct u) η) :
    HasProjectedMajorantMoments
      (Wikipedia.SzemeredisTheorem.generalizedConvolution (n + 1) u)
      (2 * η) := by
  change HasProjectedMajorantMoments
    (Wikipedia.SzemeredisTheorem.fiberConvolution
      (n + 1) (cutTestProduct u))
    (2 * η)
  exact h.fiberConvolution

end HasProjectedMajorantMoments

end Wikipedia.SzemeredisTheorem
