import Wikipedia.SzemeredisTheorem
import Wikipedia.SzemeredisTheorem.Transference.APSimplexCut
import Wikipedia.GreenTao.Transference.ConvolutionClosure

/-!
# Quantitative relative Szemerédi assembly

This file composes the parts of transference which do not depend on the
remaining sparse-simplex comparison.

* Cut discrepancy against the constant tests retains the mean of the sparse
  weight in its dense model.
* A uniform weighted Szemerédi theorem gives a positive lower bound for the
  dense model's progression count.
* Any quantitative relative-counting comparison then transfers that lower
  bound back to the sparse weight.

The final theorem plugs in the polynomial dense-model theorem obtained from
the ordinary CFZ linear-forms condition.  Its only unproved analytic input
is named explicitly by `RelativeAPComparisonLe`; no asymptotic or
pseudorandomness assertion is hidden in this module.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped Polynomial

/-- The explicit cut-discrepancy error produced by the polynomial
dense-model theorem. -/
noncomputable def polynomialDenseModelError
    (p : ℝ[X]) (cutError approximationError : ℝ) : ℝ :=
  polynomialCoefficientL1 p * cutError +
    approximationError * (2 + cutError)

/-- Quantitative relative counting at progression length `r + 2`.

The sparse weight is only assumed nonnegative and bounded by `ν`; the dense
model is pointwise in `[0,1]`.  This is exactly the comparison theorem left
to the recursive densification argument. -/
def RelativeAPComparisonLe
    (r N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ) (cutError countError : ℝ) : Prop :=
  ∀ (f g : ZMod N → ℝ),
    (∀ x, 0 ≤ f x) →
    (∀ x, f x ≤ ν x) →
    IsUnitBounded g →
    CutDiscrepancyLe (r + 1) f g cutError →
    |cyclicAPCount (r + 2) N f -
        cyclicAPCount (r + 2) N g| ≤ countError

/-- A dense model with enough retained mean and a relative-counting
comparison transfers the weighted Szemerédi lower bound to the sparse
weight. -/
theorem relativeAPCount_lower_bound_of_model
    {r N : ℕ} [NeZero N]
    {ν f g : ZMod N → ℝ}
    {δ denseCount cutError countError : ℝ}
    (hweighted :
      HasWeightedAPCount (r + 2) N δ denseCount)
    (hf0 : ∀ x, 0 ≤ f x)
    (hfν : ∀ x, f x ≤ ν x)
    (hg : IsUnitBounded g)
    (hcut : CutDiscrepancyLe (r + 1) f g cutError)
    (hmean : δ + cutError ≤ mean f)
    (hcomparison :
      RelativeAPComparisonLe
        r N ν cutError countError) :
    denseCount - countError ≤
      cyclicAPCount (r + 2) N f := by
  have hmeanDifference :
      |mean f - mean g| ≤ cutError :=
    hcut.abs_mean_sub_le (Nat.succ_pos r)
  have hgmean : δ ≤ mean g := by
    have hupper := (abs_le.mp hmeanDifference).2
    linarith
  have hdense :
      denseCount ≤ cyclicAPCount (r + 2) N g :=
    hweighted g hg.nonneg hg.le_one hgmean
  have hcountDifference :
      |cyclicAPCount (r + 2) N f -
          cyclicAPCount (r + 2) N g| ≤ countError :=
    hcomparison f g hf0 hfν hg hcut
  have hlower := (abs_le.mp hcountDifference).1
  linarith

/-- Positive dense margin gives a positive sparse progression count. -/
theorem relativeAPCount_pos_of_model
    {r N : ℕ} [NeZero N]
    {ν f g : ZMod N → ℝ}
    {δ denseCount cutError countError : ℝ}
    (hweighted :
      HasWeightedAPCount (r + 2) N δ denseCount)
    (hf0 : ∀ x, 0 ≤ f x)
    (hfν : ∀ x, f x ≤ ν x)
    (hg : IsUnitBounded g)
    (hcut : CutDiscrepancyLe (r + 1) f g cutError)
    (hmean : δ + cutError ≤ mean f)
    (hcomparison :
      RelativeAPComparisonLe
        r N ν cutError countError)
    (hmargin : countError < denseCount) :
    0 < cyclicAPCount (r + 2) N f := by
  have hlower :=
    relativeAPCount_lower_bound_of_model
      hweighted hf0 hfν hg hcut hmean hcomparison
  linarith

/-- End-to-end quantitative transference from the CFZ linear-forms
condition, a weighted dense Szemerédi bound, and the named relative
comparison input.

The progressions have length `r + 2`, so the dense model uses cut arity
`r + 1` and precisely the same `r + 2`-linear-forms condition. -/
theorem relativeAPCount_lower_bound_of_linearFormsCondition
    {r N : ℕ} [NeZero N]
    {ν f : ZMod N → ℝ}
    {linearFormsError cutError approximationError : ℝ}
    {p : ℝ[X]} {δ denseCount countError : ℝ}
    (happroximationError : 0 ≤ approximationError)
    (hcutError : 0 ≤ cutError)
    (hf0 : ∀ x, 0 ≤ f x)
    (hfν : ∀ x, f x ≤ ν x)
    (hν0 : ∀ x, 0 ≤ ν x)
    (hp :
      ApproximatesPositivePartOnUnitInterval
        p approximationError)
    (hLF :
      HasLinearFormsCondition
        (r + 2) N ν linearFormsError)
    (hN : Nat.Coprime N (Nat.factorial (r + 1)))
    (hconvert :
      (2 : ℝ) ^ (2 ^ (r + 1)) * linearFormsError ≤
        cutError ^ (2 ^ (r + 1)))
    (hweighted :
      HasWeightedAPCount (r + 2) N δ denseCount)
    (hmean :
      δ + polynomialDenseModelError
          p cutError approximationError ≤ mean f)
    (hcomparison :
      RelativeAPComparisonLe r N ν
        (polynomialDenseModelError
          p cutError approximationError)
        countError) :
    denseCount - countError ≤
      cyclicAPCount (r + 2) N f := by
  obtain ⟨g, hg, hcut⟩ :=
    exists_cutDiscrepancy_model_of_linearFormsCondition
      happroximationError hcutError
      hf0 hfν hν0 hp hLF hN hconvert
  exact relativeAPCount_lower_bound_of_model
    hweighted hf0 hfν hg hcut hmean hcomparison

/-- Positive-margin version of the complete quantitative wrapper. -/
theorem relativeAPCount_pos_of_linearFormsCondition
    {r N : ℕ} [NeZero N]
    {ν f : ZMod N → ℝ}
    {linearFormsError cutError approximationError : ℝ}
    {p : ℝ[X]} {δ denseCount countError : ℝ}
    (happroximationError : 0 ≤ approximationError)
    (hcutError : 0 ≤ cutError)
    (hf0 : ∀ x, 0 ≤ f x)
    (hfν : ∀ x, f x ≤ ν x)
    (hν0 : ∀ x, 0 ≤ ν x)
    (hp :
      ApproximatesPositivePartOnUnitInterval
        p approximationError)
    (hLF :
      HasLinearFormsCondition
        (r + 2) N ν linearFormsError)
    (hN : Nat.Coprime N (Nat.factorial (r + 1)))
    (hconvert :
      (2 : ℝ) ^ (2 ^ (r + 1)) * linearFormsError ≤
        cutError ^ (2 ^ (r + 1)))
    (hweighted :
      HasWeightedAPCount (r + 2) N δ denseCount)
    (hmean :
      δ + polynomialDenseModelError
          p cutError approximationError ≤ mean f)
    (hcomparison :
      RelativeAPComparisonLe r N ν
        (polynomialDenseModelError
          p cutError approximationError)
        countError)
    (hmargin : countError < denseCount) :
    0 < cyclicAPCount (r + 2) N f := by
  have hlower :=
    relativeAPCount_lower_bound_of_linearFormsCondition
      happroximationError hcutError hf0 hfν hν0 hp
      hLF hN hconvert hweighted hmean hcomparison
  linarith

end Wikipedia.SzemeredisTheorem
