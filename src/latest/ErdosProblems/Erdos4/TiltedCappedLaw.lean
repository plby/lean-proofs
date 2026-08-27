import ErdosProblems.Erdos4.TiltedConditioning
import ErdosProblems.Erdos4.TiltedMoments

/-!
# The capped label law

The unused mass is assigned to a dummy label. On a bad normalizer the
dummy is selected with probability one; no random normalizer is divided
into the importance weights.
-/

open scoped BigOperators

namespace Erdos4.Tilted

open FGKMT

variable {I Ω : Type*} [Fintype I] [Fintype Ω]

noncomputable def fillSubprob (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i ≤ 1) :
    FiniteLaw (Option I) where
  weight := fun i => match i with
    | none => 1 - ∑ j, w j
    | some j => w j
  nonneg := fun i => by
    cases i with
    | none => exact sub_nonneg.mpr hsum
    | some j => exact hw j
  total := by
    rw [Fintype.sum_option]
    ring

theorem fillSubprob_some (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i ≤ 1) (i : I) :
    (fillSubprob w hw hsum).prob (fun j => j = some i) = w i := by
  rw [prob_eq_weight]
  rfl

noncomputable def cappedLabelLaw (ν : FiniteLaw Ω) (μ : FiniteLaw I)
    (E : I → Ω → Prop) (o : Ω) : FiniteLaw (Option I) := by
  classical
  exact if h : eventNormalizer ν μ E o ≤ 2 then
    fillSubprob (fun i => μ.weight i * eventWeight ν (E i) o / 2)
      (fun i => div_nonneg (mul_nonneg (μ.nonneg i) (eventWeight_nonneg ν (E i) o)) (by norm_num))
      (by
        have heq : (∑ i, μ.weight i * eventWeight ν (E i) o / 2) = eventNormalizer ν μ E o / 2 := by
          rw [← Finset.sum_div]
          rfl
        rw [heq]
        linarith)
    else FiniteLaw.dirac none

open Classical in
theorem cappedLabelLaw_some (ν : FiniteLaw Ω) (μ : FiniteLaw I)
    (E : I → Ω → Prop) (o : Ω) (i : I) :
    (cappedLabelLaw ν μ E o).prob (fun j => j = some i) =
      if eventNormalizer ν μ E o ≤ 2 then μ.weight i * eventWeight ν (E i) o / 2 else 0 := by
  unfold cappedLabelLaw
  split_ifs with h
  · exact fillSubprob_some _ _ _ i
  · rw [prob_eq_weight]
    simp [FiniteLaw.dirac]

theorem cappedLabelLaw_support (ν : FiniteLaw Ω) (μ : FiniteLaw I)
    (E : I → Ω → Prop) (o : Ω) (i : I)
    (hi : 0 < (cappedLabelLaw ν μ E o).weight (some i)) : E i o := by
  classical
  rw [← prob_eq_weight, cappedLabelLaw_some] at hi
  by_contra he
  simp only [eventWeight, if_neg he, mul_zero, zero_div, ite_self, lt_self_iff_false] at hi

open Classical in
theorem cappedLabelLaw_some_eq_loss (ν : FiniteLaw Ω) (μ : FiniteLaw I)
    (E : I → Ω → Prop) (o : Ω) (i : I) :
    (cappedLabelLaw ν μ E o).prob (fun j => j = some i) =
      (μ.weight i * eventWeight ν (E i) o -
        if 2 < eventNormalizer ν μ E o then μ.weight i * eventWeight ν (E i) o else 0) / 2 := by
  rw [cappedLabelLaw_some]
  by_cases h : eventNormalizer ν μ E o ≤ 2
  · simp [h, not_lt.mpr h]
  · simp [h, lt_of_not_ge h]

end Erdos4.Tilted
