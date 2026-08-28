import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierParameterDerivativeIteratedBasic

/-!
# Local calculus of the original directional-derivative words

The operator is the original tail-first list of real directional derivatives.
Its smoothness and linearity hold on the original open base. Each induction
step differentiates an equality on a neighborhood inside that open; it makes
no regularity assertion across the boundary and does not reorder derivatives.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesis

open FourierParameter

local notation "word" => iteratedDirectionalDerivativeList

variable {U : Opens ℂ} {f g : ℂ → ℂ}

/-- Every original directional-derivative word remains real smooth on the base open. -/
theorem word_contDiffOn (hf : ContDiffOn ℝ ∞ f U) (s : List ℂ) :
    ContDiffOn ℝ ∞ (word s f) U := by
  induction s with
  | nil => exact hf
  | cons v s ih =>
    exact ((contDiffOn_infty_iff_fderiv_of_isOpen U.isOpen).mp ih).2.clm_apply
      contDiffOn_const

/-- Appending words composes the literal tail-first operators without changing their order. -/
theorem word_append (s t : List ℂ) (f : ℂ → ℂ) :
    word (s ++ t) f = word s (word t f) := by
  induction s with
  | nil => rfl
  | cons v s ih =>
    simp only [List.cons_append, iteratedDirectionalDerivativeList, ih]

/-- Addition commutes with every original word inside the open of smoothness. -/
theorem word_add_eqOn (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (s : List ℂ) :
    Set.EqOn (word s (fun z => f z + g z)) (fun z => word s f z + word s g z) U := by
  induction s with
  | nil => exact fun _ _ => rfl
  | cons v s ih =>
    intro z hz
    have hnear : word s (fun z => f z + g z) =ᶠ[𝓝 z]
        (fun z => word s f z + word s g z) :=
      Filter.mem_of_superset (U.isOpen.mem_nhds hz) (fun _ hy => ih hy)
    have hdf : DifferentiableAt ℝ (word s f) z :=
      ((word_contDiffOn hf s).contDiffAt (U.isOpen.mem_nhds hz)).differentiableAt (by simp)
    have hdg : DifferentiableAt ℝ (word s g) z :=
      ((word_contDiffOn hg s).contDiffAt (U.isOpen.mem_nhds hz)).differentiableAt (by simp)
    change fderiv ℝ (word s (fun z => f z + g z)) z v =
      fderiv ℝ (word s f) z v + fderiv ℝ (word s g) z v
    exact congrArg (fun A : ℂ →L[ℝ] ℂ => A v)
      (hnear.fderiv_eq.trans (fderiv_fun_add hdf hdg))

/-- Complex constant multiplication commutes with every original real derivative word
inside the original open base. -/
theorem word_const_mul_eqOn (hf : ContDiffOn ℝ ∞ f U) (a : ℂ) (s : List ℂ) :
    Set.EqOn (word s (fun z => a * f z)) (fun z => a * word s f z) U := by
  induction s with
  | nil => exact fun _ _ => rfl
  | cons v s ih =>
    intro z hz
    have hnear : word s (fun z => a * f z) =ᶠ[𝓝 z] (fun z => a * word s f z) :=
      Filter.mem_of_superset (U.isOpen.mem_nhds hz) (fun _ hy => ih hy)
    have hdf : DifferentiableAt ℝ (word s f) z :=
      ((word_contDiffOn hf s).contDiffAt (U.isOpen.mem_nhds hz)).differentiableAt (by simp)
    change fderiv ℝ (word s (fun z => a * f z)) z v = a * fderiv ℝ (word s f) z v
    exact congrArg (fun A : ℂ →L[ℝ] ℂ => A v)
      (hnear.fderiv_eq.trans (fderiv_const_mul hdf a))

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesis
