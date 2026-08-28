import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierSynthesisInverseHolomorphicBasic
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierParameterDerivativeIteratedBasic

/-!
# Real directional iterates of an actual holomorphic function

For a function holomorphic on its original open domain, the literal real
directional derivative along a list is its iterated complex derivative
times the product of the directions. Each induction step uses equality
on a neighborhood inside the open domain before differentiating, so no
equality or regularity outside that domain is needed or asserted.
-/

noncomputable section

open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesisInverse

open FourierParameter

variable {V : Set ℂ} {g : ℂ → ℂ}

/-- The literal real-directional iterator agrees with the complex derivative on the open domain. -/
theorem iteratedDirectionalDerivativeList_eqOn_iteratedDeriv (hV : IsOpen V)
    (hg : DifferentiableOn ℂ g V) (s : List ℂ) :
    Set.EqOn (iteratedDirectionalDerivativeList s g)
      (fun z => iteratedDeriv s.length g z * s.prod) V := by
  induction s with
  | nil =>
    intro z _
    simp only [iteratedDirectionalDerivativeList, List.length_nil, iteratedDeriv_zero,
      List.prod_nil, mul_one]
  | cons v s ih =>
    intro z hz
    have hnear : iteratedDirectionalDerivativeList s g =ᶠ[𝓝 z]
        (fun y => iteratedDeriv s.length g y * s.prod) :=
      Filter.mem_of_superset (hV.mem_nhds hz) (fun _ hy => ih hy)
    have hD : DifferentiableAt ℂ (iteratedDeriv s.length g) z :=
      (holomorphic_iteratedDeriv hV hg s.length).differentiableAt (hV.mem_nhds hz)
    change fderiv ℝ (iteratedDirectionalDerivativeList s g) z v =
      iteratedDeriv (s.length + 1) g z * (v * s.prod)
    rw [hnear.fderiv_eq,
      real_fderiv_apply_eq_complex_deriv (hD.mul_const s.prod) v,
      deriv_mul_const hD s.prod, iteratedDeriv_succ]
    ac_rfl

/-- Pointwise form for every list and every point in the genuine holomorphic domain. -/
theorem iteratedDirectionalDerivativeList_eq_iteratedDeriv (hV : IsOpen V)
    (hg : DifferentiableOn ℂ g V) (s : List ℂ) (z : ℂ) (hz : z ∈ V) :
    iteratedDirectionalDerivativeList s g z = iteratedDeriv s.length g z * s.prod :=
  iteratedDirectionalDerivativeList_eqOn_iteratedDeriv hV hg s hz

/-- The exact norm identity transports complex derivative bounds to real directional iterates. -/
theorem norm_iteratedDirectionalDerivativeList (hV : IsOpen V)
    (hg : DifferentiableOn ℂ g V) (s : List ℂ) (z : ℂ) (hz : z ∈ V) :
    ‖iteratedDirectionalDerivativeList s g z‖ =
      ‖iteratedDeriv s.length g z‖ * ‖s.prod‖ := by
  rw [iteratedDirectionalDerivativeList_eq_iteratedDeriv hV hg s z hz, norm_mul]

/-- Every actual real directional iterate is real smooth on the same original open domain. -/
theorem holomorphic_iteratedDirectionalDerivativeList_contDiffOn_real (hV : IsOpen V)
    (hg : DifferentiableOn ℂ g V) (s : List ℂ) :
    ContDiffOn ℝ ∞ (iteratedDirectionalDerivativeList s g) V := by
  have h : ContDiffOn ℝ ∞ (fun z => iteratedDeriv s.length g z * s.prod) V :=
    (holomorphic_iteratedDeriv_contDiffOn_real hV hg s.length).mul contDiffOn_const
  exact h.congr (fun z hz =>
    iteratedDirectionalDerivativeList_eq_iteratedDeriv hV hg s z hz)

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesisInverse
