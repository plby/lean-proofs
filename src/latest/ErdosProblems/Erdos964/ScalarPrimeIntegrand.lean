import ErdosProblems.Erdos964.ScalarSieveFace
import ErdosProblems.Erdos964.GGPYIntegralComparison
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# The two smooth pieces of the scalar prime integrand
-/

namespace Erdos964

theorem scalarSieveFace_eq_min (z : ℝ) :
    scalarSieveFace z = truncatedSieveFace (min z 1) := by
  by_cases hz : z ≤ 1
  · rw [scalarSieveFace_eq_small z hz, min_eq_left hz]
  · rw [scalarSieveFace_eq_large z (by linarith), min_eq_right (by linarith)]

theorem continuous_scalarSieveFace : Continuous scalarSieveFace := by
  have hpoly : Continuous (fun z : ℝ => z * sieveFaceKernel z) := by
    unfold sieveFaceKernel
    fun_prop
  have heq : scalarSieveFace = fun z => min z 1 * sieveFaceKernel (min z 1) := by
    funext z
    rw [scalarSieveFace_eq_min, truncatedSieveFace_eq]
  rw [heq]
  exact hpoly.comp (continuous_id.min continuous_const)

noncomputable def scalarPrimeIntegrand (a z : ℝ) : ℝ :=
  scalarSieveFace z / (z * (1 - a * z))

noncomputable def scalarSmallPrimeIntegrand (a z : ℝ) : ℝ :=
  sieveFaceKernel z / (1 - a * z)

noncomputable def scalarLargePrimeIntegrand (a z : ℝ) : ℝ :=
  (41 / 60) / (z * (1 - a * z))

theorem scalarPrimeIntegrand_eq_small (a z : ℝ) (hz : z ≤ 1) :
    scalarPrimeIntegrand a z = scalarSmallPrimeIntegrand a z := by
  rw [scalarPrimeIntegrand, scalarSieveFace_eq_small z hz, ggpy_face_integrand_eq]
  rfl

theorem scalarPrimeIntegrand_eq_large (a z : ℝ) (hz : 1 ≤ z) :
    scalarPrimeIntegrand a z = scalarLargePrimeIntegrand a z := by
  rw [scalarPrimeIntegrand, scalarSieveFace_eq_large z hz]
  have h : truncatedSieveFace 1 = 41 / 60 := by
    simpa only [scalarSieveFace_eq_small 1 le_rfl] using scalarSieveFace_one
  rw [h]
  rfl

theorem smooth_quotient_on (f q : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (hq : ContDiff ℝ 1 q)
    (s : Set ℝ) (hne : ∀ z ∈ s, q z ≠ 0) :
    (∀ z ∈ s, DifferentiableAt ℝ (fun z => f z / q z) z) ∧
      ContinuousOn (deriv (fun z => f z / q z)) s := by
  have hU : IsOpen {z | q z ≠ 0} := isOpen_ne_fun hq.continuous continuous_const
  have hquot : ContDiffOn ℝ 1 (fun z => f z / q z) {z | q z ≠ 0} :=
    hf.contDiffOn.div hq.contDiffOn (fun z hz => hz)
  constructor
  · intro z hz
    exact (hf.differentiable (by decide) z).div (hq.differentiable (by decide) z) (hne z hz)
  · exact (hquot.continuousOn_deriv_of_isOpen hU le_rfl).mono hne

theorem scalarSmallPrimeIntegrand_smooth_on (a : ℝ) (s : Set ℝ)
    (hs : ∀ z ∈ s, 1 - a * z ≠ 0) :
    (∀ z ∈ s, DifferentiableAt ℝ (scalarSmallPrimeIntegrand a) z) ∧
      ContinuousOn (deriv (scalarSmallPrimeIntegrand a)) s := by
  unfold scalarSmallPrimeIntegrand
  apply smooth_quotient_on _ _ _ _ s hs
  · unfold sieveFaceKernel
    fun_prop
  · fun_prop

theorem scalarLargePrimeIntegrand_smooth_on (a : ℝ) (s : Set ℝ)
    (hz : ∀ z ∈ s, z ≠ 0) (hs : ∀ z ∈ s, 1 - a * z ≠ 0) :
    (∀ z ∈ s, DifferentiableAt ℝ (scalarLargePrimeIntegrand a) z) ∧
      ContinuousOn (deriv (scalarLargePrimeIntegrand a)) s := by
  unfold scalarLargePrimeIntegrand
  apply smooth_quotient_on _ _ (by fun_prop) (by fun_prop) s
  intro z hzs
  exact mul_ne_zero (hz z hzs) (hs z hzs)

end Erdos964
