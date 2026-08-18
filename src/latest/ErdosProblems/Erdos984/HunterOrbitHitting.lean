/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos984.HunterPositiveMeasure

/-!
# Positive orbit kernels give radial recurrence opportunities
-/

open Set Function MeasureTheory Metric
open scoped BigOperators ENNReal

namespace Erdos984

noncomputable section

def hunterOrbitPositiveSet (D : ℕ) (theta : UnitAddTorus (Fin D))
    (a d : ℕ) : Set (UnitAddTorus (Fin D)) :=
  {center | 0 < (hunterOrbitKernelSum D theta a d center).re}

@[fun_prop] lemma continuous_hunterOrbitKernelSum
    (D : ℕ) (theta : UnitAddTorus (Fin D)) (a d : ℕ) :
    Continuous (hunterOrbitKernelSum D theta a d) := by
  have hp : Continuous (fun center : UnitAddTorus (Fin D) ↦
      ∑ q : Fin D → HunterKernelDigit (hunterKernelPower D),
        hunterOrbitCoeff D theta a d q *
          torusFourier (kernelFrequency (hunterKernelPower D) q) center) := by
    fun_prop
  apply hp.congr
  intro center
  exact (hunterOrbitKernelSum_eq_fourier D theta a d center).symm

lemma measurableSet_hunterOrbitPositiveSet
    (D : ℕ) (theta : UnitAddTorus (Fin D)) (a d : ℕ) :
    MeasurableSet (hunterOrbitPositiveSet D theta a d) := by
  exact measurableSet_lt measurable_const
    (by fun_prop : Continuous (fun center ↦
      (hunterOrbitKernelSum D theta a d center).re)).measurable

lemma hunterOrbitKernelSum_im
    (D : ℕ) (theta : UnitAddTorus (Fin D)) (a d : ℕ)
    (center : UnitAddTorus (Fin D)) :
    (hunterOrbitKernelSum D theta a d center).im = 0 := by
  simp [hunterOrbitKernelSum, hunterLocalizedKernel_im]

lemma normSq_hunterOrbitKernelSum_eq_re_sq
    (D : ℕ) (theta : UnitAddTorus (Fin D)) (a d : ℕ)
    (center : UnitAddTorus (Fin D)) :
    Complex.normSq (hunterOrbitKernelSum D theta a d center) =
      (hunterOrbitKernelSum D theta a d center).re ^ 2 := by
  rw [Complex.normSq_apply, hunterOrbitKernelSum_im]
  ring

lemma integrable_of_continuous_real_unitAddTorus
    {D : Type*} [Fintype D] {f : UnitAddTorus D → ℝ}
    (hf : Continuous f) : Integrable f := by
  let cf : C(UnitAddTorus D, ℝ) := ⟨f, hf⟩
  let bf := ContinuousMap.linearIsometryBoundedOfCompact
    (UnitAddTorus D) ℝ ℝ cf
  have hbf := BoundedContinuousFunction.integrable
    (volume : Measure (UnitAddTorus D)) bf
  apply hbf.congr
  filter_upwards with x
  exact ContinuousMap.linearIsometryBoundedOfCompact_apply_apply cf x

/-- Quantitative positive-measure recurrence estimate. -/
lemma one_div_four_mul_pow_le_volumeReal_hunterOrbitPositiveSet
    (D : ℕ) (hD : 400 ≤ D) {theta : UnitAddTorus (Fin D)}
    (htheta : HunterTypicalRotation D theta)
    (a d : ℕ) (hd : 0 < d) (hdN : d < hunterN D) :
    1 / (4 * (D : ℝ) ^ (5 * D)) ≤
      volume.real (hunterOrbitPositiveSet D theta a d) := by
  let S : UnitAddTorus (Fin D) → ℝ := fun center ↦
    (hunterOrbitKernelSum D theta a d center).re
  let m : ℝ := hunterKernelMean D / 2 * hunterX D
  let C : ℝ := 4 * (D : ℝ) ^ (5 * D)
  have hScont : Continuous S := by
    dsimp [S]
    fun_prop
  have hSint : Integrable S := integrable_of_continuous_real_unitAddTorus hScont
  have hSsq : Integrable (fun x ↦ S x ^ 2) :=
    integrable_of_continuous_real_unitAddTorus (hScont.pow 2)
  have hm : 0 < m := by
    dsimp [m]
    have hX : (0 : ℝ) < hunterX D := by
      exact_mod_cast pow_pos (show 0 < D by omega) (100000 * D)
    exact mul_pos (div_pos (hunterKernelMean_pos D) (by norm_num)) hX
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos (by norm_num) (pow_pos (by positivity) _)
  have hmean : ∫ x, S x = m := by
    dsimp [S, m]
    calc
      ∫ x, (hunterOrbitKernelSum D theta a d x).re =
          (∫ x, hunterOrbitKernelSum D theta a d x).re := by
        simpa using integral_re (integrable_hunterOrbitKernelSum D theta a d)
      _ = hunterKernelMean D / 2 * hunterX D := by
        rw [integral_hunterOrbitKernelSum]
        simp
  have hsecondEq : (∫ x, S x ^ 2) =
      ∫ x, Complex.normSq (hunterOrbitKernelSum D theta a d x) := by
    apply integral_congr_ae
    filter_upwards with x
    exact (normSq_hunterOrbitKernelSum_eq_re_sq D theta a d x).symm
  have hsecond : ∫ x, S x ^ 2 ≤ C * m ^ 2 := by
    rw [hsecondEq]
    calc
      ∫ x, Complex.normSq (hunterOrbitKernelSum D theta a d x) ≤
          (D ^ (5 * D) : ℕ) * hunterKernelMean D ^ 2 *
            (hunterX D : ℝ) ^ 2 :=
        integral_normSq_hunterOrbitKernelSum_le_power D hD htheta a d hd hdN
      _ = C * m ^ 2 := by
        dsimp [C, m]
        push_cast
        ring
  simpa [hunterOrbitPositiveSet, S, C] using
    one_div_le_measureReal_posSet_of_secondMoment
      S hScont.measurable hSint hSsq m C hm hC hmean hsecond

lemma pow_neg_sixD_le_volumeReal_hunterOrbitPositiveSet
    (D : ℕ) (hD : 400 ≤ D) {theta : UnitAddTorus (Fin D)}
    (htheta : HunterTypicalRotation D theta)
    (a d : ℕ) (hd : 0 < d) (hdN : d < hunterN D) :
    ((D : ℝ) ^ (6 * D))⁻¹ ≤
      volume.real (hunterOrbitPositiveSet D theta a d) := by
  apply le_trans ?_
    (one_div_four_mul_pow_le_volumeReal_hunterOrbitPositiveSet
      D hD htheta a d hd hdN)
  rw [one_div]
  apply (inv_le_inv₀ (by positivity) (by positivity)).2
  have hfour : (4 : ℝ) ≤ (D : ℝ) ^ D := by
    calc
      (4 : ℝ) ≤ D := by exact_mod_cast (show 4 ≤ D by omega)
      _ ≤ (D : ℝ) ^ D := by
        have hDreal : (1 : ℝ) ≤ D := by exact_mod_cast (show 1 ≤ D by omega)
        rw [show (D : ℝ) ^ D = (D : ℝ) ^ (1 : ℕ) *
            (D : ℝ) ^ (D - 1) by
          rw [← pow_add]
          congr 1
          omega]
        simp only [pow_one]
        exact le_mul_of_one_le_right (by positivity)
          (one_le_pow₀ hDreal)
  calc
    4 * (D : ℝ) ^ (5 * D) ≤
        (D : ℝ) ^ D * (D : ℝ) ^ (5 * D) :=
      mul_le_mul_of_nonneg_right hfour (by positivity)
    _ = (D : ℝ) ^ (6 * D) := by rw [← pow_add]; congr 1; ring

/-- Positivity forces one orbit point into the Euclidean ball of radius
`hunterRho D` around the center. -/
lemma exists_orbit_term_close_of_mem_positiveSet
    (D : ℕ) (hD : 4 ≤ D) (theta : UnitAddTorus (Fin D))
    (a d : ℕ) {center : UnitAddTorus (Fin D)}
    (hcenter : center ∈ hunterOrbitPositiveSet D theta a d) :
    ∃ t < hunterX D,
      squaredNorm (centeredTorusLift
        (center - additiveOrbit theta (a + t * d))) < hunterRho D ^ 2 := by
  by_contra hnot
  push Not at hnot
  have hterm : ∀ t ∈ Finset.range (hunterX D),
      (hunterLocalizedKernel D
        (center - additiveOrbit theta (a + t * d))).re ≤ 0 := by
    intro t ht
    apply hunterLocalizedKernel_re_nonpos_of_rho_sq_le_squaredNorm D hD
    exact hnot t (by simpa using ht)
  have hsum : (∑ t ∈ Finset.range (hunterX D),
      (hunterLocalizedKernel D
        (center - additiveOrbit theta (a + t * d))).re) ≤ 0 := by
    exact Finset.sum_nonpos fun t ht ↦ hterm t ht
  apply (not_lt_of_ge hsum)
  simpa [hunterOrbitPositiveSet, hunterOrbitKernelSum, additiveOrbit, map_sum] using hcenter

lemma radial_opportunity_of_mem_positiveSet
    (D : ℕ) (hD : 4 ≤ D) (theta : UnitAddTorus (Fin D))
    (a d : ℕ) {center : UnitAddTorus (Fin D)}
    (hcenter : center ∈ hunterOrbitPositiveSet D theta a d) :
    ∃ t < hunterX D, ∃ u : EuclideanSpace ℝ (Fin D),
      additiveOrbit theta (a + t * d) = center + euclideanToTorus u ∧
      radialBin (hunterDelta D) u ≤ hunterK D := by
  obtain ⟨t, ht, hclose⟩ :=
    exists_orbit_term_close_of_mem_positiveSet D hD theta a d hcenter
  let z := center - additiveOrbit theta (a + t * d)
  let u : EuclideanSpace ℝ (Fin D) := -centeredTorusLift z
  have hmap : euclideanToTorus u = -z := by
    dsimp [u]
    rw [map_neg, euclideanToTorus_centeredTorusLift]
  have horbit : additiveOrbit theta (a + t * d) =
      center + euclideanToTorus u := by
    rw [hmap]
    dsimp [z]
    abel
  have hunorm : ‖u‖ < hunterRho D := by
    have hrho := hunterRho_pos (show 0 < D by omega)
    have hsquare : ‖u‖ ^ 2 < hunterRho D ^ 2 := by
      simpa [u, z, squaredNorm] using hclose
    exact (sq_lt_sq₀ (norm_nonneg _) hrho.le).1 hsquare
  refine ⟨t, ht, u, horbit, radialBin_le (hunterDelta_pos (by omega)) ?_⟩
  rw [hunter_radialLower_eq_rho]
  exact hunorm

end

end Erdos984
