import Wikipedia.HopfProblem.ToricTwists
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Torus coordinates and logarithms on the cusp model

The chart-independent coordinates on the dense torus turn the constructed
twisted action into the explicit multiplicative formula of §4.3. Logarithms
of norms then turn integral monomial substitutions into real linear maps.
-/

noncomputable section

open Set Topology
open scoped ContDiff Matrix

namespace Wikipedia.HopfProblem.ToricSpace

open ToricCharts ToricFan Triangle

/-- These are the torus characters `(x₁,x₂,t)`. Their arbitrary extension to
the boundary is only used to make this a total function. -/
def torusCoordinates (x : Space) : CoordinateSpace 3 :=
  monomial (preferredTriangle x).rays ((parametrization (preferredTriangle x)).symm x)

theorem torusCoordinates_inclusion (s : Triangle) {z : CoordinateSpace 3} (hz : z ∈ torus) :
    torusCoordinates (inclusion s z) = monomial s.rays z := by
  have he := parametrization_transition s (preferredTriangle (inclusion s z))
    (preferred_mem (inclusion s z))
  unfold torusCoordinates
  rw [he.2]
  change monomial (preferredTriangle (inclusion s z)).rays
    (monomial (transition s (preferredTriangle (inclusion s z))) z) = _
  rw [monomial_mul_on_torus _ _ hz, transition_covariance]

@[simp] theorem torusCoordinates_time (x : Space) : torusCoordinates x 2 = time x :=
  monomial_rays_height _ _

theorem torusCoordinates_nonzero {x : Space} (hx : x ∈ openTorus) (i : Fin 3) :
    torusCoordinates x i ≠ 0 := by
  obtain ⟨z, hz, rfl⟩ := hx
  rw [torusCoordinates_inclusion _ hz]
  exact monomial_mapsTo_torus _ hz i

theorem inclusion_preimage_openTorus (s : Triangle) : inclusion s ⁻¹' openTorus = torus := by
  ext z
  simp [mem_openTorus_iff, Triangle.time, torus, Fin.forall_fin_succ, and_assoc]

theorem torusCoordinates_holomorphic :
    ContMDiffOn (modelWithCornersSelf ℂ (CoordinateSpace 3))
      (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω torusCoordinates openTorus := by
  apply contMDiffOn_of_comp_inclusion _ _ openTorus_isOpen
  intro s
  rw [inclusion_preimage_openTorus]
  exact ((monomial_contDiffOn s.rays ω).mono (torus_subset_domain _)).contMDiffOn.congr
    (fun z hz => torusCoordinates_inclusion s hz)

theorem torusCoordinates_translate (v : Fin 2 → ℤ) {x : Space} (hx : x ∈ openTorus) :
    torusCoordinates (translate v x) = monomial (shear v) (torusCoordinates x) := by
  obtain ⟨z, hz, rfl⟩ := hx
  rw [translate_inclusion, torusCoordinates_inclusion _ hz,
    torusCoordinates_inclusion _ hz, rays_shift]
  exact (monomial_mul_on_torus _ _ hz).symm

theorem monomial_rays_factors (s : Triangle) (u : ActingTorus) :
    monomial s.rays (factors s u) = (fun j => (u j : ℂ)) := by
  rw [factors, monomial_mul_on_torus _ _ (fun j => (u j).ne_zero), rays_dual, monomial_one]

theorem torusCoordinates_action (u : ActingTorus) {x : Space} (hx : x ∈ openTorus) :
    torusCoordinates (torusAction u x) = (fun j => (u j : ℂ)) * torusCoordinates x := by
  obtain ⟨z, hz, rfl⟩ := hx
  have hs : scale referenceTriangle u z ∈ torus :=
    fun j => mul_ne_zero (factors_nonzero _ _ j) (hz j)
  rw [torusAction_inclusion, torusCoordinates_inclusion _ hs, torusCoordinates_inclusion _ hz]
  rw [scale, monomial_mul, monomial_rays_factors]

theorem torusCoordinates_variableMultiplier (u : ℂ → Fin 2 → ℂˣ)
    {x : Space} (hx : x ∈ openTorus) :
    torusCoordinates (variableMultiplier u x) =
      (fun j => (fibreMultiplier (u (time x)) j : ℂ)) * torusCoordinates x :=
  torusCoordinates_action _ hx

theorem torusCoordinates_twistedTranslate (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) {x : Space} (hx : x ∈ openTorus) :
    torusCoordinates (twistedTranslate C v x) =
      (fun j => (fibreMultiplier (exponentialMultiplier C v (time x)) j : ℂ)) *
        monomial (shear (cuspVector v)) (torusCoordinates x) := by
  have ht : translate (cuspVector v) x ∈ openTorus := by
    simpa only [mem_openTorus_iff, time_translate] using hx
  rw [twistedTranslate, torusCoordinates_variableMultiplier _ ht,
    time_translate, torusCoordinates_translate _ hx]

theorem torusCoordinates_twistedTranslate_apply (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) {x : Space} (hx : x ∈ openTorus) (i : Fin 2) :
    torusCoordinates (twistedTranslate C v x) i.castSucc =
      (exponentialMultiplier C v (time x) i : ℂ) *
        (time x) ^ cuspVector v i * torusCoordinates x i.castSucc := by
  rw [torusCoordinates_twistedTranslate C v hx]
  fin_cases i <;>
    simp [monomial, shear, fibreMultiplier, Fin.prod_univ_succ, mul_comm, mul_left_comm, mul_assoc]

def logNorm (z : CoordinateSpace 3) : Fin 3 → ℝ := fun i => Real.log ‖z i‖

theorem logNorm_monomial (A : Matrix (Fin 3) (Fin 3) ℤ)
    {z : CoordinateSpace 3} (hz : z ∈ torus) :
    logNorm (monomial A z) = A.map (Int.castRingHom ℝ) *ᵥ logNorm z := by
  ext i
  change Real.log ‖∏ j, z j ^ A i j‖ = ∑ j, (A i j : ℝ) * Real.log ‖z j‖
  rw [norm_prod, Real.log_prod (fun j _ => norm_ne_zero_iff.mpr (zpow_ne_zero _ (hz j)))]
  simp [norm_zpow, Real.log_zpow]

def logCoordinates (x : Space) : Fin 3 → ℝ := logNorm (torusCoordinates x)

theorem logCoordinates_inclusion (s : Triangle) {z : CoordinateSpace 3} (hz : z ∈ torus) :
    logCoordinates (inclusion s z) = s.rays.map (Int.castRingHom ℝ) *ᵥ logNorm z := by
  rw [logCoordinates, torusCoordinates_inclusion s hz, logNorm_monomial _ hz]

@[simp] theorem logCoordinates_time (x : Space) : logCoordinates x 2 = Real.log ‖time x‖ := by
  simp [logCoordinates, logNorm]

theorem logNorm_sum (s : Triangle) {z : CoordinateSpace 3} (hz : z ∈ torus) :
    ∑ j, logNorm z j = Real.log ‖Triangle.time z‖ := by
  have he := congrFun (logCoordinates_inclusion s hz) 2
  simpa [Matrix.mulVec, dotProduct, logCoordinates_time] using he.symm

/-- The real logarithmic multiplier matrix `R(t) = -2π Im C(t)`. -/
def driftMatrix (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (t : ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => -2 * Real.pi * (C t i j).im

theorem exponentialMultiplier_log_norm (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) (t : ℂ) (i : Fin 2) :
    Real.log ‖(exponentialMultiplier C v t i : ℂ)‖ =
      (driftMatrix C t *ᵥ (fun j => (v j : ℝ))) i := by
  simp [exponentialMultiplier, Complex.norm_exp, driftMatrix, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two, Complex.mul_re, Complex.mul_im]
  ring

theorem logCoordinates_twistedTranslate (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) {x : Space} (hx : x ∈ openTorus) (i : Fin 2) :
    logCoordinates (twistedTranslate C v x) i.castSucc = logCoordinates x i.castSucc +
      Real.log ‖time x‖ * (cuspVector v i : ℝ) +
      (driftMatrix C (time x) *ᵥ (fun j => (v j : ℝ))) i := by
  have ht : time x ≠ 0 := (mem_openTorus_iff x).mp hx
  have hu : ‖(exponentialMultiplier C v (time x) i : ℂ)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (exponentialMultiplier C v (time x) i).ne_zero
  have hp : ‖(time x) ^ cuspVector v i‖ ≠ 0 := norm_ne_zero_iff.mpr (zpow_ne_zero _ ht)
  have hz : ‖torusCoordinates x i.castSucc‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (torusCoordinates_nonzero hx _)
  simp only [logCoordinates, logNorm, torusCoordinates_twistedTranslate_apply C v hx, norm_mul]
  rw [Real.log_mul (mul_ne_zero hu hp) hz, Real.log_mul hu hp,
    exponentialMultiplier_log_norm, norm_zpow, Real.log_zpow]
  ring

/-- The rescaled position in §4.4, defined on torus points with `|t| ≠ 1`. -/
def position (x : Space) : Fin 2 → ℝ := fun i => logCoordinates x i.castSucc / Real.log ‖time x‖

theorem position_twistedTranslate (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) {x : Space} (hx : x ∈ openTorus) (ht : Real.log ‖time x‖ ≠ 0)
    (i : Fin 2) : position (twistedTranslate C v x) i = position x i +
      (cuspVector v i : ℝ) +
      (driftMatrix C (time x) *ᵥ (fun j => (v j : ℝ))) i / Real.log ‖time x‖ := by
  simp only [position, time_twistedTranslate, logCoordinates_twistedTranslate C v hx]
  field_simp

end Wikipedia.HopfProblem.ToricSpace
