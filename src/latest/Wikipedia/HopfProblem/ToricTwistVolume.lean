import Wikipedia.HopfProblem.ToricTwists
import Wikipedia.HopfProblem.ToricTwistDeterminant
import Wikipedia.HopfProblem.ToricMonomialDerivative

/-!
# The Jacobian of a parameter-dependent toric multiplier

The dependence of the multipliers on the cusp parameter contributes a
rank-one term to the derivative.  Differentiating the product-one relation
shows that this term has zero contribution to the determinant.
-/

noncomputable section

open Set Topology
open scoped ContDiff Matrix

namespace Wikipedia.HopfProblem.ToricFan.Triangle

@[simp] theorem rays_det_shift (s : Triangle) (v : Fin 2 → ℤ) :
    (s.shift v).rays.det = s.rays.det := by
  simp only [rays_det]
  rfl

end Wikipedia.HopfProblem.ToricFan.Triangle

namespace Wikipedia.HopfProblem.ToricSpace

open ToricCharts ToricFan

theorem time_fderiv_single (z : CoordinateSpace 3) (j : Fin 3) :
    fderiv ℂ Triangle.time z (Pi.single j 1) =
      (![z 1 * z 2, z 0 * z 2, z 0 * z 1] : CoordinateSpace 3) j := by
  have h := ((hasFDerivAt_apply (𝕜 := ℂ) 0 z).mul
    (hasFDerivAt_apply (𝕜 := ℂ) 1 z)).mul (hasFDerivAt_apply (𝕜 := ℂ) 2 z)
  change HasFDerivAt (fun w : CoordinateSpace 3 => w 0 * w 1 * w 2) _ z at h
  change fderiv ℂ (fun w : CoordinateSpace 3 => w 0 * w 1 * w 2) z (Pi.single j 1) = _
  rw [h.fderiv]
  fin_cases j <;> simp <;> ring

def productTimeScale (a : ℂ → CoordinateSpace 3) (z : CoordinateSpace 3) : CoordinateSpace 3 :=
  a (Triangle.time z) * z

theorem productTimeScale_fderiv_entry (a : ℂ → CoordinateSpace 3) (z : CoordinateSpace 3)
    (ha : ∀ i, DifferentiableAt ℂ (fun t => a t i) (Triangle.time z)) (i j : Fin 3) :
    fderiv ℂ (productTimeScale a) z (Pi.single j 1) i =
      (if i = j then a (Triangle.time z) i else 0) +
      (deriv (fun t => a t i) (Triangle.time z) * z i) *
        (![z 1 * z 2, z 0 * z 2, z 0 * z 1] : CoordinateSpace 3) j := by
  have ht : DifferentiableAt ℂ Triangle.time z :=
    Triangle.time_holomorphic.differentiable (by simp) z
  have hc k := ((ha k).hasDerivAt.comp_hasFDerivAt z ht.hasFDerivAt).mul
    (hasFDerivAt_apply (𝕜 := ℂ) k z)
  have hf := hasFDerivAt_pi.mpr hc
  change HasFDerivAt (fun w : CoordinateSpace 3 => fun k => a (Triangle.time w) k * w k)
    _ z at hf
  change fderiv ℂ (fun w : CoordinateSpace 3 => fun k => a (Triangle.time w) k * w k)
    z (Pi.single j 1) i = _
  rw [hf.fderiv]
  simp only [ContinuousLinearMap.pi_apply, add_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [time_fderiv_single]
  by_cases hij : i = j
  · subst j
    simp
    ring
  · simp [hij]
    ring

theorem product_one_deriv_relation (a : ℂ → CoordinateSpace 3) (t : ℂ)
    (ha : ∀ i, DifferentiableAt ℂ (fun r => a r i) t)
    (hprod : ∀ r, a r 0 * a r 1 * a r 2 = 1) :
    deriv (fun r => a r 0) t * a t 1 * a t 2 +
      a t 0 * deriv (fun r => a r 1) t * a t 2 +
      a t 0 * a t 1 * deriv (fun r => a r 2) t = 0 := by
  have h := ((ha 0).hasDerivAt.mul (ha 1).hasDerivAt).mul (ha 2).hasDerivAt
  change HasDerivAt (fun r => a r 0 * a r 1 * a r 2) _ t at h
  have he : (fun r => a r 0 * a r 1 * a r 2) = (fun _ : ℂ => 1) := funext hprod
  rw [he] at h
  have hzero := h.unique (hasDerivAt_const t 1)
  calc
    _ = (deriv (fun r => a r 0) t * a t 1 + a t 0 * deriv (fun r => a r 1) t) *
      a t 2 + (a t 0 * a t 1) * deriv (fun r => a r 2) t := by ring
    _ = 0 := hzero

/-- The product-one condition cancels the rank-one correction to the
Jacobian.  The formula holds also when some coordinates of `z` vanish. -/
theorem productTimeScale_det_fderiv (a : ℂ → CoordinateSpace 3) (z : CoordinateSpace 3)
    (ha : ∀ i, DifferentiableAt ℂ (fun t => a t i) (Triangle.time z))
    (hprod : ∀ t, a t 0 * a t 1 * a t 2 = 1) :
    (jacobianMatrix (productTimeScale a) z).det = 1 := by
  have hm : jacobianMatrix (productTimeScale a) z = Matrix.of (fun i j =>
      (if i = j then a (Triangle.time z) i else 0) +
      (deriv (fun t => a t i) (Triangle.time z) * z i) *
        (![z 1 * z 2, z 0 * z 2, z 0 * z 1] : CoordinateSpace 3) j) := by
    ext i j
    exact productTimeScale_fderiv_entry a z ha i j
  rw [hm, det_diagonal_add_timeGradient]
  rw [product_one_deriv_relation a (Triangle.time z) ha hprod,
    hprod (Triangle.time z), mul_zero, add_zero]

theorem varying_factors_holomorphic (s : Triangle) (u : ℂ → Fin 2 → ℂˣ) {D : Set ℂ}
    (hu : ∀ j, ContDiffOn ℂ ω (fun t => (u t j : ℂ)) D) :
    ContDiffOn ℂ ω (fun t => factors s (fibreMultiplier (u t))) D := by
  have hval : ContDiffOn ℂ ω
      (fun t => fun j => (fibreMultiplier (u t) j : ℂ)) D := by
    apply contDiffOn_pi.mpr
    intro j
    fin_cases j
    · exact hu 0
    · exact hu 1
    · exact contDiffOn_const
  exact (monomial_contDiffOn s.dual ω).comp hval
    (fun t _ => torus_subset_domain _ (fun j => (fibreMultiplier (u t) j).ne_zero))

/-- The actual parameter-dependent chart map preserves coordinate volume:
its complex Jacobian determinant is one throughout the open parameter set,
including on the central fibre. -/
theorem varying_scale_det_fderiv (s : Triangle) (u : ℂ → Fin 2 → ℂˣ) {D : Set ℂ}
    (hD : IsOpen D) (hu : ∀ j, ContDiffOn ℂ ω (fun t => (u t j : ℂ)) D)
    {z : CoordinateSpace 3} (hz : Triangle.time z ∈ D) :
    (jacobianMatrix (fun w => scale s (fibreMultiplier (u (Triangle.time w))) w) z).det = 1 := by
  apply productTimeScale_det_fderiv (fun t => factors s (fibreMultiplier (u t))) z
  · have hf := (varying_factors_holomorphic s u hu).contDiffAt (hD.mem_nhds hz)
    exact differentiableAt_pi.mp (hf.differentiableAt (by simp))
  · intro t
    have h := time_factors s (fibreMultiplier (u t))
    simpa [Triangle.time, fibreMultiplier] using h

theorem twistedTranslate_chart_formula (s : Triangle)
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ) (z : CoordinateSpace 3) :
    twistedTranslate C v (inclusion s z) = inclusion (s.shift (cuspVector v))
      (scale (s.shift (cuspVector v))
        (fibreMultiplier (exponentialMultiplier C v (Triangle.time z))) z) := by
  rw [twistedTranslate, translate_inclusion, variableMultiplier_inclusion]

/-- Reading the actual twisted action in the translated ambient chart gives
precisely the parameter-dependent scaling map, on the whole source chart. -/
theorem twistedTranslate_in_coordinates (s : Triangle)
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ) (z : CoordinateSpace 3) :
    (parametrization (s.shift (cuspVector v))).symm
      (twistedTranslate C v (inclusion s z)) =
      scale (s.shift (cuspVector v))
        (fibreMultiplier (exponentialMultiplier C v (Triangle.time z))) z := by
  rw [twistedTranslate_chart_formula]
  exact (parametrization (s.shift (cuspVector v))).left_inv (mem_univ _)

/-- The multipliers in the twisted lattice action preserve chart volume
even though the period matrix varies with the cusp parameter. -/
theorem twistedTranslate_chart_det_fderiv (s : Triangle)
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ) {D : Set ℂ}
    (hD : IsOpen D) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) D)
    {z : CoordinateSpace 3} (hz : Triangle.time z ∈ D) :
    (jacobianMatrix (fun w => scale (s.shift (cuspVector v))
      (fibreMultiplier (exponentialMultiplier C v (Triangle.time w))) w) z).det = 1 :=
  varying_scale_det_fderiv (s.shift (cuspVector v)) (exponentialMultiplier C v)
    hD (exponentialMultiplier_holomorphic C v hC) hz

/-- The signs of the source and translated target charts agree.  Together
with the actual Jacobian formula this is the signed-volume invariance
identity for the varying twisted action. -/
theorem twistedTranslate_chart_signed_volume (s : Triangle)
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ) {D : Set ℂ}
    (hD : IsOpen D) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) D)
    {z : CoordinateSpace 3} (hz : Triangle.time z ∈ D) :
    ((s.shift (cuspVector v)).rays.det : ℂ) *
      (jacobianMatrix (fun w => scale (s.shift (cuspVector v))
        (fibreMultiplier (exponentialMultiplier C v (Triangle.time w))) w) z).det =
      (s.rays.det : ℂ) := by
  rw [twistedTranslate_chart_det_fderiv s C v hD hC hz, Triangle.rays_det_shift, mul_one]

/-- The determinant formula for the actual action composed with the source
parametrization and the target chart, with no independently specified map. -/
theorem twistedTranslate_in_coordinates_det_fderiv (s : Triangle)
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ) {D : Set ℂ}
    (hD : IsOpen D) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) D)
    {z : CoordinateSpace 3} (hz : Triangle.time z ∈ D) :
    (jacobianMatrix (fun w => (parametrization (s.shift (cuspVector v))).symm
      (twistedTranslate C v (inclusion s w))) z).det = 1 := by
  simpa only [twistedTranslate_in_coordinates] using
    twistedTranslate_chart_det_fderiv s C v hD hC hz

theorem twistedTranslate_in_coordinates_signed_volume (s : Triangle)
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ) {D : Set ℂ}
    (hD : IsOpen D) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) D)
    {z : CoordinateSpace 3} (hz : Triangle.time z ∈ D) :
    ((s.shift (cuspVector v)).rays.det : ℂ) *
      (jacobianMatrix (fun w => (parametrization (s.shift (cuspVector v))).symm
        (twistedTranslate C v (inclusion s w))) z).det = (s.rays.det : ℂ) := by
  rw [twistedTranslate_in_coordinates_det_fderiv s C v hD hC hz,
    Triangle.rays_det_shift, mul_one]

end Wikipedia.HopfProblem.ToricSpace
