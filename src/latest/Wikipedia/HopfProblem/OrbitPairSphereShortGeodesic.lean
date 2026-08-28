import Wikipedia.HopfProblem.OrbitPairSphereTangentExponential
import Wikipedia.NoExoticSixSphere.SphereCurveDistance

/-!
# Short sphere geodesics minimize the actual path energy

The rank-two exponential has energy equal to its squared initial speed.
For sufficiently small tangent vectors this equals the squared endpoint
angle, including the zero tangent vector. Rescaling time gives the usual
angle-squared divided by interval-length formula. The previously proved
endpoint-angle inequality compares it with every smooth unit-valued path
having the same endpoints.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HopfProblem.OrbitPair.SphereTangentExponential

open NoExoticSixSphere GLOrthonormalization CayleyTransform OrthogonalExponential

variable {n : ℕ}

theorem endpoint_angle_sq {x : Vector n} (hx : ‖x‖ = 1) (v : Tangent x)
    (hv : ‖v‖ ≤ Real.pi / 2) :
    Real.arccos (inner ℝ x (curve x v 1)) ^ 2 = ‖v‖ ^ 2 := by
  have hK : ‖(generator x v : Vector n →L[ℝ] Vector n)‖ ≤ Real.pi :=
    (norm_generator_le hx v).trans (by linarith)
  simpa only [curve, one_smul] using!
    SkewShortExponential.eigenvector_endpoint_angle_sq (generator x v) hK hx (gram_base hx v)

def segment (x : Vector n) (v : Tangent x) (l u t : ℝ) : Vector n :=
  curve x v ((t - l) / (u - l))

theorem segment_start (x : Vector n) (v : Tangent x) (l u : ℝ) : segment x v l u l = x := by
  rw [segment, sub_self, zero_div, curve_zero]

theorem segment_end (x : Vector n) (v : Tangent x) {l u : ℝ} (hlu : l ≠ u) :
    segment x v l u u = curve x v 1 := by
  rw [segment, div_self (sub_ne_zero.mpr hlu.symm)]

theorem contDiff_segment_family (x : Vector n) (l u : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × Tangent x => segment x p.2 l u p.1) :=
  (contDiff_family x).comp
    (((contDiff_fst.sub contDiff_const).div_const (u - l)).prodMk contDiff_snd)

theorem contDiff_segment (x : Vector n) (v : Tangent x) (l u : ℝ) :
    ContDiff ℝ ∞ (segment x v l u) :=
  (contDiff_segment_family x l u).comp (contDiff_id.prodMk contDiff_const)

theorem norm_segment {x : Vector n} (hx : ‖x‖ = 1) (v : Tangent x) (l u t : ℝ) :
    ‖segment x v l u t‖ = 1 := norm_curve hx v _

theorem hasDerivAt_segment {x : Vector n} (hx : ‖x‖ = 1) (v : Tangent x) (l u t : ℝ) :
    HasDerivAt (segment x v l u)
      ((1 / (u - l)) • (exp (((t - l) / (u - l)) • generator x v)).1.1 (v : Vector n)) t := by
  have ht : HasDerivAt (fun r : ℝ => (r - l) / (u - l)) (1 / (u - l)) t :=
    ((hasDerivAt_id t).sub_const l).div_const (u - l)
  exact HasDerivAt.scomp t (hasDerivAt_curve hx v ((t - l) / (u - l))) ht

theorem speed_sq_segment {x : Vector n} (hx : ‖x‖ = 1) (v : Tangent x) (l u t : ℝ) :
    ‖deriv (segment x v l u) t‖ ^ 2 = (1 / (u - l)) ^ 2 * ‖v‖ ^ 2 := by
  rw [(hasDerivAt_segment hx v l u t).deriv, norm_smul,
    (exp (((t - l) / (u - l)) • generator x v)).property,
    mul_pow, Real.norm_eq_abs, sq_abs]
  rfl

theorem energy_segment {x : Vector n} (hx : ‖x‖ = 1) (v : Tangent x) (l u : ℝ) :
    SpherePathEnergy.energy (segment x v l u) l u = ‖v‖ ^ 2 / (u - l) := by
  unfold SpherePathEnergy.energy
  simp only [speed_sq_segment hx, intervalIntegral.integral_const, smul_eq_mul]
  by_cases h : u - l = 0
  · simp [h]
  · field_simp

theorem short_segment_energy_le {γ : ℝ → Vector n} (hγ : ContDiff ℝ ∞ γ)
    (hunit : ∀ t, ‖γ t‖ = 1) {x : Vector n} (hx : ‖x‖ = 1)
    (v : Tangent x) (hv : ‖v‖ ≤ Real.pi / 2) {l u : ℝ} (hlu : l < u)
    (hl : γ l = x) (hu : γ u = curve x v 1) :
    SpherePathEnergy.energy (segment x v l u) l u ≤ SpherePathEnergy.energy γ l u := by
  have h := SphereCurveAngle.endpoint_angle_sq_le_energy hγ hunit hlu
  rw [hl, hu, endpoint_angle_sq hx v hv] at h
  rw [energy_segment hx]
  apply (div_le_iff₀ (sub_pos.mpr hlu)).mpr
  simpa only [SpherePathEnergy.energy, mul_comm] using h

end Wikipedia.HopfProblem.OrbitPair.SphereTangentExponential
