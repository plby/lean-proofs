import Wikipedia.HopfProblem.OrbitPairSpherePathEnergy
import Wikipedia.NoExoticSixSphere.SmoothSphereRotation

/-!
# Smooth transport of sphere geodesics by actual rotations

The local rotation and its actual inverse are smooth wherever their two
reflection normals are nonzero. Orthogonal transport preserves the integral
energy, not just endpoint distances. These facts allow the local logarithm
at a fixed basepoint to describe segments with both endpoints varying.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HopfProblem.OrbitPair.SphereGeodesicTransport

open NoExoticSixSphere

variable {E B : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

theorem contDiffAt_reflection {v z : B → E} {p : B}
    (hv : ContDiffAt ℝ ∞ v p) (hz : ContDiffAt ℝ ∞ z p) (hn : v p ≠ 0) :
    ContDiffAt ℝ ∞ (fun q => hyperplaneReflectionOperator (v q) (z q)) p := by
  have hnorm : ContDiffAt ℝ ∞ (fun q => ‖v q‖ ^ 2) p := hv.norm_sq (𝕜 := ℝ)
  have hinv := hnorm.inv (pow_ne_zero 2 (norm_ne_zero_iff.mpr hn))
  have hi : ContDiffAt ℝ ∞ (fun q => inner ℝ (v q) (z q)) p := hv.inner ℝ hz
  have h : ContDiffAt ℝ ∞ (fun q =>
      z q - (2 * (‖v q‖ ^ 2)⁻¹ * inner ℝ (v q) (z q)) • v q) p :=
    hz.sub (((contDiffAt_const.mul hinv).mul hi).smul hv)
  simpa only [hyperplaneReflectionOperator_apply] using! h

def forward (x a z : E) : E := localRotationEquiv x a z

def backward (x a z : E) : E := (localRotationEquiv x a).symm z

theorem forward_formula (x a z : E) :
    forward x a z = hyperplaneReflectionOperator a (hyperplaneReflectionOperator (x + a) z) := rfl

theorem backward_formula (x a z : E) :
    backward x a z = hyperplaneReflectionOperator (x + a) (hyperplaneReflectionOperator a z) := rfl

theorem forward_backward (x a z : E) : forward x a (backward x a z) = z :=
  (localRotationEquiv x a).apply_symm_apply z

theorem backward_forward (x a z : E) : backward x a (forward x a z) = z :=
  (localRotationEquiv x a).symm_apply_apply z

theorem norm_forward (x a z : E) : ‖forward x a z‖ = ‖z‖ :=
  (localRotationEquiv x a).norm_map z

theorem norm_backward (x a z : E) : ‖backward x a z‖ = ‖z‖ :=
  (localRotationEquiv x a).symm.norm_map z

theorem forward_self (x z : E) : forward x x z = z := by
  change localRotationOperator x x z = z
  rw [localRotationOperator_self]
  rfl

theorem backward_self (x z : E) : backward x x z = z := by
  have h := forward_backward x x z
  rwa [forward_self] at h

theorem forward_base {x a : E} (hx : ‖x‖ = 1) (ha : ‖a‖ = 1) : forward x a x = a := by
  let x' : UnitSphere E := ⟨x, by simpa only [Metric.mem_sphere, dist_zero_right] using hx⟩
  let a' : UnitSphere E := ⟨a, by simpa only [Metric.mem_sphere, dist_zero_right] using ha⟩
  exact localRotationEquiv_apply x' a'

theorem backward_base {x a : E} (hx : ‖x‖ = 1) (ha : ‖a‖ = 1) : backward x a a = x := by
  have h := backward_forward x a x
  rwa [forward_base hx ha] at h

theorem contDiffAt_forward {x a z : B → E} {p : B}
    (hx : ContDiffAt ℝ ∞ x p) (ha : ContDiffAt ℝ ∞ a p) (hz : ContDiffAt ℝ ∞ z p)
    (hne : a p ≠ 0) (hsum : x p + a p ≠ 0) :
    ContDiffAt ℝ ∞ (fun q => forward (x q) (a q) (z q)) p :=
  contDiffAt_reflection ha (contDiffAt_reflection (hx.add ha) hz hsum) hne

theorem contDiffAt_backward {x a z : B → E} {p : B}
    (hx : ContDiffAt ℝ ∞ x p) (ha : ContDiffAt ℝ ∞ a p) (hz : ContDiffAt ℝ ∞ z p)
    (hne : a p ≠ 0) (hsum : x p + a p ≠ 0) :
    ContDiffAt ℝ ∞ (fun q => backward (x q) (a q) (z q)) p :=
  contDiffAt_reflection (hx.add ha) (contDiffAt_reflection ha hz hne) hsum

theorem energy_isometry (e : E ≃ₗᵢ[ℝ] E) {γ : ℝ → E} (hγ : ContDiff ℝ ∞ γ) (l u : ℝ) :
    SpherePathEnergy.energy (fun t => e (γ t)) l u = SpherePathEnergy.energy γ l u := by
  have hd (t : ℝ) : HasDerivAt (fun r => e (γ r)) (e (deriv γ t)) t :=
    e.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
      (((hγ.differentiable (by simp)) t).hasDerivAt)
  unfold SpherePathEnergy.energy
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [(hd t).deriv, e.norm_map]

theorem energy_forward (x a : E) {γ : ℝ → E} (hγ : ContDiff ℝ ∞ γ) (l u : ℝ) :
    SpherePathEnergy.energy (fun t => forward x a (γ t)) l u = SpherePathEnergy.energy γ l u :=
  energy_isometry (localRotationEquiv x a) hγ l u

theorem energy_backward (x a : E) {γ : ℝ → E} (hγ : ContDiff ℝ ∞ γ) (l u : ℝ) :
    SpherePathEnergy.energy (fun t => backward x a (γ t)) l u = SpherePathEnergy.energy γ l u :=
  energy_isometry (localRotationEquiv x a).symm hγ l u

end Wikipedia.HopfProblem.OrbitPair.SphereGeodesicTransport
