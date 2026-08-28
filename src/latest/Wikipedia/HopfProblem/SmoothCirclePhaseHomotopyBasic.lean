import Wikipedia.HopfProblem.SmoothCirclePhaseHomotopySegment
import Mathlib.Analysis.Complex.Circle
import Mathlib.Topology.Homotopy.Basic

/-!
# The explicit unit-phase homotopy

For continuous complex functions `f` and `g`, with `f` unit-valued and `g`
within distance one half, normalize their literal straight-line segment.
The segment is bounded away from zero, so this gives a continuous homotopy
through unit values. Both the ambient homotopy and the homotopy with values
in Mathlib's actual complex unit circle retain this same formula.

Only the given topology is used on the source. No smoothness is asserted.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SmoothCirclePhaseHomotopy

variable {M : Type*}

/-- The prescribed normalized straight-line formula, without a homotopy-choice operation. -/
def phase (f g : M → ℂ) (t : unitInterval) (x : M) : ℂ :=
  SmoothCircleApproximation.normalize (segment f g t x)

@[simp] theorem phase_zero (f g : M → ℂ) (hunit : ∀ x, ‖f x‖ = 1) (x : M) :
    phase f g 0 x = f x := by
  rw [phase, segment_zero, SmoothCircleApproximation.normalize_eq_self (hunit x)]

@[simp] theorem phase_one (f g : M → ℂ) (x : M) :
    phase f g 1 x = SmoothCircleApproximation.normalize (g x) := by
  rw [phase, segment_one]

/-- Every intermediate phase has norm exactly one. -/
theorem norm_phase (f g : M → ℂ) (hunit : ∀ x, ‖f x‖ = 1)
    (hclose : ∀ x, dist (g x) (f x) ≤ (1 / 2 : ℝ)) (t : unitInterval) (x : M) :
    ‖phase f g t x‖ = 1 :=
  SmoothCircleApproximation.norm_normalize (segment_ne_zero f g hunit hclose t x)

/-- The closeness hypothesis itself supplies the nonvanishing of the endpoint `g`. -/
theorem close_right_ne_zero (f g : M → ℂ) (hunit : ∀ x, ‖f x‖ = 1)
    (hclose : ∀ x, dist (g x) (f x) ≤ (1 / 2 : ℝ)) (x : M) : g x ≠ 0 := by
  simpa only [segment_one] using segment_ne_zero f g hunit hclose 1 x

variable [TopologicalSpace M]

/-- Radial normalization is continuous along every continuous nonzero map. -/
theorem continuous_normalize_comp (f : M → ℂ) (hf : Continuous f)
    (hne : ∀ x, f x ≠ 0) : Continuous (fun x => SmoothCircleApproximation.normalize (f x)) := by
  change Continuous (fun x => ‖f x‖⁻¹ • f x)
  exact (hf.norm.inv₀ (fun x => norm_ne_zero_iff.mpr (hne x))).smul hf

/-- The original complex map, radially normalized at each point. -/
def normalizedMap (g : M → ℂ) (hg : Continuous g) (hne : ∀ x, g x ≠ 0) : C(M, ℂ) :=
  ⟨fun x => SmoothCircleApproximation.normalize (g x), continuous_normalize_comp g hg hne⟩

@[simp] theorem normalizedMap_apply (g : M → ℂ) (hg : Continuous g)
    (hne : ∀ x, g x ≠ 0) (x : M) :
    normalizedMap g hg hne x = SmoothCircleApproximation.normalize (g x) := rfl

/-- A continuous unit-valued function as a map into the native complex circle. -/
def unitCircleMap (f : M → ℂ) (hf : Continuous f) (hunit : ∀ x, ‖f x‖ = 1) :
    C(M, _root_.Circle) where
  toFun x := ⟨f x, mem_sphere_zero_iff_norm.mpr (hunit x)⟩
  continuous_toFun := hf.subtype_mk _

@[simp] theorem unitCircleMap_coe (f : M → ℂ) (hf : Continuous f)
    (hunit : ∀ x, ‖f x‖ = 1) (x : M) : (unitCircleMap f hf hunit x : ℂ) = f x := rfl

/-- Normalization as an actual continuous map into Mathlib's unit circle. -/
def normalizedCircleMap (g : M → ℂ) (hg : Continuous g) (hne : ∀ x, g x ≠ 0) :
    C(M, _root_.Circle) :=
  unitCircleMap (fun x => SmoothCircleApproximation.normalize (g x))
    (continuous_normalize_comp g hg hne)
    (fun x => SmoothCircleApproximation.norm_normalize (hne x))

@[simp] theorem normalizedCircleMap_coe (g : M → ℂ) (hg : Continuous g)
    (hne : ∀ x, g x ≠ 0) (x : M) :
    (normalizedCircleMap g hg hne x : ℂ) = SmoothCircleApproximation.normalize (g x) := rfl

/-- Literal joint continuity in the native interval parameter and the original source. -/
theorem continuous_phase (f g : M → ℂ) (hf : Continuous f) (hg : Continuous g)
    (hunit : ∀ x, ‖f x‖ = 1) (hclose : ∀ x, dist (g x) (f x) ≤ (1 / 2 : ℝ)) :
    Continuous (fun p : unitInterval × M => phase f g p.1 p.2) :=
  continuous_normalize_comp _ (continuous_segment f g hf hg)
    (fun p => segment_ne_zero f g hunit hclose p.1 p.2)

/-- The actual ambient homotopy, with the original function as its starting map. -/
def ambientHomotopy (f g : M → ℂ) (hf : Continuous f) (hg : Continuous g)
    (hunit : ∀ x, ‖f x‖ = 1) (hclose : ∀ x, dist (g x) (f x) ≤ (1 / 2 : ℝ)) :
    ContinuousMap.Homotopy ⟨f, hf⟩
      (normalizedMap g hg (close_right_ne_zero f g hunit hclose)) where
  toFun p := phase f g p.1 p.2
  continuous_toFun := continuous_phase f g hf hg hunit hclose
  map_zero_left := phase_zero f g hunit
  map_one_left := phase_one f g

@[simp] theorem ambientHomotopy_apply (f g : M → ℂ) (hf : Continuous f) (hg : Continuous g)
    (hunit : ∀ x, ‖f x‖ = 1) (hclose : ∀ x, dist (g x) (f x) ≤ (1 / 2 : ℝ))
    (t : unitInterval) (x : M) :
    ambientHomotopy f g hf hg hunit hclose (t, x) =
      SmoothCircleApproximation.normalize ((1 - (t : ℝ)) • f x + (t : ℝ) • g x) := rfl

theorem norm_ambientHomotopy (f g : M → ℂ) (hf : Continuous f) (hg : Continuous g)
    (hunit : ∀ x, ‖f x‖ = 1) (hclose : ∀ x, dist (g x) (f x) ≤ (1 / 2 : ℝ))
    (t : unitInterval) (x : M) : ‖ambientHomotopy f g hf hg hunit hclose (t, x)‖ = 1 :=
  norm_phase f g hunit hclose t x

/-- The same explicit homotopy with values in the native complex unit-circle subtype. -/
def circleHomotopy (f g : M → ℂ) (hf : Continuous f) (hg : Continuous g)
    (hunit : ∀ x, ‖f x‖ = 1) (hclose : ∀ x, dist (g x) (f x) ≤ (1 / 2 : ℝ)) :
    ContinuousMap.Homotopy (unitCircleMap f hf hunit)
      (normalizedCircleMap g hg (close_right_ne_zero f g hunit hclose)) where
  toFun p := ⟨phase f g p.1 p.2,
    mem_sphere_zero_iff_norm.mpr (norm_phase f g hunit hclose p.1 p.2)⟩
  continuous_toFun := (continuous_phase f g hf hg hunit hclose).subtype_mk _
  map_zero_left x := _root_.Circle.ext (phase_zero f g hunit x)
  map_one_left x := _root_.Circle.ext (phase_one f g x)

@[simp] theorem circleHomotopy_coe (f g : M → ℂ) (hf : Continuous f) (hg : Continuous g)
    (hunit : ∀ x, ‖f x‖ = 1) (hclose : ∀ x, dist (g x) (f x) ≤ (1 / 2 : ℝ))
    (t : unitInterval) (x : M) :
    (circleHomotopy f g hf hg hunit hclose (t, x) : ℂ) =
      SmoothCircleApproximation.normalize ((1 - (t : ℝ)) • f x + (t : ℝ) • g x) := rfl

end Wikipedia.HopfProblem.SmoothCirclePhaseHomotopy
