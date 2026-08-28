import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFrameSmooth
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationHolomorphicFrameCalculus

/-!
# The actual closed antiholomorphic form of the constructed smooth frame

In an original scalar chart the coefficient is `(∂̄sᵢ) / sᵢ`. The proved
transition law of the constructed frame and the actual holomorphicity of the
given transitions show that these quotients agree. Their chart-selected
values are therefore genuinely smooth global functions, and actual mixed
derivatives prove the closedness needed by the global integral solver.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationHolomorphicFrame

open HolomorphicCharacterBundle PeriodTorusLineBundleClassification
  PeriodTorusLineBundleClassificationFrame
  PeriodTorusLineBundleClassificationConnection

local notation "Iℂ" => modelWithCornersSelf ℂ ComplexPlane₂

variable {ι : Type*} (A : TransitionData ComplexPlane₂ ι)

/-- The literal logarithmic antiholomorphic derivative of a constructed
smooth-frame coefficient in a fixed original chart. -/
def localForcing (i : ι) (k : Fin 2) (x : ComplexPlane₂) : ℂ :=
  dbarCoordinate (frameCoefficient A i) k x / frameCoefficient A i x

/-- Chart selection takes the derivative with the chart fixed. Its actual
independence of the chosen chart is proved below. -/
def forcingCoefficient (k : Fin 2) (x : ComplexPlane₂) : ℂ :=
  localForcing A (A.indexAt x) k x

variable [A.IsHolomorphic Iℂ]

theorem transition_complex_differentiableAt (i j : ι) {x : ComplexPlane₂}
    (hx : x ∈ A.baseSet i ∩ A.baseSet j) :
    DifferentiableAt ℂ (fun y => (A.transition i j y : ℂ)) x :=
  ((A.transition_holomorphic Iℂ i j).contDiffOn.contDiffAt
    (((A.isOpen_baseSet i).inter (A.isOpen_baseSet j)).mem_nhds hx)).differentiableAt
      (by simp)

/-- Differentiate the actual coefficient transition relation on its open
overlap; the derivative of the holomorphic transition vanishes. -/
theorem frameCoefficient_dbar_change (i j : ι) (k : Fin 2) {x : ComplexPlane₂}
    (hi : x ∈ A.baseSet i) (hj : x ∈ A.baseSet j) :
    dbarCoordinate (frameCoefficient A j) k x =
      (A.transition i j x : ℂ) * dbarCoordinate (frameCoefficient A i) k x := by
  have he : frameCoefficient A j =ᶠ[𝓝 x]
      (fun y => (A.transition i j y : ℂ) * frameCoefficient A i y) := by
    filter_upwards [((A.isOpen_baseSet i).inter (A.isOpen_baseSet j)).mem_nhds ⟨hi, hj⟩]
      with y hy
    exact (frameCoefficient_compatible A i j y hy).symm
  have hd := dbarCoordinate_congr he k
  have hg := transition_complex_differentiableAt A i j ⟨hi, hj⟩
  rw [dbarCoordinate_mul (hg.restrictScalars ℝ)
    ((frameCoefficient_contDiffAt A i x hi).differentiableAt (by simp)),
    dbarCoordinate_zero_of_differentiableAt hg k, mul_zero, add_zero] at hd
  exact hd

/-- The literal logarithmic derivatives agree in any two original charts. -/
theorem localForcing_eq (i j : ι) (k : Fin 2) {x : ComplexPlane₂}
    (hi : x ∈ A.baseSet i) (hj : x ∈ A.baseSet j) :
    localForcing A i k x = localForcing A j k x := by
  apply (div_eq_div_iff (frameCoefficient_ne_zero A i x)
    (frameCoefficient_ne_zero A j x)).mpr
  rw [frameCoefficient_dbar_change A i j k hi hj,
    ← frameCoefficient_compatible A i j x ⟨hi, hj⟩]
  ring

theorem forcingCoefficient_eq (i : ι) (k : Fin 2) {x : ComplexPlane₂}
    (hx : x ∈ A.baseSet i) : forcingCoefficient A k x = localForcing A i k x :=
  localForcing_eq A (A.indexAt x) i k (A.mem_baseSet_at x) hx

theorem forcingCoefficient_eventuallyEq (i : ι) (k : Fin 2) {x : ComplexPlane₂}
    (hx : x ∈ A.baseSet i) : forcingCoefficient A k =ᶠ[𝓝 x] localForcing A i k := by
  filter_upwards [(A.isOpen_baseSet i).mem_nhds hx] with y hy
  exact forcingCoefficient_eq A i k hy

theorem localForcing_contDiffAt (i : ι) (k : Fin 2) {x : ComplexPlane₂}
    (hx : x ∈ A.baseSet i) : ContDiffAt ℝ ∞ (localForcing A i k) x :=
  contDiffAt_logarithmicDbar (frameCoefficient_contDiffAt A i x hx)
    (frameCoefficient_ne_zero A i x) k

/-- The actual chart-selected coefficient is globally smooth; no regularity
of the preferred chart-index function is required. -/
theorem forcingCoefficient_contDiff (k : Fin 2) :
    ContDiff ℝ ∞ (forcingCoefficient A k) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  exact (localForcing_contDiffAt A (A.indexAt x) k (A.mem_baseSet_at x)).congr_of_eventuallyEq
    (forcingCoefficient_eventuallyEq A (A.indexAt x) k (A.mem_baseSet_at x))

/-- Closedness follows from the actual local logarithmic derivative and the
real Schwarz identity, rather than a supplied integrability hypothesis. -/
theorem forcingCoefficient_closed (x : ComplexPlane₂) :
    dbarCoordinate (forcingCoefficient A 1) 0 x =
      dbarCoordinate (forcingCoefficient A 0) 1 x := by
  rw [dbarCoordinate_congr
      (forcingCoefficient_eventuallyEq A (A.indexAt x) 1 (A.mem_baseSet_at x)) 0,
    dbarCoordinate_congr
      (forcingCoefficient_eventuallyEq A (A.indexAt x) 0 (A.mem_baseSet_at x)) 1]
  exact dbar_logarithmic_closed
    (frameCoefficient_contDiffAt A (A.indexAt x) x (A.mem_baseSet_at x))
    (frameCoefficient_ne_zero A (A.indexAt x) x)

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationHolomorphicFrame
