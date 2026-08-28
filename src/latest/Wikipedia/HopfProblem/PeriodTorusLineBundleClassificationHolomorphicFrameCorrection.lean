import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationHolomorphicFrameForcing
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationGlobalDbar

/-!
# A genuinely solved global correction of the constructed smooth frame

The unrestricted global integral solver supplies a smooth primitive of the
actual closed forcing form. Multiplication by its negative exponential
preserves nonvanishing and the original transitions, and its antiholomorphic
derivatives cancel exactly. The two-variable Cauchy--Riemann theorem then
gives actual holomorphic local coefficients.
-/

noncomputable section

open Set
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationHolomorphicFrame

open HolomorphicCharacterBundle PeriodTorusLineBundleClassification
  PeriodTorusLineBundleClassificationFrame

local notation "Iℂ" => modelWithCornersSelf ℂ ComplexPlane₂

variable {ι : Type*} (A : TransitionData ComplexPlane₂ ι) [A.IsHolomorphic Iℂ]

/-- The actual globally smooth closed forcing form has a genuine global
primitive by the proved integral/exhaustion theorem. -/
theorem exists_frame_primitive :
    ∃ u : ComplexPlane₂ → ℂ, ContDiff ℝ ∞ u ∧
      ∀ k x, dbarCoordinate u k x = forcingCoefficient A k x := by
  obtain ⟨u, hu, h0, h1⟩ := exists_smooth_global_dbar_primitive_cover
    (forcingCoefficient_contDiff A 0) (forcingCoefficient_contDiff A 1)
    (forcingCoefficient_closed A)
  refine ⟨u, hu, ?_⟩
  intro k x
  fin_cases k
  · exact h0 x
  · exact h1 x

/-- A choice of the genuinely proved global primitive. -/
def framePrimitive : ComplexPlane₂ → ℂ := (exists_frame_primitive A).choose

theorem framePrimitive_contDiff : ContDiff ℝ ∞ (framePrimitive A) :=
  (exists_frame_primitive A).choose_spec.1

theorem framePrimitive_dbar (k : Fin 2) (x : ComplexPlane₂) :
    dbarCoordinate (framePrimitive A) k x = forcingCoefficient A k x :=
  (exists_frame_primitive A).choose_spec.2 k x

/-- The globally smooth, nowhere-zero scalar correction. -/
def correctionFactor (x : ComplexPlane₂) : ℂ := Complex.exp (-framePrimitive A x)

theorem correctionFactor_contDiff : ContDiff ℝ ∞ (correctionFactor A) :=
  (framePrimitive_contDiff A).neg.cexp

theorem correctionFactor_ne_zero (x : ComplexPlane₂) : correctionFactor A x ≠ 0 :=
  Complex.exp_ne_zero _

theorem correctionFactor_dbar (k : Fin 2) (x : ComplexPlane₂) :
    dbarCoordinate (correctionFactor A) k x =
      -(correctionFactor A x * forcingCoefficient A k x) := by
  have hu := (framePrimitive_contDiff A).differentiable (by simp) x
  have hn : DifferentiableAt ℝ (fun y => -framePrimitive A y) x := hu.neg
  change dbarCoordinate (fun y => Complex.exp (-framePrimitive A y)) k x = _
  rw [dbarCoordinate_cexp hn k, dbarCoordinate_neg hu k, framePrimitive_dbar A k x]
  exact mul_neg _ _

/-- Corrected local coefficients, still expressed in the original charts. -/
def correctedCoefficient (i : ι) (x : ComplexPlane₂) : ℂ :=
  correctionFactor A x * frameCoefficient A i x

theorem correctedCoefficient_ne_zero (i : ι) (x : ComplexPlane₂) :
    correctedCoefficient A i x ≠ 0 :=
  mul_ne_zero (correctionFactor_ne_zero A x) (frameCoefficient_ne_zero A i x)

theorem correctedCoefficient_contDiffOn (i : ι) :
    ContDiffOn ℝ ∞ (correctedCoefficient A i) (A.baseSet i) :=
  (correctionFactor_contDiff A).contDiffOn.mul (frameCoefficient_contDiffOn A i)

/-- Multiplication by one global scalar preserves the original native
transition relation exactly. -/
theorem correctedCoefficient_compatible : A.IsCompatible (correctedCoefficient A) := by
  intro i j x hx
  change (A.transition i j x : ℂ) *
      (correctionFactor A x * frameCoefficient A i x) =
    correctionFactor A x * frameCoefficient A j x
  rw [mul_left_comm, frameCoefficient_compatible A i j x hx]

/-- The actual antiholomorphic derivatives of the corrected coefficients
vanish, using the solved forcing equation and the ordinary product rule. -/
theorem correctedCoefficient_dbar_eq_zero (i : ι) (k : Fin 2) {x : ComplexPlane₂}
    (hx : x ∈ A.baseSet i) : dbarCoordinate (correctedCoefficient A i) k x = 0 := by
  have hc := (correctionFactor_contDiff A).differentiable (by simp) x
  have hs := (frameCoefficient_contDiffAt A i x hx).differentiableAt (by simp)
  change dbarCoordinate (fun y => correctionFactor A y * frameCoefficient A i y) k x = 0
  rw [dbarCoordinate_mul hc hs k, correctionFactor_dbar A k x,
    forcingCoefficient_eq A i k hx]
  dsimp only [localForcing]
  field_simp [frameCoefficient_ne_zero A i x]
  ring

/-- The corrected local coefficient is jointly holomorphic, not merely
formally annihilated by an abstract differential operator. -/
theorem correctedCoefficient_analyticOnNhd (i : ι) :
    AnalyticOnNhd ℂ (correctedCoefficient A i) (A.baseSet i) :=
  analyticOnNhd_of_dbarCoordinate_zero (A.isOpen_baseSet i)
    ((correctedCoefficient_contDiffOn A i).differentiableOn (by simp))
    (fun _ hx => correctedCoefficient_dbar_eq_zero A i 0 hx)
    (fun _ hx => correctedCoefficient_dbar_eq_zero A i 1 hx)

theorem correctedCoefficient_contDiffOn_complex (i : ι) :
    ContDiffOn ℂ ω (correctedCoefficient A i) (A.baseSet i) :=
  (correctedCoefficient_analyticOnNhd A i).contDiffOn_of_completeSpace

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationHolomorphicFrame
