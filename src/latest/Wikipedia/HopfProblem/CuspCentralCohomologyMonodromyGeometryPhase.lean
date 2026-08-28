import Wikipedia.HopfProblem.CuspCentralHomologySpecializationComplexPhase
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationMonodromyMap

/-!
# Joint toric transport around the nonzero base circle

The already constructed complex-fibre homeomorphisms vary continuously
in the real argument parameter.  A positive full turn is exactly the
phase-plane shear, as an equality in the original toric space.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel

open ToricSpace CuspPositive CuspCollapse CuspHoneycomb

/-- Increasing the chosen argument by one turn produces the actual
planar phase shear, with no change of deck labels. -/
theorem compensatingPhase_add_one (r : ℝ) (p : PhasePlane) :
    compensatingPhase (r + 1) p = compensatingPhase r (phasePlaneShear p) := by
  funext i
  fin_cases i
  · change p.1 0 * Circle.exp (2 * Real.pi * (r + 1) * p.2 0) =
      (p.1 0 * Circle.exp (2 * Real.pi * p.2 0)) *
        Circle.exp (2 * Real.pi * r * p.2 0)
    rw [show 2 * Real.pi * (r + 1) * p.2 0 =
      2 * Real.pi * p.2 0 + 2 * Real.pi * r * p.2 0 by ring,
      Circle.exp_add]
    simp only [mul_assoc]
  · change p.1 1 * Circle.exp (2 * Real.pi * (r + 1) * p.2 1) =
      (p.1 1 * Circle.exp (2 * Real.pi * p.2 1)) *
        Circle.exp (2 * Real.pi * r * p.2 1)
    rw [show 2 * Real.pi * (r + 1) * p.2 1 =
      2 * Real.pi * p.2 1 + 2 * Real.pi * r * p.2 1 by ring,
      Circle.exp_add]
    simp only [mul_assoc]
  · change Circle.exp (2 * Real.pi * (r + 1)) = Circle.exp (2 * Real.pi * r)
    rw [mul_add, mul_one, Circle.exp_add, circle_exp_two_pi, mul_one]

@[simp] theorem rotatedLevel_zero (ρ : ℝ) : rotatedLevel ρ 0 = (ρ : ℂ) := by
  simp [rotatedLevel]

@[simp] theorem rotatedLevel_add_one (ρ r : ℝ) :
    rotatedLevel ρ (r + 1) = rotatedLevel ρ r := by
  simp [rotatedLevel, mul_add, Circle.exp_add, circle_exp_two_pi]

theorem rotatedLevel_continuous (ρ : ℝ) : Continuous (rotatedLevel ρ) := by
  unfold rotatedLevel
  fun_prop

variable (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (ε : ℝ) (hε1 : ε < 1) (hρε : ρ < ε) (hR : SmallDrift (positiveTwist C₀) ε)

/-- Joint continuity is in the original toric space, not just in each
separately parametrized time fibre. -/
theorem complexPhaseHomeomorph_joint_continuous :
    Continuous (fun p : ℝ × PhasePlane =>
      (complexPhaseHomeomorph C₀ ρ hρ ε hε1 hρε hR p.1 p.2 : Space)) := by
  have hq : Continuous (fun p : ℝ × PhasePlane =>
      normalizedPositivePoint C₀ ρ hρ p.2.2) :=
    (normalizedPositivePoint_continuous C₀ ρ hρ).comp continuous_snd.snd
  have hq' : Continuous (fun p : ℝ × PhasePlane =>
      ((normalizedPositivePoint C₀ ρ hρ p.2.2).1 : Space)) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp hq)
  simp only [complexPhaseHomeomorph_coe]
  change Continuous (fun p : ℝ × PhasePlane => compensatingPhase p.1 p.2 •
    ((normalizedPositivePoint C₀ ρ hρ p.2.2).1 : Space))
  exact compensatingPhase_continuous.smul hq'

/-- The endpoint formula holds after every real initial angle, in the
literal toric space.  The source shear therefore has a geometric origin. -/
theorem complexPhaseHomeomorph_add_one_coe (r : ℝ) (p : PhasePlane) :
    (complexPhaseHomeomorph C₀ ρ hρ ε hε1 hρε hR (r + 1) p : Space) =
      (complexPhaseHomeomorph C₀ ρ hρ ε hε1 hρε hR r (phasePlaneShear p) : Space) := by
  rw [complexPhaseHomeomorph_coe, complexPhaseHomeomorph_coe,
    compensatingPhase_add_one]
  rfl

end Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel
