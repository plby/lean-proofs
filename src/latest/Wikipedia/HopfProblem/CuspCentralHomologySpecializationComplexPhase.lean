import Wikipedia.HopfProblem.CuspCentralHomologySpecializationModelFrozen
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationMonodromyPhase

/-!
# Actual toric fibres with a nonreal base phase

A real angle is retained as an explicit parameter.  Multiplication by its
base-circle phase, together with the compensating planar fibre phases,
gives a homeomorphism onto the literal complex-time toric fibre.  Its deck
covariance uses the actual compact-torus normalizer.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel

open ToricSpace CuspPositive CuspCollapse CuspHoneycomb CuspHoneycombTiling

local notation "Plane" => CuspHoneycombTiling.Plane

/-- Complex time with a chosen real lift of its argument. -/
def rotatedLevel (ρ r : ℝ) : ℂ := (Circle.exp (2 * Real.pi * r) : ℂ) * (ρ : ℂ)

@[simp] theorem norm_rotatedLevel (ρ r : ℝ) (hρ : 0 ≤ ρ) :
    ‖rotatedLevel ρ r‖ = ρ := by
  rw [rotatedLevel, norm_mul, Circle.norm_coe, one_mul, Complex.norm_of_nonneg hρ]

theorem rotatedLevel_ne_zero (ρ r : ℝ) (hρ : 0 < ρ) : rotatedLevel ρ r ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [norm_rotatedLevel ρ r hρ.le]
  exact hρ.ne'

theorem rotatedLevel_norm_lt (ρ r : ℝ) (hρ : 0 ≤ ρ) (ε : ℝ) (hρε : ρ < ε) :
    ‖rotatedLevel ρ r‖ < ε := by
  rwa [norm_rotatedLevel ρ r hρ]

theorem rotatedLevel_norm_le (ρ r : ℝ) (hρ : 0 ≤ ρ) (η : ℝ) (hρη : ρ ≤ η) :
    ‖rotatedLevel ρ r‖ ≤ η := by
  rwa [norm_rotatedLevel ρ r hρ]

/-- The base-circle factor, without the compensating fibre phases. -/
def baseRotationPhase (r : ℝ) : CompactTorus := ![1, 1, Circle.exp (2 * Real.pi * r)]

/-- Fixed compact rotation restricted to a literal time fibre. -/
def baseRotationMap (ρ r : ℝ) (x : ToricFibre (ρ : ℂ)) : ToricFibre (rotatedLevel ρ r) :=
  ⟨compactTorusAction (baseRotationPhase r) x, by
    rw [compactTorusAction, time_torusAction, compactTorusUnits_apply, x.2]
    rfl⟩

/-- Inverse fixed compact rotation restricted to the rotated time fibre. -/
def baseInverseRotationMap (ρ r : ℝ) (x : ToricFibre (rotatedLevel ρ r)) : ToricFibre (ρ : ℂ) :=
  ⟨compactTorusAction (baseRotationPhase r)⁻¹ x, by
    rw [compactTorusAction, time_torusAction, compactTorusUnits_apply, x.2]
    change ((Circle.exp (2 * Real.pi * r))⁻¹ : Circle) *
      ((Circle.exp (2 * Real.pi * r) : ℂ) * (ρ : ℂ)) = (ρ : ℂ)
    rw [Circle.coe_inv, inv_mul_cancel_left₀ (Circle.coe_ne_zero _)]⟩

theorem baseRotationMap_continuous (ρ r : ℝ) : Continuous (baseRotationMap ρ r) := by
  have h : Continuous (fun x : ToricFibre (ρ : ℂ) =>
      compactTorusAction (baseRotationPhase r) (x : Space)) := by
    change Continuous (fun x : ToricFibre (ρ : ℂ) => baseRotationPhase r • (x : Space))
    exact (continuous_const : Continuous
      (fun _ : ToricFibre (ρ : ℂ) => baseRotationPhase r)).smul
        (continuous_subtype_val : Continuous (fun x : ToricFibre (ρ : ℂ) => (x : Space)))
  exact h.subtype_mk _

theorem baseInverseRotationMap_continuous (ρ r : ℝ) :
    Continuous (baseInverseRotationMap ρ r) := by
  have h : Continuous (fun x : ToricFibre (rotatedLevel ρ r) =>
      compactTorusAction (baseRotationPhase r)⁻¹ (x : Space)) := by
    change Continuous (fun x : ToricFibre (rotatedLevel ρ r) =>
      (baseRotationPhase r)⁻¹ • (x : Space))
    exact (continuous_const : Continuous
      (fun _ : ToricFibre (rotatedLevel ρ r) => (baseRotationPhase r)⁻¹)).smul
        (continuous_subtype_val : Continuous
          (fun x : ToricFibre (rotatedLevel ρ r) => (x : Space)))
  exact h.subtype_mk _

/-- The genuine fixed compact-torus action between two literal time fibres. -/
def baseRotationHomeomorph (ρ r : ℝ) : ToricFibre (ρ : ℂ) ≃ₜ ToricFibre (rotatedLevel ρ r) where
  toFun := baseRotationMap ρ r
  invFun := baseInverseRotationMap ρ r
  left_inv x := by
    apply Subtype.ext
    change compactTorusAction (baseRotationPhase r)⁻¹
      (compactTorusAction (baseRotationPhase r) (x : Space)) = (x : Space)
    rw [compactTorusAction_mul, inv_mul_cancel, compactTorusAction_one]
  right_inv x := by
    apply Subtype.ext
    change compactTorusAction (baseRotationPhase r)
      (compactTorusAction (baseRotationPhase r)⁻¹ (x : Space)) = (x : Space)
    rw [compactTorusAction_mul, mul_inv_cancel, compactTorusAction_one]
  continuous_toFun := baseRotationMap_continuous ρ r
  continuous_invFun := baseInverseRotationMap_continuous ρ r

/-- The continuous planar phase adjustment before the fixed base rotation. -/
def partialPlanarPhase (r : ℝ) (y : Plane) : CompactFibreTorus :=
  fun i => Circle.exp (2 * Real.pi * r * y i)

theorem partialPlanarPhase_continuous (r : ℝ) : Continuous (partialPlanarPhase r) := by
  apply continuous_pi
  intro i
  exact Circle.exp.continuous.comp (continuous_const.mul (continuous_apply i))

/-- The planar phase adjustment has a literal continuous inverse. -/
def partialPhaseHomeomorph (r : ℝ) : PhasePlane ≃ₜ PhasePlane where
  toFun p := (p.1 * partialPlanarPhase r p.2, p.2)
  invFun p := (p.1 * (partialPlanarPhase r p.2)⁻¹, p.2)
  left_inv p := by simp
  right_inv p := by simp
  continuous_toFun :=
    (continuous_fst.mul ((partialPlanarPhase_continuous r).comp continuous_snd)).prodMk
      continuous_snd
  continuous_invFun :=
    (continuous_fst.mul (((partialPlanarPhase_continuous r).comp continuous_snd).inv)).prodMk
      continuous_snd

theorem baseRotationPhase_mul_partialPhase (r : ℝ) (p : PhasePlane) :
    baseRotationPhase r * compactFibrePhase (p.1 * partialPlanarPhase r p.2) =
      compensatingPhase r p := by
  funext i
  fin_cases i <;> simp [baseRotationPhase, compactFibrePhase, partialPlanarPhase,
    compensatingPhase]

variable (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (ε : ℝ) (hε1 : ε < 1) (hρε : ρ < ε) (hR : SmallDrift (positiveTwist C₀) ε)
    (r : ℝ)

/-- The compensated phase plane parametrizes the original complex-time fibre. -/
def complexPhaseHomeomorph : PhasePlane ≃ₜ ToricFibre (rotatedLevel ρ r) :=
  ((partialPhaseHomeomorph r).trans
    (frozenPhaseHomeomorph C₀ ρ hρ ε hε1 hρε hR)).trans (baseRotationHomeomorph ρ r)

@[simp] theorem complexPhaseHomeomorph_coe (p : PhasePlane) :
    (complexPhaseHomeomorph C₀ ρ hρ ε hε1 hρε hR r p : Space) =
      compactTorusAction (compensatingPhase r p)
        ((normalizedPositivePoint C₀ ρ hρ p.2).1 : Space) := by
  change compactTorusAction (baseRotationPhase r)
    (frozenPhaseHomeomorph C₀ ρ hρ ε hε1 hρε hR (partialPhaseHomeomorph r p) : Space) = _
  rw [frozenPhaseHomeomorph_coe, compactFibreAction_eq_compact, compactTorusAction_mul]
  change compactTorusAction
    (baseRotationPhase r * compactFibrePhase (p.1 * partialPlanarPhase r p.2))
    ((normalizedPositivePoint C₀ ρ hρ p.2).1 : Space) = _
  rw [baseRotationPhase_mul_partialPhase]

/-- The original integral labels remain the exact deck labels at every angle. -/
theorem complexPhaseHomeomorph_deck (v : Fin 2 → ℤ) (p : PhasePlane) :
    (complexPhaseHomeomorph C₀ ρ hρ ε hε1 hρε hR r (honeycombDeckMap C₀ v p) : Space) =
      twistedTranslate (fun _ => C₀) v
        (complexPhaseHomeomorph C₀ ρ hρ ε hε1 hρε hR r p : Space) := by
  rw [complexPhaseHomeomorph_coe, complexPhaseHomeomorph_coe, compensatingPhase_deck]
  change compactTorusAction (phaseTransform C₀ v (compensatingPhase r p))
    ((normalizedPositivePoint C₀ ρ hρ (p.2 + latticePoint (cuspVector v))).1 : Space) = _
  rw [normalizedPositivePoint_equivariant C₀ ρ hρ ε hε1 hρε hR,
    positiveFibreTranslate_coe, twistedTranslate_constant_polar]

end Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel
