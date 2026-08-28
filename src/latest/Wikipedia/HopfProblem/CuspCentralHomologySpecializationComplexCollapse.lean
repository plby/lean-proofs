import Wikipedia.HopfProblem.CuspCentralHomologySpecializationComplexPhase
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationModelCollapse
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationMonodromyMap

/-!
# The independent prescribed collapse at a nonreal level

The full compact three-torus phase is retained in the prescribed polar
collapse.  In the actual compensated source coordinates, the prescription
is precisely the rotating central point, before taking any quotient.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel

open ToricSpace CuspRetraction CuspControlledRetraction CuspPositive CuspHoneycomb

variable (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (ε : ℝ) (hε1 : ε < 1) (hρε : ρ < ε) (hR : SmallDrift (positiveTwist C₀) ε)
    (r : ℝ) (η : ℝ) (hρη : ρ ≤ η)

/-- These are the literal polar coordinates in the punctured closed tube. -/
theorem toricFibrePunctured_complexPhase (p : PhasePlane) :
    toricFibrePunctured η (rotatedLevel ρ r) (rotatedLevel_ne_zero ρ r hρ)
        (rotatedLevel_norm_le ρ r hρ.le η hρη)
        (complexPhaseHomeomorph C₀ ρ hρ ε hε1 hρε hR r p) =
      puncturedPolarMap η (compensatingPhase r p,
        positiveFibrePunctured ρ hρ η hρη (normalizedPositivePoint C₀ ρ hρ p.2)) := by
  apply Subtype.ext
  apply Subtype.ext
  exact complexPhaseHomeomorph_coe C₀ ρ hρ ε hε1 hρε hR r p

/-- No deformation endpoint is used: the independently prescribed polar
map has the exact phase-rotated central formula on every representative. -/
theorem prescribedCollapse_complexPhase (p : PhasePlane) :
    prescribedCollapse C₀ η
        (toricFibrePunctured η (rotatedLevel ρ r) (rotatedLevel_ne_zero ρ r hρ)
          (rotatedLevel_norm_le ρ r hρ.le η hρη)
          (complexPhaseHomeomorph C₀ ρ hρ ε hε1 hρε hR r p)) =
      rotatingCentralPoint C₀ r p := by
  apply Subtype.ext
  rw [toricFibrePunctured_complexPhase C₀ ρ hρ ε hε1 hρε hR r η hρη p,
    prescribedCollapse_polar]
  change compactTorusAction (compensatingPhase r p)
      ((honeycombHomeomorph C₀
        (normalizedPosition C₀ ((normalizedPositivePoint C₀ ρ hρ p.2).1 : Space))).1 : Space) =
    compactTorusAction (compensatingPhase r p) ((honeycombHomeomorph C₀ p.2).1 : Space)
  have hy := (normalizedPositiveHomeomorph C₀ ρ hρ ε hε1 hρε hR).symm_apply_apply p.2
  rw [normalizedPositiveHomeomorph_symm_apply, normalizedPositiveHomeomorph_apply] at hy
  rw [hy]

end Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel
