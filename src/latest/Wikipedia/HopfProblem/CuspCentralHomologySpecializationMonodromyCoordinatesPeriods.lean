import Wikipedia.HopfProblem.CuspCentralHomologySpecializationMonodromyCoordinates
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationModelPeriods

/-!
# Compatibility of the source monodromy marking with the actual periods

The four-circle coordinate homeomorphism sends actual real period
coefficients to their original source order.  Combined with the proved
exponential formula, this fixes the marking on the literal frozen and
varying positive-real fibres.
-/

noncomputable section

open Set Topology
open scoped Matrix ContDiff

namespace Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel

open ToricCharts ToricSpace CuspRetraction CuspUniformization CuspPositive
open CuspHoneycomb PeriodTorusHigherHomology

local notation "Plane" => CuspHoneycombTiling.Plane

/-- The original source order on actual real period representatives. -/
theorem sourceCoordinateTorusHomeomorph_periods
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (a β : Plane) :
    sourceCoordinateTorusHomeomorph C₀
        (sourceProjection C₀
          (planarPhase a * sourcePhaseCharacter C₀ (realCuspVector β), realCuspVector β)) =
      coordinateProjection 4 ![β 0, β 1, a 0, a 1] := by
  rw [← sourceProductHomeomorph_symm_coordinateProjection,
    sourceCoordinateTorusHomeomorph, Homeomorph.trans_apply, Homeomorph.apply_symm_apply,
    sourceProductCoordinateHomeomorph_apply, compactFibreTorusHomeomorph_planarPhase]
  funext i
  fin_cases i <;> rfl

theorem sourceCoordinateTorusHomeomorph_symm_periods
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (a β : Plane) :
    (sourceCoordinateTorusHomeomorph C₀).symm
        (coordinateProjection 4 ![β 0, β 1, a 0, a 1]) =
      sourceProjection C₀
        (planarPhase a * sourcePhaseCharacter C₀ (realCuspVector β), realCuspVector β) := by
  apply (sourceCoordinateTorusHomeomorph C₀).injective
  rw [Homeomorph.apply_symm_apply, sourceCoordinateTorusHomeomorph_periods]

/-- The source's four-circle marking agrees with the actual full period
vector on the literal frozen quotient fibre. -/
theorem frozenSourceHomeomorph_sourceCoordinatePeriods
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (ε : ℝ) (hε1 : ε < 1) (hρε : ρ < ε) (hR : SmallDrift (positiveTwist C₀) ε)
    (a β : Plane) :
    frozenSourceHomeomorph C₀ ρ hρ ε hε1 hρε hR
        ((sourceCoordinateTorusHomeomorph C₀).symm
          (coordinateProjection 4 ![β 0, β 1, a 0, a 1])) =
      fibreProjection (fun _ => C₀) ε (ρ : ℂ) (positiveLevel_norm_lt ρ hρ.le ε hρε)
        ⟨exponentialPoint (ρ : ℂ) (realToComplex a +
            logarithmicPeriod (fun _ => C₀) (logarithm (ρ : ℂ)) *ᵥ realToComplex β),
          time_exponentialPoint (Complex.ofReal_ne_zero.mpr hρ.ne') _⟩ := by
  rw [sourceCoordinateTorusHomeomorph_symm_periods, frozenSourceHomeomorph_projection]
  apply congrArg (fibreProjection (fun _ => C₀) ε (ρ : ℂ)
    (positiveLevel_norm_lt ρ hρ.le ε hρε))
  exact Subtype.ext (frozenPhaseHomeomorph_periods C₀ ρ hρ ε hε1 hρε hR a β)

/-- The same marking agrees with the actual full period vector after
the already proved change of twist to the varying quotient fibre. -/
theorem varyingSourceHomeomorph_sourceCoordinatePeriods
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hρε : ρ < ε)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : SmallDrift C ε) (hRD : SmallDrift (frozen C) ε) (a β : Plane) :
    varyingSourceHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD
        ((sourceCoordinateTorusHomeomorph (C 0)).symm
          (coordinateProjection 4 ![β 0, β 1, a 0, a 1])) =
      fibreProjection C ε (ρ : ℂ) (positiveLevel_norm_lt ρ hρ.le ε hρε)
        ⟨exponentialPoint (ρ : ℂ) (realToComplex a +
            logarithmicPeriod C (logarithm (ρ : ℂ)) *ᵥ realToComplex β),
          time_exponentialPoint (Complex.ofReal_ne_zero.mpr hρ.ne') _⟩ := by
  rw [sourceCoordinateTorusHomeomorph_symm_periods, varyingSourceHomeomorph_projection]
  apply congrArg (fibreProjection C ε (ρ : ℂ) (positiveLevel_norm_lt ρ hρ.le ε hρε))
  exact Subtype.ext (varyingPhaseHomeomorph_periods C ρ hρ ε hε hε1 hρε hC hRC hRD a β)

end Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel
