import Wikipedia.HopfProblem.CuspCentralHomologyBaseTorus
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationModelPeriods
import Wikipedia.HopfProblem.CuspControlledRetractionStraightenedCollapse

/-!
# The base coordinate of the prescribed collapse in actual periods

The geometric base projection forgets precisely the compact phase of a
central toric point. Its value on the independent prescribed collapse is
therefore the normalized logarithmic position of the original point.
The actual exponential period formula and actual change of twist then
recover the two logarithmic period coefficients, modulo the integral
lattice. No chosen fibre marking or deformation endpoint enters this proof.
-/

noncomputable section

open Set Topology
open scoped Matrix

namespace Wikipedia.HopfProblem.CuspBoundaryTopVanishing

open ToricCharts ToricSpace CuspUniformization CuspRetraction CuspPositive
open CuspControlledRetraction CuspCollapse CuspHoneycomb CuspCentralHomology
open CuspCentralHomology.SpecializationModel PeriodTorusHigherHomology

local notation "Plane" => CuspHoneycombTiling.Plane

/-- The genuine base projection of a central point is read from its modulus. -/
theorem baseTorusProjection_centralProject
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (x : CentralFibre) :
    baseTorusProjection C r hr (centralProject C r hr x) =
      baseTorusPoint ((honeycombHomeomorph (C 0)).symm (centralModulus x)) := by
  obtain ⟨p, rfl⟩ := honeycombPolarMap_surjective (C 0) x
  change baseTorusProjection C r hr (honeycombCollapseMap C r hr p) =
    baseTorusPoint ((honeycombHomeomorph (C 0)).symm
      (centralModulus (centralPolarMap (phaseCoordinatesHomeomorph (C 0) p))))
  rw [baseTorusProjection_honeycombCollapseMap, centralModulus_centralPolarMap]
  exact congrArg baseTorusPoint ((honeycombHomeomorph (C 0)).symm_apply_apply p.2).symm

/-- Taking the toric modulus preserves the rescaled logarithmic position. -/
theorem position_modulus {x : Space} (hx : time x ≠ 0) :
    position (modulus x) = position x := by
  ext i
  simp only [position, time_modulus, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _), logCoordinates, logNorm,
    torusCoordinates_modulus ((mem_openTorus_iff x).mpr hx), coordinateModulus_apply]

/-- Normalization uses only the modulus, including its positive time. -/
theorem normalizedPosition_modulus (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    {x : Space} (hx : time x ≠ 0) :
    normalizedPosition C₀ (modulus x) = normalizedPosition C₀ x := by
  simp only [normalizedPosition, time_modulus, position_modulus hx,
    inverseDisplacement_positiveTwist_norm]

/-- The prescribed collapse has the original normalized base coordinate. -/
theorem baseTorusProjection_prescribedCollapse
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (η : ℝ) (x : PuncturedClosedTube η) :
    baseTorusProjection C r hr (centralProject C r hr (prescribedCollapse (C 0) η x)) =
      baseTorusPoint (normalizedPosition (C 0) (x.1 : Space)) := by
  rw [baseTorusProjection_centralProject, prescribedCollapse_modulus]
  change baseTorusPoint ((honeycombHomeomorph (C 0)).symm
    (honeycombHomeomorph (C 0)
      (normalizedPosition (C 0)
        (((puncturedPolarHomeomorph η).symm x).2.1.1 : Space)))) = _
  rw [Homeomorph.symm_apply_apply, puncturedPolarHomeomorph_symm_positive_coe]
  change baseTorusPoint (normalizedPosition (C 0) (modulus (x.1 : Space))) = _
  rw [normalizedPosition_modulus (C 0) x.2]

/-- Removing the real part of a frozen correction does not change displacement. -/
theorem inverseDisplacement_positiveTwist_frozen
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (t : ℂ) :
    inverseDisplacement (positiveTwist (C 0)) t = inverseDisplacement (frozen C) t := by
  unfold inverseDisplacement displacementMatrix
  rw [driftMatrix_positiveTwist]
  rfl

/-- Straightening the actual exponential point recovers its original real
logarithmic period coefficients, not coordinates of a chosen marking. -/
theorem normalizedPosition_changeTwist_markedPoint
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (s : ℂ)
    (hlog : Real.log ‖exponential s‖ < 0)
    (hRC : entryNorm (driftMatrix C (exponential s)) ≤ -Real.log ‖exponential s‖ / 4)
    (hR0 : entryNorm (driftMatrix (frozen C) (exponential s)) ≤
      -Real.log ‖exponential s‖ / 4) (a β : Plane) :
    normalizedPosition (C 0)
      (changeTwist C (frozen C) (exponentialPoint (exponential s)
        (realToComplex a + logarithmicPeriod C s *ᵥ realToComplex β))) =
      realCuspVector β := by
  rw [changeTwist_markedExponentialPoint C (frozen C) s hlog hRC,
    normalizedPosition, time_exponentialPoint (exponential_ne_zero s),
    position_markedExponentialPoint (frozen C) s hlog.ne,
    inverseDisplacement_positiveTwist_frozen,
    inverseDisplacement_displacement (frozen C) hlog hR0]

/-- The original exponential period representative in a containing closed tube. -/
def markedPointPunctured (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (η : ℝ) (s : ℂ) (hη : ‖exponential s‖ ≤ η) (a β : Plane) :
    PuncturedClosedTube η :=
  ⟨⟨exponentialPoint (exponential s)
      (realToComplex a + logarithmicPeriod C s *ᵥ realToComplex β), by
      rw [time_exponentialPoint (exponential_ne_zero s)]
      exact hη⟩, by
    change time (exponentialPoint (exponential s) _) ≠ 0
    rw [time_exponentialPoint (exponential_ne_zero s)]
    exact exponential_ne_zero s⟩

@[simp] theorem markedPointPunctured_coe
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (η : ℝ) (s : ℂ) (hη : ‖exponential s‖ ≤ η) (a β : Plane) :
    ((markedPointPunctured C η s hη a β).1 : Space) =
      exponentialPoint (exponential s)
        (realToComplex a + logarithmicPeriod C s *ᵥ realToComplex β) := rfl

/-- Both actual base-circle coordinates of the straightened prescribed collapse. -/
theorem baseTorusProjection_straightened_markedPoint
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (η : ℝ) (s : ℂ) (hη : ‖exponential s‖ ≤ η)
    (hlog : Real.log ‖exponential s‖ < 0)
    (hRC : entryNorm (driftMatrix C (exponential s)) ≤ -Real.log ‖exponential s‖ / 4)
    (hR0 : entryNorm (driftMatrix (frozen C) (exponential s)) ≤
      -Real.log ‖exponential s‖ / 4) (a β : Plane) :
    baseTorusProjection C r hr (centralProject C r hr
      (straightenedPrescribedCollapse C η (markedPointPunctured C η s hη a β))) =
      coordinateProjection 2 β := by
  rw [straightenedPrescribedCollapse, Function.comp_apply,
    baseTorusProjection_prescribedCollapse]
  change baseTorusPoint (normalizedPosition (C 0)
    (changeTwist C (frozen C) (exponentialPoint (exponential s)
      (realToComplex a + logarithmicPeriod C s *ᵥ realToComplex β)))) = _
  rw [normalizedPosition_changeTwist_markedPoint C s hlog hRC hR0,
    baseTorusPoint_realCuspVector]

end Wikipedia.HopfProblem.CuspBoundaryTopVanishing
